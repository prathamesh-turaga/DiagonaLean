/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic)
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Computability.Language
import Mathlib.Tactic
import DiagonaLean.PCP.Reductions.Halt_to_PCP
import DiagonaLean.MatMort.Basic
import DiagonaLean.PCP.Basic
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Synthetic.ReduceToPCP

/-! # PCP ⪯ₘ MatMort

Reduction from PCP to MatMort following [Paterson1970]. Strings in the intersection
of `topCFG P` and `botCFG P` encode valid solution tile sequences for the PCP instance `P`. The main
results are `pcp_iff_nempcfg` and `npcp_iff_empcfg`.

Reduction from the Post Correspondence Problem (PCP) to the Matrix Mortality
Problem (MatMort), following the construction by [Paterson1970].

The Matrix Mortality Problem asks whether a finite set of $3 \times 3$ integer
matrices admits a finite sequence of (possibly repeated) matrix multiplications
that evaluates to the zero matrix.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatMort.Reduction
open Matrix Computability DiagonaLean.PCP DiagonaLean.MatMort

/-- The initialization matrix `S`. When left-multiplied by any row vector `[a, b, c]`, it projects
  the first coordinate and sets up the vector `a • [1, 0, 1]`. -/
def S : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1; 0, 0, 0; 0, 0, 0]

/-- The termination matrix `T`. When left-multiplied by `[a, b, c]`, it yields `[a - b, b - a, 0]`,
  which is the zero vector if and only if `a = b`. -/
def T : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; -1, 1, 0; 0, 0, 0]

/-- The matrix `W' p q r s` encodes a PCP tile. Using base-10 shifts `p` and `r` and integer values
  `q` and `s`, left-multiplying by this matrix appends the strings to the current accumulated
  integers. -/
def W' (p q r s : ℤ) (_hpq : p > q ∧ q ≥ 0) (_hrs : r > s ∧ s ≥ 0) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![p, 0, 0; 0, r, 0; q, s, 1]

variable (a b c : ℤ)

/-- Multiplying a row vector by `S` results in a scaled version of `[1, 0, 1]` based on the first
  coordinate. -/
lemma row_prod_S : a • !![1, 0, 1] = !![a, b, c] * S := by simp [S]

/-- Multiplying a row vector by `T` computes the difference of the first two coordinates. -/
lemma row_prod_T : (a - b) • !![1, -1, 0] = !![a, b, c] * T := by simp [T]; grind

/-- The tile matrix `W'` is non-singular because its determinant `p * r` is non-zero. -/
lemma non_singular_W (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0) :
    det (W' p q r s hpq hrs) ≠ 0 := by
  have hp : p ≠ 0 := by linarith [hpq.1, hpq.2]
  have hr : r ≠ 0 := by linarith [hrs.1, hrs.2]
  have hdet : det (W' p q r s hpq hrs) = p * r := by
    unfold W'
    simp [Matrix.det_fin_three]
  simp only [hdet]
  exact mul_ne_zero hp hr

/-- A finite sequence of W-matrices drawn from a set `Ws`. -/
def WSeq (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ)) :=
  { is : List (Matrix (Fin 3) (Fin 3) ℤ) | is ≠ [] ∧ ∀ M ∈ is, M ∈ Ws }

/-- The product of a sequence of W-matrices, left-multiplied by `[1,0,1]`. -/
def WProd (is : List (Matrix (Fin 3) (Fin 3) ℤ)) : Matrix (Fin 1) (Fin 3) ℤ :=
  !![(1 : ℤ), 0, 1] * is.prod

/-- If a matrix `P` produces equal coordinates when multiplied by `[1, 0, 1]`, then `S * P * T`
  evaluates to the zero matrix. -/
lemma S_prod_T_eq_zero (P : Matrix (Fin 3) (Fin 3) ℤ) (h : ℤ)
    (hP : !![(1 : ℤ), 0, 1] * P = !![h, h, 1]) : S * P * T = 0 := by
  have e0 : P 0 0 + P 2 0 = h := by
    have := congr_fun (congr_fun hP 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have e1 : P 0 1 + P 2 1 = h := by
    have := congr_fun (congr_fun hP 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have e2 : P 0 2 + P 2 2 = 1 := by
    have := congr_fun (congr_fun hP 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have hSP : S * P = !![h, h, 1; 0, 0, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, Matrix.mul_apply, Fin.sum_univ_three] <;> omega
  rw [hSP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_three]

/- TODO: Make all Aristotle-generated lemmas more readable. -/
set_option maxHeartbeats 1600000 in
/-- Given a sequence of matrices `Ms` drawn from `{S, T} ∪ Ws` whose product with a starting vector
  `u` is zero, this lemma extracts the contiguous subsequence `Run` of `W'` matrices that represent
  the actual PCP tile sequence. -/
private lemma mortal_extract
    (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hWs : ∀ M ∈ Ws, ∃ (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0),
             M = W' p q r s hpq hrs)
    (Ms : List (Matrix (Fin 3) (Fin 3) ℤ))
    (hMem : ∀ M ∈ Ms, M ∈ ({S, T} : Finset (Matrix (Fin 3) (Fin 3) ℤ)) ∪ Ws)
    (u : Matrix (Fin 1) (Fin 3) ℤ) (R : List (Matrix (Fin 3) (Fin 3) ℤ))
    (hRmem : ∀ M ∈ R, M ∈ Ws)
    (hGood :
      (∃ γ a b : ℤ, γ ≠ 0 ∧ 0 < a ∧ 0 ≤ b ∧
          !![(1 : ℤ), 0, 1] * R.prod = !![a, b, 1] ∧ u = γ • !![a, b, 1]) ∨
      (∃ δ e f : ℤ, δ ≠ 0 ∧ 0 < e ∧ f < 0 ∧
          !![(1 : ℤ), -1, 0] * R.prod = !![e, f, 0] ∧ u = δ • !![e, f, 0]))
    (hzero : u * Ms.prod = 0) :
    ∃ (Run : List (Matrix (Fin 3) (Fin 3) ℤ)), (∀ M ∈ Run, M ∈ Ws) ∧ Run ≠ [] ∧
      ∃ h : ℤ, 0 < h ∧ !![(1 : ℤ), 0, 1] * Run.prod = !![h, h, 1] := by
  induction' Ms with M Ms ih generalizing u R;
  · rcases hGood with ( ⟨ γ, a, b, hγ, ha, hb, h₁, rfl ⟩ | ⟨ δ, e, f, hδ, he, hf, h₁, rfl ⟩ ) <;>
      simp_all +decide [ ← Matrix.ext_iff ]; all_goals simp_all +decide [ Fin.forall_fin_succ ];
  · by_cases hM : M = S ∨ M = T;
    · rcases hM with ( rfl | rfl );
      · simp +zetaDelta at *;
        convert ih hMem ( u * S ) [ ] _ _ _ using 1;
        · norm_num;
        · rcases hGood with (⟨γ, hγ, x, hx, y, hy, hxy, rfl⟩ | ⟨δ, hδ, x, hx, y, hy, hxy, rfl⟩)
          <;> simp +decide [ * ] at *;
          · exact Or.inl ⟨γ * x, mul_ne_zero hγ hx.ne',
              by ext i; fin_cases i <;> simp +decide [ Matrix.vecMul, S ]⟩;
          · simp +decide [ S ];
            exact Or.inl ⟨ hδ, hx.ne' ⟩;
        · rw [ ← hzero, Matrix.mul_assoc ];
      · rcases hGood with (⟨γ, a, b, hγ, ha, hb, hR, rfl ⟩ | ⟨δ, e, f, hδ, he, hf, hR, rfl⟩);
        · by_cases hab : a = b;
          · use R;
            refine' ⟨ hRmem, _, a, ha, _ ⟩;
            · rintro rfl; norm_num at *;
              linarith;
            · grobner;
          · convert ih (fun M hM => hMem M ( List.mem_cons_of_mem _ hM ))
              ( ( γ * ( a - b ) ) • !![1, -1, 0] ) [ ] ( by norm_num ) _ _ using 1;
            · exact Or.inr ⟨γ * ( a - b ), 1, -1, mul_ne_zero hγ ( sub_ne_zero_of_ne hab ),
                by norm_num, by norm_num, by norm_num, by norm_num⟩;
            · convert hzero using 1;
              simp +decide;
              ext i; fin_cases i <;> norm_num [ Matrix.vecMul, Matrix.mul_apply ] <;> ring_nf;
              · unfold T; norm_num [ Fin.sum_univ_succ, vecHead, vecTail ] ; ring_nf;
                erw [ Matrix.cons_val_succ' ] ; norm_num;
              · simp +decide [ vecHead, vecTail, T ] ; ring_nf;
                simp +decide [ Fin.sum_univ_three ] ; ring_nf;
              · simp +decide [ vecHead, vecTail, T ] ; ring_nf;
                simp +decide [ Fin.sum_univ_three ] ; ring_nf;
        · specialize ih ( fun M hM => hMem M ( List.mem_cons_of_mem _ hM ) )
            ( δ • !![1, -1, 0] ) [ ] ; simp_all +decide;
          simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ ];
          simp_all +decide [ Matrix.vecMul, dotProduct ];
          simp_all +decide [ Fin.sum_univ_three, Matrix.mul_apply ];
          simp_all +decide [ T ];
          exact ih (by cases lt_or_gt_of_ne hδ <;> nlinarith)
            (by cases lt_or_gt_of_ne hδ <;> nlinarith) (by cases lt_or_gt_of_ne hδ <;> nlinarith);
    · simp +zetaDelta at *;
      obtain ⟨ p, q, r, s, hpq, hrs, rfl ⟩ := hWs M ( by tauto );
      rcases hGood with ( ⟨ γ, hγ, x, hx, y, hy, hxy, rfl ⟩ | ⟨ δ, hδ, x, hx, y, hy, hxy, rfl ⟩ );
      · convert ih hMem.2 ( γ • !![p * x + q, r * y + s, 1] ) ( R ++ [ W' p q r s hpq hrs ] ) ( by
          grind ) ( by
          refine Or.inl ⟨ γ, hγ, p * x + q, by nlinarith, r * y + s, by nlinarith, ?_, ?_ ⟩
            <;> simp +decide [ * ];
          convert congr_arg ( fun v : Fin 3 → ℤ => v ᵥ* W' p q r s hpq hrs ) hxy using 1;
          · simp +decide;
          · ext i; fin_cases i <;> simp +decide [ *, Matrix.vecMul ] ;
            · unfold W'; simp +decide [ vecHead, vecTail ] ; ring;
            · unfold W'; simp +decide [ vecHead, vecTail ] ; ring;
            · simp +decide [ vecHead, vecTail, W' ] ) (by
          convert hzero using 1;
          ext i j ; fin_cases i ; fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ]
            <;> ring_nf!;
          · unfold W'; norm_num ; ring_nf;
            simp +decide;
          · unfold W'; norm_num ; ring_nf;
            simp +decide;
          · unfold W'; norm_num ; ring_nf;
            simp +decide ) using 1;
      · convert ih hMem.2 ( δ • !![x * p, y * r, 0] ) ( R ++ [ W' p q r s hpq hrs ] ) _ _ _ using 1;
        · grind;
        · refine Or.inr ⟨ δ, hδ, x * p, by nlinarith, y * r, by nlinarith, ?_, ?_ ⟩;
          · convert congr_arg ( fun v => v * W' p q r s hpq hrs ) hxy using 1;
            any_goals exact fun _ => ⟨ fun v m => v ᵥ* m ⟩;
            · simp +decide;
            · simp +decide [ W' ];
          · ext i j ; fin_cases i ; fin_cases j <;> norm_num;
        · convert hzero using 1;
          ext i j ; fin_cases i ; fin_cases j ;
          simp +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring_nf;
          · unfold W'; simp +decide; ring;
          · simp +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring_nf;
            unfold W'; simp +decide; ring;
          · simp +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring_nf;
            unfold W'; simp +decide; ring;

/-- A sequence of matrices from `{S, T} ∪ Ws` is mortal if and only if there is a valid sequence
  of `W'` matrices (a tile sequence) that produces equal accumulated integer values. -/
theorem mortal_iff_exists_prod_of_Ws
    (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hWs : ∀ M ∈ Ws, ∃ (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0),
             M = W' p q r s hpq hrs) :
    HasSolution ({S, T} ∪ Ws) ↔ ∃ (seq : WSeq Ws) (h : ℤ), h > 0 ∧ WProd seq.val = !![h, h, 1] := by
  constructor
  · rintro ⟨Ms, hMem, hMs0⟩
    obtain ⟨Run, hRunMem, hRunNe, h, hpos, hRunProd⟩ :=
      mortal_extract Ws hWs Ms hMem !![(1 : ℤ), 0, 1] [] (by simp)
        (Or.inl ⟨1, 1, 0, one_ne_zero, one_pos, le_refl 0, by simp, by simp⟩)
        (by simpa using congrArg (fun X => !![(1 : ℤ), 0, 1] * X) hMs0)
    exact ⟨⟨Run, hRunNe, hRunMem⟩, h, hpos, hRunProd⟩
  · rintro ⟨⟨is, his_ne, his_mem⟩, h, hh, hprod⟩
    refine ⟨S :: (is ++ [T]), ?_, ?_⟩
    · intro M hM
      rcases List.mem_cons.mp hM with rfl | hM'
      · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · rcases List.mem_append.mp hM' with hM'' | hM''
        · exact Finset.mem_union_right _ (his_mem M hM'')
        · rw [List.mem_singleton.mp hM'']
          exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · have hp : (S :: (is ++ [T])).prod = S * is.prod * T := by
        simp [List.prod_cons, List.prod_append, mul_assoc]
      rw [hp]
      have hprod' : !![(1 : ℤ), 0, 1] * is.prod = !![h, h, 1] := hprod
      exact S_prod_T_eq_zero is.prod h hprod'

/-- The alphabet `{1, 2, 3}`, typed as `Fin 3`. `d : Fin 3` represents digit `d.val + 1`. -/
abbrev S123 := Fin 3

/-- The alphabet `{2, 3}`, typed as `Fin 2`. But, `d : Fin 2` represents digit `d.val + 1`. -/
abbrev S23 := Fin 2

/-- Lifts a List over `{0, 1}` (Fin 2) to a List over `{1, 2, 3}` (Fin 3) by incrementing each
  digit. -/
def liftS23 (w : List S23) : List S123 := w.map Fin.succ

/-- Interpret a List over `{1,2,3}` as a base-10 integer:
    "simply write the symbols". Empty List → 0. -/
def wordToInt (w : List S123) : ℤ :=
  w.foldl (fun acc d => acc * 10 + (d.val + 1)) 0

/-- `1` followed by `n` `0`s. -/
def shift (n : ℕ) : ℤ := 10 ^ n

/-- The integer representation of a List over `{1, 2, 3}` is always non-negative. -/
lemma wordToInt_nonneg (w : List S123) : 0 ≤ wordToInt w := by
  unfold wordToInt
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w d ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    grind

/-- The integer representation of a List is strictly less than `10^|w|`. -/
lemma wordToInt_lt_shift (w : List S123) : wordToInt w < shift w.length := by
  unfold wordToInt shift
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w d ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
               List.length_append, List.length_singleton, pow_succ]
    grind

/-- The matrix for a pair of words `(u, v)` over `{1,2,3}`:
    - `q = wordToInt u`,  `p = 10^|u|`
    - `s = wordToInt v`,  `r = 10^|v|` -/
def StringPairToW (U V : List S123) : Matrix (Fin 3) (Fin 3) ℤ :=
  W' (shift U.length) (wordToInt U) (shift V.length) (wordToInt V)
    ⟨wordToInt_lt_shift U, wordToInt_nonneg U⟩
    ⟨wordToInt_lt_shift V, wordToInt_nonneg V⟩

/-- Appending words corresponds to: shift left by |U| and add. -/
lemma wordToInt_append (X U : List S123) :
    wordToInt (X ++ U) = wordToInt X * shift U.length + wordToInt U := by
  unfold wordToInt shift
  induction U using List.reverseRecOn generalizing X with
  | nil => simp
  | append_singleton U d ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
               List.length_append, List.length_singleton, pow_succ]
    grind

/-- The mapping from words over `{1, 2, 3}` to their base-10 integer representation is injective. -/
lemma wordToInt_injective : Function.Injective wordToInt := by
  intro w1 w2 h; induction' w1 using List.reverseRecOn with d1 w1 ih generalizing w2 <;>
    induction' w2 using List.reverseRecOn with d2 w2 ih' <;> simp_all +decide [wordToInt_append]
  · have h_wordToInt_nil : wordToInt [] = 0 := by rfl
    have h_wordToInt_singleton : ∀ w : S123, wordToInt [w] = w.val + 1 := by native_decide +revert
    simp_all +decide [shift] ; linarith [Fin.is_lt w2, wordToInt_nonneg d2]
  · unfold wordToInt at h; simp_all +decide [ shift ] ;
    linarith [ show ( w1 : ℕ ) < 3 by exact Fin.is_lt w1,
               show ( List.foldl ( fun acc d => acc * 10 + ( d.val + 1 ) ) 0 d1 : ℤ ) ≥ 0 by exact
                (by induction' d1 using List.reverseRecOn with d1 ih <;>
                  simp_all +decide [List.foldl] ;
                    linarith [ show ( w1 : ℕ ) < 3 by exact Fin.is_lt w1 ] ;) ];
  · have h_eq : wordToInt d1 = wordToInt d2 ∧ w1.val = w2.val := by
      unfold shift wordToInt at * ; simp_all +decide; omega;
    exact ⟨ ih h_eq.1, Fin.ext h_eq.2 ⟩

/-- `liftS23` is injective. -/
lemma liftS23_injective : Function.Injective liftS23 := by
  intro a b hab
  exact List.map_injective_iff.mpr (fun x y h => Fin.succ_injective _ h) hab

/-- Multiplying the row vector `[x, y, 1]` by `StringPairToW U V`
    encodes concatenation: `x` gets `U` appended, `y` gets `V` appended. -/
lemma concatenation_mortal (X Y U V : List S123) :
    !![wordToInt X, wordToInt Y, 1] * StringPairToW U V =
    !![wordToInt (X ++ U), wordToInt (Y ++ V), 1] := by
  unfold StringPairToW;
  unfold W'; simp +decide [ wordToInt_append ] ;

/-- Left-multiplying the row vector `[wordToInt X, wordToInt Y, 1]` by a product of
    `StringPairToW` matrices concatenates all the first components onto `X` (coord 0)
    and all the second components onto `Y` (coord 1). -/
lemma row_mul_prod (X Y : List S123) (pairs : List (List S123 × List S123)) :
    !![wordToInt X, wordToInt Y, 1] *
        (pairs.map (fun p => StringPairToW p.1 p.2)).prod =
    !![wordToInt (X ++ (pairs.map Prod.fst).flatten),
       wordToInt (Y ++ (pairs.map Prod.snd).flatten), 1] := by
  induction pairs generalizing X Y with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.flatten_cons, ← Matrix.mul_assoc,
               concatenation_mortal]
    rw [ih (X ++ p.1) (Y ++ p.2)]
    simp [List.append_assoc]

/-- The digit `1` in `S123`. -/
notation "one₁₂₃" => (0 : S123)

variable {K : Stack S23}

/-- `liftS23` distributes over concatenation. -/
lemma liftS23_append (a b : List S23) :
    liftS23 (a ++ b) = liftS23 a ++ liftS23 b := by
  simp [liftS23, List.map_append]

/-- Flattening the (lifted) top words of a stack equals the lift of its top-concatenation. -/
lemma flatten_liftS23_top (A : Stack S23) :
    (A.map (fun t => liftS23 t.top)).flatten = liftS23 (τ1 A) := by
  induction A with
  | nil => simp [liftS23]
  | cons t A ih =>
    rw [List.map_cons, List.flatten_cons, ih, τ1_cons, liftS23_append]

/-- Flattening the (lifted) bottom words of a stack equals the lift of its bottom-concatenation. -/
lemma flatten_liftS23_bot (A : Stack S23) :
    (A.map (fun t => liftS23 t.bot)).flatten = liftS23 (τ2 A) := by
  induction A with
  | nil => simp [liftS23]
  | cons t A ih =>
    rw [List.map_cons, List.flatten_cons, ih, τ2_cons, liftS23_append]

/-- If the flattened, lifted string representations of the top and bottom words match
    (with a leading `1` marker on one bottom tile), then the original top and bottom strings
    must be equal. (Proved by Aristotle). -/
lemma bots_eq_of_word (L : List (Tile S23 × Bool))
    (heq : one₁₂₃ :: liftS23 (τ1 (L.map Prod.fst))
         = (L.map (fun tb => if tb.2 then one₁₂₃ :: liftS23 tb.1.bot
                              else liftS23 tb.1.bot)).flatten) :
    τ1 (L.map Prod.fst) = τ2 (L.map Prod.fst) := by
  revert L;
  intro L hL
  have h_count : (List.map (fun tb => if tb.2 then 1 else 0) L).sum = 1 := by
    have h_count : (List.map (fun tb => if tb.2 then 1 else 0) L).sum =
        (List.flatten (List.map
          (fun tb => if tb.2 then [0] ++ liftS23 tb.1.bot else liftS23 tb.1.bot) L)).count 0 := by
      have h_count : ∀ (tb : Tile S23 × Bool),
          (if tb.2 then 1 else 0) =
            (if tb.2 then [0] ++ liftS23 tb.1.bot else liftS23 tb.1.bot).count 0 := by
        intro tb; split_ifs <;> simp +decide [ *, List.count ] ;
        · unfold liftS23; aesop;
        · rw [ List.countP_eq_zero.mpr ] ; simp +decide [ liftS23 ];
          rintro a ( ⟨ _, rfl ⟩ | ⟨ _, rfl ⟩ ) <;> decide;
      induction L <;> simp +decide [ * ];
      rename_i k hk ih; clear hL ih
      induction ‹List ( Tile S23 × Bool ) › <;> simp +decide [ * ] ;
    simp_all +decide [ ← hL ];
    exact List.count_eq_zero_of_not_mem fun h => by
      have := List.mem_map.mp h; obtain ⟨ x, hx, hx' ⟩ := this
      simp_all +decide [ Fin.succ_ne_zero ] ;
  obtain ⟨A, t, B, hL⟩ :
      ∃ A : List (Tile S23 × Bool), ∃ t : Tile S23, ∃ B : List (Tile S23 × Bool),
        L = A ++ [(t, true)] ++ B ∧
          (∀ tb ∈ A, tb.2 = false) ∧ (∀ tb ∈ B, tb.2 = false) := by
    have h_split : ∃ i : Fin L.length, (L.get i).2 = true ∧
        ∀ j : Fin L.length, j ≠ i → (L.get j).2 = false := by
      have h_unique_true :
          (Finset.univ.filter (fun i : Fin L.length => (L.get i).2 = true)).card = 1 := by
        convert h_count using 1;
        rw [ Finset.card_filter ];
        refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
      obtain ⟨ i, hi ⟩ := Finset.card_eq_one.mp h_unique_true;
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
      exact ⟨ i, hi.1, fun j hj => by_contra fun hj' => hj <| hi.2 j <| by simpa using hj' ⟩;
    obtain ⟨ i, hi₁, hi₂ ⟩ := h_split;
    refine' ⟨ L.take i, L.get i |>.1, L.drop ( i + 1 ), _, _, _ ⟩;
    · simp +decide [ ← hi₁, List.take_append_drop ];
    · intro tb htb; rw [ List.mem_iff_get ] at htb
      obtain ⟨ j, hj ⟩ := htb; simp_all +decide [ Fin.ext_iff ] ;
      rw [ ← hj,
        hi₂ ⟨ j, by simpa using j.2.trans_le ( by simp ) ⟩
          ( by simpa [ Fin.ext_iff ] using
              ne_of_lt ( show ( j : ℕ ) < i from by simpa using j.2.trans_le ( by simp ) ) ) ];
    · intro tb htb; rw [ List.mem_iff_get ] at htb
      obtain ⟨ j, hj ⟩ := htb; simp_all +decide [ Fin.ext_iff ] ;
      convert hi₂ ⟨ i + 1 + j, _ ⟩ _ using 1;
      repeat grind;
  have h_liftS23_A : liftS23 (τ2 (A.map Prod.fst)) = [] := by
    have h_liftS23_A :
        (liftS23 (τ2 (A.map Prod.fst))) ++ (0 :: liftS23 t.bot) ++
          (liftS23 (τ2 (B.map Prod.fst))) = 0 :: liftS23 (τ1 (L.map Prod.fst)) := by
      simp_all +decide [ List.flatten_append, List.map_append ];
      have h_liftS23_A :
          ∀ (L : List (Tile S23 × Bool)), (∀ tb ∈ L, tb.2 = false) →
            (List.map
              (fun tb => if tb.2 = true then 0 :: liftS23 tb.1.bot else liftS23 tb.1.bot) L
              ).flatten = liftS23 (τ2 (L.map Prod.fst)) := by
        intros L hL; induction L <;> simp_all +decide [ List.map, liftS23_append ]
      rw [ h_liftS23_A A, h_liftS23_A B ]; all_goals grind;
    cases h : liftS23 ( τ2 ( List.map Prod.fst A ) ) <;> simp_all +decide [ List.append_assoc ];
    rename_i k hk;
    replace h := congr_arg List.head? h ; simp_all +decide [ liftS23 ];
    grind;
  simp_all +decide [ liftS23 ];
  rw [ show
        ( List.map
            ( fun tb => if tb.2 = true then 0 :: List.map Fin.succ tb.1.bot
                        else List.map Fin.succ tb.1.bot ) A
          ).flatten = List.map Fin.succ ( τ2 ( List.map Prod.fst A ) ) from ?_,
      show
        ( List.map
            ( fun tb => if tb.2 = true then 0 :: List.map Fin.succ tb.1.bot
                        else List.map Fin.succ tb.1.bot ) B
          ).flatten = List.map Fin.succ ( τ2 ( List.map Prod.fst B ) ) from ?_ ] at *;
  · simp_all +decide;
    exact List.map_injective_iff.mpr ( Fin.succ_injective _ ) <| by
      simpa using
        ‹List.map Fin.succ ( τ1 ( List.map Prod.fst A ) ) ++
            ( List.map Fin.succ t.top ++
                List.map Fin.succ ( τ1 ( List.map Prod.fst B ) ) ) =
          List.map Fin.succ t.bot ++
            List.map Fin.succ ( τ2 ( List.map Prod.fst B ) ) ›;
  · have h_liftS23_B :
        ∀ (B : List (Tile S23 × Bool)), (∀ tb ∈ B, tb.2 = false) →
          (List.map
            (fun tb => if tb.2 = true then 0 :: List.map Fin.succ tb.1.bot
                        else List.map Fin.succ tb.1.bot) B
            ).flatten = List.map Fin.succ (τ2 (List.map Prod.fst B)) := by
      intros B hB; induction B <;> simp_all +decide;
    grind;
  · have h_liftS23_B :
        ∀ (L : List (Tile S23 × Bool)), (∀ tb ∈ L, tb.2 = false) →
          (List.map
            (fun tb => if tb.2 = true then 0 :: List.map Fin.succ tb.1.bot
                        else List.map Fin.succ tb.1.bot) L
            ).flatten = List.map Fin.succ (τ2 (List.map Prod.fst L)) := by
      intros L hL; induction L <;> simp_all +decide;
    grind

/-- Packages all inductive work: given the product equation, produce a tile sequence that is a PCP
  solution. (Proved by Aristotle). -/
private lemma exists_solution_from_prod
    (K : Stack S23) (is : List (Matrix (Fin 3) (Fin 3) ℤ))
    (his_ne : is ≠ [])
    (hdec : ∀ M ∈ is,
      (∃ t ∈ K.toFinset, M = StringPairToW (liftS23 t.top) (liftS23 t.bot)) ∨
      (∃ t ∈ K.toFinset, M = StringPairToW (liftS23 t.top) (one₁₂₃ :: liftS23 t.bot)))
    {h : ℤ} (hprod : WProd is = !![h, h, 1]) :
    ∃ tiles : List (Tile S23), tiles ≠ [] ∧
      (∀ t ∈ tiles, t ∈ K.toFinset) ∧ τ1 tiles = τ2 tiles := by
  have hL : ∃ (L : List (Tile S23 × Bool)),
      is = L.map (fun tb =>
        StringPairToW (liftS23 tb.1.top)
          (if tb.2 then 0 :: liftS23 tb.1.bot else liftS23 tb.1.bot)) ∧
      ∀ tb ∈ L, tb.1 ∈ K.toFinset := by
    have hL : ∀ (is : List (Matrix (Fin 3) (Fin 3) ℤ)),
        (∀ M ∈ is,
          (∃ t ∈ K.toFinset, M = StringPairToW (liftS23 t.top) (liftS23 t.bot)) ∨
          (∃ t ∈ K.toFinset, M = StringPairToW (liftS23 t.top) (0 :: liftS23 t.bot))) →
        ∃ (L : List (Tile S23 × Bool)),
          is = L.map (fun tb =>
            StringPairToW (liftS23 tb.1.top)
              (if tb.2 then 0 :: liftS23 tb.1.bot else liftS23 tb.1.bot)) ∧
          ∀ tb ∈ L, tb.1 ∈ K.toFinset := by
      intro is hdec
      induction' is with M is ih;
      · exact ⟨ [ ], rfl, by intros; contradiction ⟩;
      · simp +zetaDelta at *;
        rcases hdec.1 with ( ⟨ t, ht, rfl ⟩ | ⟨ t, ht, rfl ⟩ ) <;>
          [ exact Exists.elim ( ih hdec.2 ) fun L hL => ⟨ ( t, false ) :: L, by aesop ⟩ ;
            exact Exists.elim ( ih hdec.2 ) fun L hL => ⟨ ( t, true ) :: L, by aesop ⟩ ];
    exact hL is hdec;
  obtain ⟨L, hL_is, hL_mem⟩ := hL
  use L.map Prod.fst;
  convert bots_eq_of_word L _;
  · aesop;
  · have h_word_eq :
        wordToInt (0 :: liftS23 (τ1 (L.map Prod.fst))) =
          wordToInt ((L.map (fun tb =>
            if tb.2 then 0 :: liftS23 tb.1.bot else liftS23 tb.1.bot)).flatten) := by
      have h_word_eq :
          !![wordToInt (0 :: liftS23 (τ1 (L.map Prod.fst))),
             wordToInt ((L.map (fun tb =>
               if tb.2 then 0 :: liftS23 tb.1.bot else liftS23 tb.1.bot)).flatten),
             1] = !![h, h, 1] := by
        convert hprod using 1;
        convert row_mul_prod [0] []
          ( L.map ( fun tb =>
              ( liftS23 tb.1.top,
                if tb.2 then 0 :: liftS23 tb.1.bot else liftS23 tb.1.bot ) ) )
          |> Eq.symm using 1;
        · simp +decide [ List.map_map ];
          constructor <;> congr! 2;
          convert flatten_liftS23_top ( L.map Prod.fst ) |> Eq.symm using 1;
          exact congr_arg _ ( List.ext_get ( by aesop ) ( by aesop ) );
        · unfold WProd; aesop;
      simp_all +decide [ ← List.ofFn_inj ];
    exact wordToInt_injective h_word_eq

/-- If there exists a sequence of `W'` matrices derived from a PCP instance `K` that yields equal coordinates, then `K` has a solution. -/
lemma pcp_if_exists_prod (K : Stack S23)
    (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hWs : ∀ M ∈ Ws,
      (∃ t ∈ K.toFinset, M = StringPairToW (liftS23 t.top) (liftS23 t.bot)) ∨
      (∃ t ∈ K.toFinset, M = StringPairToW (liftS23 t.top) (one₁₂₃ :: liftS23 t.bot))) :
    (∃ (seq : WSeq Ws) (h : ℤ), h > 0 ∧ WProd seq.val = !![h, h, 1]) →
    PCP.DecisionProblem K := by
  rintro ⟨⟨is, his_ne, his_mem⟩, h, hh, hprod⟩
  obtain ⟨tiles, htiles_ne, htiles_K, hτ⟩ :=
    exists_solution_from_prod K is his_ne
      (fun M hM => hWs M (his_mem M hM)) hprod
  exact ⟨tiles, htiles_ne, fun t ht => List.mem_toFinset.mp (htiles_K t ht), hτ⟩

/-- If a PCP instance `K` has a solution, then its corresponding set of constructed matrices has a mortality solution. -/

abbrev mat_image (K : Stack S23) :=({S, T} ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot)))


lemma pcp_if_matmort (h : PCP.DecisionProblem K) :
    HasSolution (mat_image K) := by
  obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := h;
  by_cases hA : A = [] <;> simp_all +decide;
  obtain ⟨ t₀, rest, rfl ⟩ := List.exists_cons_of_ne_nil hA;
  set pairs : List (List S123 × List S123) := (liftS23 t₀.top, 0 :: liftS23 t₀.bot)
    :: (rest.map (fun t => (liftS23 t.top, liftS23 t.bot)))
  set Wmats : List (Matrix (Fin 3) (Fin 3) ℤ) := pairs.map (fun p => StringPairToW p.1 p.2)
  set P : Matrix (Fin 3) (Fin 3) ℤ := Wmats.prod;
  have h_row_mul_prod : !![(1 : ℤ), 0, 1] * P = !![wordToInt (0 :: liftS23 (τ1 (t₀ :: rest))),
      wordToInt (0 :: liftS23 (τ2 (t₀ :: rest))), 1] := by
    convert row_mul_prod [ 0 ] [ ] pairs using 1;
    simp +zetaDelta at *;
    · norm_num [wordToInt]
    · simp only [pairs, List.nil_append, List.singleton_append,
                List.map_cons, List.map_map, Function.comp_def,
                List.flatten_cons,
                flatten_liftS23_top, flatten_liftS23_bot,
                τ1_cons, τ2_cons, liftS23_append]
      exact Equiv.Perm.congr_arg rfl
  refine' ⟨ S :: Wmats ++ [ T ], _, _ ⟩ <;> simp_all +decide [ Finset.mem_union, Finset.mem_image ];
  · grind +qlia;
  · convert S_prod_T_eq_zero P ( wordToInt ( 0 :: liftS23 ( t₀.bot ++ τ2 rest ) ) ) _ using 1;
    · rw [ Matrix.mul_assoc ];
    · convert h_row_mul_prod using 1;
      simp +decide [ ← List.ofFn_inj, Matrix.vecMul ]

/-- If the constructed set of matrices for a PCP instance `K` is mortal, then `K` has a solution. -/

lemma matmort_if_pcp
    (h : HasSolution (mat_image K)) :
    PCP.DecisionProblem K := by
  have h_exists_prod : ∃ (seq : WSeq (Finset.image (fun tile => StringPairToW (liftS23 tile.top)
    (liftS23 tile.bot)) (List.toFinset K) ∪
      Finset.image (fun tile => StringPairToW (liftS23 tile.top) (0 :: liftS23 tile.bot))
        (List.toFinset K))) (h : ℤ), h > 0 ∧ WProd seq.val = !![h, h, 1] := by
    convert mortal_iff_exists_prod_of_Ws _ _ |>.1 _;
    · simp +zetaDelta at *;
      rintro M ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;>
        [ exact ⟨ _, _, _, _, ⟨ wordToInt_lt_shift _, wordToInt_nonneg _ ⟩,
          ⟨ wordToInt_lt_shift _, wordToInt_nonneg _ ⟩, rfl ⟩ ;
            exact ⟨ _, _, _, _, ⟨ wordToInt_lt_shift _, wordToInt_nonneg _ ⟩,
              ⟨ wordToInt_lt_shift _, wordToInt_nonneg _ ⟩, rfl ⟩ ];
    · simpa only [ Finset.union_assoc ] using h;
  convert pcp_if_exists_prod K _ _ h_exists_prod;
  grind

/-- PCP has a solution iff Matrix Mortality has a solution with H(K) = {S, T} ∪ ⋃ {W(U_i,V_i),
  W(U_i,1::V_i)} with K over {2, 3}. -/
lemma pcp_iff_matmort (K : Stack S23) :
    PCP.DecisionProblem K ↔
    HasSolution (mat_image K) :=
  ⟨pcp_if_matmort, matmort_if_pcp⟩

open DiagonaLean.Synthetic.Notation

/-- Matrix mortality of `3 × 3` integer matrices is undecidable: reduced from PCP over the
alphabet `S23 = {2, 3}` by the encoding `mat_image`, with `pcp_iff_matmort` supplying the
correctness equivalence. -/
theorem matmort_undecidable : Undecidable (fun Ws => HasSolution Ws) := by
  reduceToPCP over_type S23 with_red_function mat_image
    using_lemmas pcp_if_matmort matmort_if_pcp

end DiagonaLean.MatMort.Reduction
