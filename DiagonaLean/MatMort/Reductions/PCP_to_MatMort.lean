/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji

Citations:
- [Paterson1970] M. S. Paterson, "Unsolvability in 3 × 3 Matrices," *Studies in Applied
  Mathematics*, vol. 49, no. 1, pp. 105–107, Mar. 1970, doi: 10.1002/sapm1970491105.
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Computability.Language
import Mathlib.Tactic

import DiagonaLean.MatMort.Basic
import DiagonaLean.PCP.Basic

namespace DiagonaLean.MatMort.Reduction
open Matrix Computability DiagonaLean.PCP DiagonaLean.MatMort

def S : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1; 0, 0, 0; 0, 0, 0]

def T : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; -1, 1, 0; 0, 0, 0]

variable {p q r s : ℕ → ℤ}

variable (hpq : p j > q j ∧ q j ≥ 0)
variable (hrs : r j > s j ∧ s j ≥ 0)

def W (j : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![p j, 0, 0; 0, r j, 0; q j, s j, 1]

local notation "W_" => W (p := p) (q := q) (r := r) (s := s)

def W' (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![p, 0, 0; 0, r, 0; q, s, 1]

variable (a b c : ℤ)

@[simp]
lemma row_prod_S : !![a, b, c] * S = a • !![1, 0, 1] := by simp [S]

@[simp]
lemma row_prod_T : !![a, b, c] * T = (a - b) • !![1, -1, 0] := by simp [T]; grind

def invW (j : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / p j, 0, 0; 0, 1 / r j, 0; -(q j / p j), -(s j / r j), 1]

lemma non_singular_W (j : ℕ) {hpq : p j > q j ∧ q ≥ 0} {hrs : r j > s j ∧ s j ≥ 0}  :
    det (W_ j) ≠ 0 := by
  have hp : p j ≠ 0 := by
    have h1 : p j > q j := hpq.1
    have h2 : q j ≥ 0 := hpq.2 j
    linarith
  have hr : r j ≠ 0 := by
    have h1 : r j > s j := hrs.1
    have h2 : s j ≥ 0 := hrs.2
    linarith
  have hdet : (W_ j).det = p j * r j := by
    unfold W
    simp [Matrix.det_fin_three]
  simp only [hdet]
  exact mul_ne_zero hp hr

theorem mortal_iff_exists_prod_of_Ws
    (hpq : ∀ j, p j > q j ∧ q j ≥ 0)
    (hrs : ∀ j, r j > s j ∧ s j ≥ 0) :
    HasSolution ({S, T} ∪ (Finset.Icc 1 m).biUnion
      (fun j => {W_ j})) ↔ ∃ (m : ℕ) (is : List ℕ) (h : ℤ), h > 0 ∧
      (∀ i ∈ is, 1 ≤ i ∧ i ≤ m) ∧ !![(1 : ℤ), 0, 1] *
        (is.map (fun j => W_ j)).prod = !![h, h, 1] := by
  sorry

/-- The alphabet `{1, 2, 3}`, typed as `Fin 3`.
    `d : Fin 3` represents digit `d.val + 1`. -/
abbrev S123 := Fin 3
abbrev S23 := Fin 2

def liftS23 (w : Word S23) : Word S123 := w.map Fin.succ

/-- Interpret a word over `{1,2,3}` as a base-10 integer:
    "simply write the symbols". Empty word → 0. -/
def wordToInt (w : Word S123) : ℤ :=
  w.foldl (fun acc d => acc * 10 + (d.val + 1)) 0

/-- `10^n`: "1 followed by n zeroes". -/
def shift (n : ℕ) : ℤ := 10 ^ n

lemma wordToInt_nonneg (w : Word S123) : 0 ≤ wordToInt w := by
  unfold wordToInt
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w d ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    grind

lemma wordToInt_lt_shift (w : Word S123) : wordToInt w < shift w.length := by
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
def string_pair_to_W (u v : Word S123) : Matrix (Fin 3) (Fin 3) ℤ :=
  W' (shift u.length) (wordToInt u) (shift v.length) (wordToInt v)
    ⟨wordToInt_lt_shift u, wordToInt_nonneg u⟩
    ⟨wordToInt_lt_shift v, wordToInt_nonneg v⟩

/- lemma concatenation_mortal (X Y U V : Word S123) : -/
/-     !![X, Y, 1] * (string_pair_to_W U V) = !![X++U,Y++V,1] := by sorry -/
/-- Appending words corresponds to: shift left by |U| and add. -/
lemma wordToInt_append (X U : Word S123) :
    wordToInt (X ++ U) = wordToInt X * shift U.length + wordToInt U := by
  unfold wordToInt shift
  induction U using List.reverseRecOn generalizing X with
  | nil => simp
  | append_singleton U d ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
               List.length_append, List.length_singleton, pow_succ]
    grind

/-- Multiplying the row vector `[x, y, 1]` by `string_pair_to_W U V`
    encodes concatenation: `x` gets `U` appended, `y` gets `V` appended. -/
lemma concatenation_mortal (X Y U V : Word S123) :
    !![wordToInt X, wordToInt Y, 1] * string_pair_to_W U V =
    !![wordToInt (X ++ U), wordToInt (Y ++ V), 1] := by
  sorry

/-- The digit `1` in `S123`. -/
notation "one₁₂₃" => (0 : S123)

/-- PCP has a solution iff Matrix Mortality has a solution with H(K) = {S, T} ∪ ⋃ {W⟨U_i,V_i⟩,
  W⟨U_i,1++V_i⟩} with K over {2, 3}. -/
lemma pcp_iff_matmort (K : Stack S23) :
    PCP.HasSolution K ↔
    HasSolution ({S, T} ∪
      K.toFinset.image
        (fun tile => string_pair_to_W (liftS23 tile.top) (liftS23 tile.bot)) ∪
      K.toFinset.image
        (fun tile => string_pair_to_W (one₁₂₃ :: liftS23 tile.top) (liftS23 tile.bot))) := by
  sorry

end DiagonaLean.MatMort.Reduction
