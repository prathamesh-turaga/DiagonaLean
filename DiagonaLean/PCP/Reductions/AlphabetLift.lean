/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import Mathlib
import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.Synthetic.Undecidability

/-! # Transporting PCP across alphabets

Every PCP instance `P : Stack γ₁` can be recoded, one symbol at a time, into a PCP instance
over any alphabet `γ₂` with at least two distinct elements: each symbol of `γ₁` is encoded
by a fixed-width binary word over `γ₂`, and the codomain instance is solvable iff the
source instance is. `PCP_alphabet_lift` packages this as a many-one reduction; the
concrete data (`liftInstance`, `symbolBits`) is exported so downstream reductions can
build the encoded instance and transport equivalences back and forth. -/

namespace DiagonaLean.PCP.AlphabetLift

variable {γ₁ γ₂ : Type} [DecidableEq γ₁]

def symbolsUsed (P : DiagonaLean.PCP.Stack γ₁) : List γ₁ :=
  (P.flatMap (fun t => t.top ++ t.bot)).dedup

/-- Fixed-width little-endian bits of `n`, padded/truncated to `len`. -/
def natToBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | len + 1, n => decide (n % 2 = 1) :: natToBits len (n / 2)

/-- Width sufficient to distinguish `n` elements. -/
def widthFor (n : ℕ) : ℕ := Nat.log2 n + 1

/-- A symbol's fixed-width bit-encoding, via its position in `symbolsUsed P`. -/
def symbolBits (P : DiagonaLean.PCP.Stack γ₁) (a : γ₁) : List Bool :=
  natToBits (widthFor (symbolsUsed P).length) ((symbolsUsed P).idxOf a)

variable (b0 b1 : γ₂)

/-- Lifts one bit to a distinguished target symbol. -/
def bitTo (b : Bool) : γ₂ := if b then b1 else b0

/-- A symbol's fixed-width word over `γ₂`. -/
def symbolWord (P :  DiagonaLean.PCP.Stack γ₁) (a : γ₁) : List γ₂ :=
  (symbolBits P a).map (bitTo b0 b1)

/-- Lifts a word over `γ₁` to a word over `γ₂`, symbol by symbol. -/
def liftWord (P :  DiagonaLean.PCP.Stack γ₁) (w : List γ₁) : List γ₂ :=
  w.flatMap (symbolWord b0 b1 P)

/-- Lifts a single tile. -/
def liftTile (P : DiagonaLean.PCP.Stack γ₁) (t : DiagonaLean.PCP.Tile γ₁) : DiagonaLean.PCP.Tile γ₂ :=
  ⟨liftWord b0 b1 P t.top, liftWord b0 b1 P t.bot⟩

/-- Lifts a whole PCP instance. -/
def liftInstance (P : DiagonaLean.PCP.Stack γ₁) : DiagonaLean.PCP.Stack γ₂ :=
  P.map (liftTile b0 b1 P)

/-- `liftWord` is a homomorphism w.r.t. concatenation — immediate from
    `List.flatMap_append`. -/
theorem liftWord_append (P : DiagonaLean.PCP.Stack γ₁) (u v : List γ₁) :
    liftWord b0 b1 P (u ++ v) = liftWord b0 b1 P u ++ liftWord b0 b1 P v := by
  simp [liftWord, List.flatMap_append]

/-- `τ1`/`τ2` (via `τProj`) commute with lifting: unfolding `foldr` and applying
`liftWord_append` step by step. -/
theorem tau_lift (proj : DiagonaLean.PCP.Tile γ₁ → List γ₁) (proj' : DiagonaLean.PCP.Tile γ₂ → List γ₂)
    (hproj : ∀ P t, proj' (liftTile b0 b1 P t) = liftWord b0 b1 P (proj t))
    (P : DiagonaLean.PCP.Stack γ₁) (A : DiagonaLean.PCP.Stack γ₁) :
    (A.map (liftTile b0 b1 P)).foldr (fun t acc => proj' t ++ acc) [] =
      liftWord b0 b1 P (A.foldr (fun t acc => proj t ++ acc) []) := by
  induction A with
  | nil => simp [liftWord]
  | cons t A ih => simp [liftWord_append, hproj, ih]

/-- Every `natToBits len n` has length `len`. -/
theorem natToBits_length (len n : ℕ) : (natToBits len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [natToBits, ih]

theorem symbolWord_length (P : DiagonaLean.PCP.Stack γ₁) (a : γ₁) :
    (symbolWord b0 b1 P a).length = widthFor (symbolsUsed P).length := by
  simp [symbolWord, symbolBits, natToBits_length]


/-- `bitTo b0 b1` is injective whenever `b0 ≠ b1` — the only way two bits can
    map to the same target symbol is if they're the same bit. -/
theorem bitTo_injective (hne : b0 ≠ b1) : Function.Injective (bitTo b0 b1) := by
  intro x y h
  cases x <;> cases y <;> simp only [bitTo] at h
  · rfl
  · exact absurd h hne
  · exact absurd h.symm hne
  · rfl

/-- `natToBits len` is injective on naturals below `2^len` — standard
    fixed-width binary decoding, by induction on the width, peeling one bit
    at a time. -/
theorem natToBits_injective (len : ℕ) {m n : ℕ} (hm : m < 2 ^ len) (hn : n < 2 ^ len) :
    natToBits len m = natToBits len n → m = n := by
  induction len generalizing m n with
  | zero =>
    intro _
    simp only [pow_zero, Nat.lt_one_iff] at hm hn
    omega
  | succ len ih =>
    intro h
    simp only [natToBits] at h
    injection h with hbit hrest
    have hm2 : m / 2 < 2 ^ len := by
      have h2 : m < 2 * 2 ^ len := by
        have := hm; simp only [pow_succ] at this; omega
      omega
    have hn2 : n / 2 < 2 ^ len := by
      have h2 : n < 2 * 2 ^ len := by
        have := hn; simp only [pow_succ] at this; omega
      omega
    have hdiv : m / 2 = n / 2 := ih hm2 hn2 hrest
    have hmod : m % 2 = n % 2 := by
      have hiff : m % 2 = 1 ↔ n % 2 = 1 := by simpa using hbit
      omega
    omega

/-- `widthFor n` is a covering width: any `n` fits in `widthFor n` bits. -/
theorem widthFor_covers (n : ℕ) : n < 2 ^ widthFor n := by
  unfold widthFor
  exact Nat.lt_log2_self

theorem idxOf_lt_length_of_mem {a : γ₁} {l : List γ₁} (h : a ∈ l) :
    l.idxOf a < l.length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · simp [hb]
    · have h' : a ∈ l := (List.mem_cons.mp h).resolve_left (Ne.symm hb)
      simp only [List.idxOf_cons, List.length_cons]
      refine lt_add_of_le_of_pos ?_ ?_
      simp[hb]
      simp_all
      simp


theorem pow_two_lt (n m : ℕ) (h1: 2^n < 2^m) (h2: 2^m < 2^(n+1)) : False := by
  by_cases h: m < n
  have two_pow: 2^m < 2^n := by
    refine (Nat.pow_lt_pow_iff_right (by simp)).mpr h
  · grind
  · simp at h
    by_cases h_m: m = n
    · grind
    · have two_ineq: n  + 1 < m := by
       grind
      have two_pow_le: 2^(n + 1) < 2^m := by
        refine (Nat.pow_lt_pow_iff_right (by simp)).mpr two_ineq
      grind

theorem log2_le_log2_of_lt_pos (m n : ℕ) (h : m < n) (h_neq_zero : m ≠ 0) : m.log2 ≤ n.log2 := by
  by_contra hcon
  have hn_ne : n ≠ 0 := by omega
  -- lower bound: 2 ^ m.log2 ≤ m — the contrapositive of `Nat.log2_lt` at k := m.log2
  have ha : (2 ^ (m.log2)) ≤ m ∧ m < (2 ^ (m.log2 + 1)) := by
    simp [(Nat.log2_eq_iff h_neq_zero).mp rfl]
  have hb : (2 ^ (n.log2)) ≤ n ∧ n < (2 ^ (n.log2 + 1)) := by
    simp [(Nat.log2_eq_iff hn_ne).mp rfl]
  have hc: (2 ^ (m.log2)) < (2 ^ (n.log2 + 1)) := by
   calc
     (2 ^ (m.log2)) ≤ m := by simp[ha]
     _ < n := h
     _ < (2 ^ (n.log2 + 1)) := by simp[hb]
  simp at hcon
  apply pow_two_lt n.log2 m.log2
  apply (Nat.pow_lt_pow_iff_right (by simp)).mpr hcon
  exact hc





theorem symbolWord_injective (P : DiagonaLean.PCP.Stack γ₁) (hne : b0 ≠ b1)
    {a a' : γ₁} (ha : a ∈ symbolsUsed P) (ha' : a' ∈ symbolsUsed P) :
    symbolWord b0 b1 P a = symbolWord b0 b1 P a' → a = a' := by
  intro h
  have hbits : symbolBits P a = symbolBits P a' :=
    List.map_injective_iff.mpr (bitTo_injective b0 b1 hne) h
  have hNodup : (symbolsUsed P).Nodup := List.nodup_dedup _
  have hidxlt : (symbolsUsed P).idxOf a < 2 ^ widthFor (symbolsUsed P).length := by
    by_cases h : List.idxOf a (symbolsUsed P) = 0
    · rw[h]
      grind
    · refine (Nat.log2_lt ?_).mp ?_
      simp[h]
      calc
        (List.idxOf a (symbolsUsed P)).log2 ≤ (symbolsUsed P).length.log2 := by
          apply log2_le_log2_of_lt_pos
          exact (idxOf_lt_length_of_mem ha)
          exact h
        _ < widthFor (symbolsUsed P).length :=  by
          exact Nat.lt_add_one (symbolsUsed P).length.log2
  have hidxlt' : (symbolsUsed P).idxOf a' < 2 ^ widthFor (symbolsUsed P).length := by
    by_cases h : List.idxOf a' (symbolsUsed P) = 0
    · rw[h]
      grind
    · refine (Nat.log2_lt ?_).mp ?_
      simp[h]
      calc
        (List.idxOf a' (symbolsUsed P)).log2 ≤ (symbolsUsed P).length.log2 := by
          apply log2_le_log2_of_lt_pos
          exact (idxOf_lt_length_of_mem ha')
          exact h
        _ < widthFor (symbolsUsed P).length :=  Nat.lt_add_one (symbolsUsed P).length.log2
  have hidx : (symbolsUsed P).idxOf a = (symbolsUsed P).idxOf a' :=
    natToBits_injective _ hidxlt hidxlt' hbits
  have hga : (symbolsUsed P).get ⟨(symbolsUsed P).idxOf a, List.idxOf_lt_length_of_mem ha⟩ = a := by
    exact List.idxOf_get (List.idxOf_lt_length_of_mem ha)
  have hga' : (symbolsUsed P).get ⟨(symbolsUsed P).idxOf a', List.idxOf_lt_length_of_mem ha'⟩ = a' := by
    exact List.idxOf_get (List.idxOf_lt_length_of_mem ha')
  rw [← hga, ← hga']
  simp[hidx]

theorem liftWord_injective (P : DiagonaLean.PCP.Stack γ₁) (hne : b0 ≠ b1)
    {u v : List γ₁} (hu : ∀ a ∈ u, a ∈ symbolsUsed P) (hv : ∀ a ∈ v, a ∈ symbolsUsed P) :
    liftWord b0 b1 P u = liftWord b0 b1 P v → u = v := by
  simp only [liftWord]
  induction u generalizing v with
  | nil =>
    intro h
    cases v with
    | nil => rfl
    | cons a' v' =>
      exfalso
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      have hle : (symbolWord b0 b1 P a').length ≤
          (symbolWord b0 b1 P a' ++ List.flatMap (symbolWord b0 b1 P) v').length := by
        simp
      rw [← h] at hle
      simp only [List.length_nil] at hle
      have hw : (symbolWord b0 b1 P a').length = widthFor (symbolsUsed P).length :=
        symbolWord_length b0 b1 P a'
      have hwpos : 1 ≤ widthFor (symbolsUsed P).length := by simp [widthFor]
      omega
  | cons a u' ih =>
     intro h
     cases v with
      | nil =>
        exfalso
        simp only [List.flatMap_cons, List.flatMap_nil] at h
        have hle : (symbolWord b0 b1 P a).length ≤
          (symbolWord b0 b1 P a ++ List.flatMap (symbolWord b0 b1 P) u').length := by
         simp
        rw [h] at hle
        simp only [List.length_nil] at hle
        have hw : (symbolWord b0 b1 P a).length = widthFor (symbolsUsed P).length :=
          symbolWord_length b0 b1 P a
        have hwpos : 1 ≤ widthFor (symbolsUsed P).length := by simp [widthFor]
        omega
      | cons a' v' =>
        have hlen : (symbolWord b0 b1 P a).length = (symbolWord b0 b1 P a').length := by
           rw[symbolWord_length, symbolWord_length]
        obtain ⟨hsw, hlw⟩ := List.append_inj h hlen
        have haa' : a = a' := by
          apply symbolWord_injective b0 b1 P hne
          simp[hu]
          simp[hv]
          exact hsw
        have huu' : u' = v' := by
          specialize ih (v := v')
          apply ih
          grind
          grind
          grind
        rw [haa', huu']


theorem τ1_lift (P A : DiagonaLean.PCP.Stack γ₁) :
    DiagonaLean.PCP.τ1 (A.map (liftTile b0 b1 P)) = liftWord b0 b1 P (DiagonaLean.PCP.τ1 A) := by
  induction A with
  | nil => simp [liftWord]
  | cons t A ih =>
      simp [liftWord_append, ← ih, liftTile]

theorem τ2_lift (P A : DiagonaLean.PCP.Stack γ₁) :
    DiagonaLean.PCP.τ2 (A.map (liftTile b0 b1 P)) = liftWord b0 b1 P (DiagonaLean.PCP.τ2 A) := by
  induction A with
  | nil => simp [liftWord]
  | cons t A ih =>
      simp[liftWord_append, ← ih, liftTile]
open DiagonaLean.PCP

theorem mem_τ1_symbolsUsed (P A : DiagonaLean.PCP.Stack γ₁) (hA : ∀ t ∈ A, t ∈ P) :
    ∀ a ∈ DiagonaLean.PCP.τ1 A, a ∈ symbolsUsed P := by
  induction A with
  | nil => simp
  | cons t A ih =>
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · simp_all
      simp[symbolsUsed]
      use t
      simp[hA, h]
    · exact ih (fun t' ht' => hA t' (List.mem_cons_of_mem _ ht')) a h

theorem mem_τ2_symbolsUsed (P A : Stack γ₁) (hA : ∀ t ∈ A, t ∈ P) :
    ∀ a ∈ τ2 A, a ∈ symbolsUsed P := by
  induction A with
  | nil => simp
  | cons t A ih =>
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · simp_all
      simp[symbolsUsed]
      use t
      simp[hA, h]
    · exact ih (fun t' ht' => hA t' (List.mem_cons_of_mem _ ht')) a h

theorem decisionProblem_lifts (P : DiagonaLean.PCP.Stack γ₁) (hne : b0 ≠ b1) :
    DiagonaLean.PCP.DecisionProblem P ↔ DiagonaLean.PCP.DecisionProblem (liftInstance b0 b1 P) := by
      constructor
      · intro h
        unfold DiagonaLean.PCP.DecisionProblem
        unfold DiagonaLean.PCP.DecisionProblem at h
        rcases h with ⟨A,hAne, hAmem, hAeq⟩
        refine ⟨A.map (liftTile b0 b1 P), ?_, ?_, ?_⟩
        · simpa using hAne
        · intro t ht
          obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
          unfold liftInstance
          apply List.mem_map_of_mem
          exact (hAmem t' ht')
        · rw [τ1_lift, τ2_lift, hAeq]
      rintro ⟨B, hBne, hBmem, hBeq⟩
      have hpre : ∀ t ∈ B, ∃ t' ∈ P, t = liftTile b0 b1 P t' := by
        intro t ht
        obtain ⟨t', ht', rfl⟩ := List.mem_map.mp (hBmem t ht)
        exact ⟨t', ht', rfl⟩
      choose f hfP hfeq using hpre
  -- `f : ∀ t, t ∈ B → Tile γ₁`, `hfP : ∀ t ht, f t ht ∈ P`,
  -- `hfeq : ∀ t ht, t = liftTile b0 b1 P (f t ht)`
      have hBA : B = (B.attach.map (fun x => f x.1 x.2)).map (liftTile b0 b1 P) := by
        simp[List.map_map]
        have hval : List.map (fun x : {t // t ∈ B} => (↑x : Tile γ₂)) B.attach = B := by
          simp
        conv_lhs => rw [← hval]
        exact List.map_congr_left (fun x _ => hfeq x.1 x.2)
      set A : Stack γ₁ := B.attach.map (fun x => f x.1 x.2) with hA_def
      have hAmemP : ∀ t ∈ A, t ∈ P := by
          intro t ht
          rw [hA_def] at ht
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
          exact hfP x.1 x.2
      unfold DecisionProblem
      use A
      simp[A]
      constructor
      · exact hBne
      · have hτ1 : τ1 B = liftWord b0 b1 P (τ1 A) := by
            conv_lhs => rw [hBA]
            exact τ1_lift b0 b1 P A
        have hτ2 : τ2 B = liftWord b0 b1 P (τ2 A) := by
            conv_lhs => rw [hBA]
            exact τ2_lift b0 b1 P A
        constructor
        · intro t x x_1 ft
          rw [← ft]
          simp[hfP]
        · show τ1 A = τ2 A
          exact liftWord_injective b0 b1 P hne (mem_τ1_symbolsUsed P A hAmemP)  (mem_τ2_symbolsUsed P A hAmemP) (by rw [← hτ1, ← hτ2, hBeq])

theorem PCP_alphabet_lift (hne : b0 ≠ b1) :
    (@DiagonaLean.PCP.DecisionProblem γ₁) ⪯ₘ (@DiagonaLean.PCP.DecisionProblem γ₂) :=
  ⟨liftInstance b0 b1, fun P => decisionProblem_lifts b0 b1 P hne⟩

end DiagonaLean.PCP.AlphabetLift
