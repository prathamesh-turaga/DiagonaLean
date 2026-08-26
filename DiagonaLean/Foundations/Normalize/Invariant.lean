/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import DiagonaLean.Foundations.Normalize.Machine

/-! # The simulation invariant

`InvAt t i t' p` says that the tape `t'` of the normalised machine, whose head sits at
absolute position `p`, encodes the tape `t` of the simulated machine, whose head sits at
absolute index `i`.
-/

@[expose] public section
namespace DiagonaLean.Foundations.Normalize

open Cslib.Turing SingleTapeTM

/-- `t'` (head at absolute position `p`) encodes `t` (head at absolute index `i`). -/
structure InvAt (t : BiTape Bool) (i : ℤ) (t' : BiTape Sym2) (p : ℤ) : Prop where
  /-- Cell `fold j` of the normalised tape holds cell `j` of the simulated tape. -/
  data : ∀ j : ℤ, decSym (cellAt t' (fold j - p)) = cellAt t (j - i)
  /-- The marker occurs in no data cell. -/
  noMk : ∀ j : ℤ, cellAt t' (fold j - p) ≠ some Mk
  /-- Cell `0` of the normalised tape holds the marker. -/
  marker : cellAt t' (-p) = some Mk
  /-- There is nothing to the left of the marker. -/
  left : ∀ n : ℤ, n < 0 → cellAt t' (n - p) = none

variable {t : BiTape Bool} {i p : ℤ} {t' : BiTape Sym2}

/-- Every position `≥ 1` of the normalised tape is a data cell. -/
lemma fold_surjective {n : ℤ} (hn : 1 ≤ n) : ∃ j : ℤ, fold j = n := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨-k, ?_⟩
    have hkneg : -k < 0 := by omega
    rw [fold_of_neg hkneg]; omega
  · refine ⟨k, ?_⟩
    have : 0 ≤ k := by omega
    rw [fold_of_nonneg this]; omega

/-- The head of the normalised machine never reads the marker except at position `0`. -/
lemma InvAt.head_ne_Mk (h : InvAt t i t' p) (hp : 1 ≤ p) : cellAt t' 0 ≠ some Mk := by
  obtain ⟨j, hj⟩ := fold_surjective hp
  have := h.noMk j
  rwa [hj, sub_self] at this

/-- At position `0` the head of the normalised machine reads the marker. -/
lemma InvAt.head_eq_Mk (h : InvAt t i t' 0) : cellAt t' 0 = some Mk := by
  simpa using h.marker

/-- The symbol read by the normalised machine decodes to the symbol read by the simulated
machine. -/
lemma InvAt.head_decode (h : InvAt t i t' (fold i)) : decSym (cellAt t' 0) = t.head := by
  have := h.data i
  simpa using this

/-- Moving the head of the simulated machine right. -/
lemma InvAt.tm_moveRight (h : InvAt t i t' p) : InvAt t.moveRight (i + 1) t' p where
  data j := by rw [h.data j, cellAt_moveRight]; ring_nf
  noMk j := h.noMk j
  marker := h.marker
  left := h.left

/-- Moving the head of the simulated machine left. -/
lemma InvAt.tm_moveLeft (h : InvAt t i t' p) : InvAt t.moveLeft (i - 1) t' p where
  data j := by rw [h.data j, cellAt_moveLeft]; ring_nf
  noMk j := h.noMk j
  marker := h.marker
  left := h.left

/-- Moving the head of the normalised machine right. -/
lemma InvAt.moveRight (h : InvAt t i t' p) : InvAt t i t'.moveRight (p + 1) where
  data j := by rw [cellAt_moveRight]; rw [show fold j - (p + 1) + 1 = fold j - p by ring]; exact h.data j
  noMk j := by
    rw [cellAt_moveRight, show fold j - (p + 1) + 1 = fold j - p by ring]; exact h.noMk j
  marker := by
    rw [cellAt_moveRight, show -(p + 1) + 1 = -p by ring]; exact h.marker
  left n hn := by
    rw [cellAt_moveRight, show n - (p + 1) + 1 = n - p by ring]; exact h.left n hn

/-- Moving the head of the normalised machine left. -/
lemma InvAt.moveLeft (h : InvAt t i t' p) : InvAt t i t'.moveLeft (p - 1) where
  data j := by
    rw [cellAt_moveLeft, show fold j - (p - 1) - 1 = fold j - p by ring]; exact h.data j
  noMk j := by
    rw [cellAt_moveLeft, show fold j - (p - 1) - 1 = fold j - p by ring]; exact h.noMk j
  marker := by
    rw [cellAt_moveLeft, show -(p - 1) - 1 = -p by ring]; exact h.marker
  left n hn := by
    rw [cellAt_moveLeft, show n - (p - 1) - 1 = n - p by ring]; exact h.left n hn

/-- Writing the encoding of a symbol on the current data cell, in both machines. -/
lemma InvAt.write (h : InvAt t i t' (fold i)) (c : Option Bool) :
    InvAt (t.write c) i (t'.write (encSym c)) (fold i) where
  data j := by
    rw [cellAt_write, cellAt_write]
    by_cases hj : j = i
    · subst hj; simp
    · rw [if_neg (by simpa [sub_eq_zero, fold_eq_iff] using hj), if_neg (by simpa [sub_eq_zero] using hj)]
      exact h.data j
  noMk j := by
    rw [cellAt_write]
    by_cases hj : j = i
    · subst hj; simp
    · rw [if_neg (by simpa [sub_eq_zero, fold_eq_iff] using hj)]
      exact h.noMk j
  marker := by
    rw [cellAt_write, if_neg (by have := fold_pos i; omega)]
    exact h.marker
  left n hn := by
    rw [cellAt_write, if_neg (by have := fold_pos i; omega)]
    exact h.left n hn

/-- Rewriting the current cell with its own contents (turning a blank into `Bl`). -/
lemma InvAt.write_preserve (h : InvAt t i t' p) (hp : 0 ≤ p) :
    InvAt t i (t'.write (preserve t'.head)) p where
  data j := by
    rw [cellAt_write]
    by_cases hj : fold j - p = 0
    · rw [if_pos hj, decSym_preserve, ← cellAt_zero t', ← hj]
      exact h.data j
    · rw [if_neg hj]; exact h.data j
  noMk j := by
    rw [cellAt_write]
    by_cases hj : fold j - p = 0
    · rw [if_pos hj]
      refine preserve_ne_Mk ?_
      rw [← cellAt_zero t', ← hj]
      exact h.noMk j
    · rw [if_neg hj]; exact h.noMk j
  marker := by
    rw [cellAt_write]
    by_cases hp0 : (-p : ℤ) = 0
    · rw [if_pos hp0]
      have : cellAt t' 0 = some Mk := by rw [← hp0]; exact h.marker
      rw [cellAt_zero] at this
      rw [this]
      rfl
    · rw [if_neg hp0]; exact h.marker
  left n hn := by
    rw [cellAt_write, if_neg (by omega)]
    exact h.left n hn

/-- Writing the marker back when standing on it. -/
lemma write_head_self (t' : BiTape Sym2) : t'.write t'.head = t' := rfl

end DiagonaLean.Foundations.Normalize
