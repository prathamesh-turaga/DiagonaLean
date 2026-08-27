/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Foundations.Normalize.Halting

/-! # The normalised machine is normalised

`normTM tm` never writes a blank, and on the encoded input it never moves left at the left
end of its tape.
-/

@[expose] public section
namespace DiagonaLean.Foundations.Normalize

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction

variable (tm : SingleTapeTM Bool)

lemma simStep_symbol (q : tm.State) (b : Bool) (a : Option Sym2) :
    (simStep tm q b a).1.symbol = encSym (tm.tr q (decSym a)).1.symbol := by
  rcases htr : tm.tr q (decSym a) with ⟨⟨wr, mv⟩, q''⟩
  match q'' with
  | none => simp [simStep, htr]
  | some q₂ =>
    match mv with
    | none => simp [simStep, htr]
    | some Turing.Dir.right => cases b <;> simp [simStep, htr]
    | some Turing.Dir.left => cases b <;> simp [simStep, htr]

/-- The normalised machine never writes a blank. -/
theorem normTM_noBlankWrites : NoBlankWrites (normTM tm) := by
  rintro ⟨q, ctrl⟩ a
  show (normTr tm q ctrl a).1.symbol ≠ none
  cases ctrl with
  | start => simp [normTr]
  | simR => rw [normTr, simStep_symbol]; exact encSym_ne_none _
  | simL => rw [normTr, simStep_symbol]; exact encSym_ne_none _
  | mvRR => simp [normTr]
  | mvRL => simp [normTr]
  | chkR => rw [normTr]; split <;> simp
  | chkL1 => simp [normTr]
  | chkL2 => rw [normTr]; split <;> simp

/-- On the encoded input, the normalised machine never moves left at the left end of its
tape. -/
theorem normTM_noLeftBoundary (w : List Bool) : NoLeftBoundary (normTM tm) (encInput w) := by
  rintro cfg hreach ⟨q, ctrl⟩ t rfl hleft
  show (normTr tm q ctrl t.head).1.movement ≠ some Turing.Dir.left
  rcases reach_phase tm w hreach with hn | ⟨q', t₀, i, hp⟩
  · exact absurd hn (by simp)
  · have hcontra : ∀ p : ℤ, 1 ≤ p → InvAt t₀ i t p → False := by
      intro p hp1 hinv
      refine left_toList_ne_nil (d := -p) (by omega) ?_ hleft
      rw [hinv.marker]
      simp
    simp only at hp
    rcases hp with ⟨hs, hi, hinv⟩ | ⟨hs, hinv⟩ | ⟨hs, hi, hinv⟩ | ⟨hs, hi, hinv⟩ |
        ⟨hs, hi, hinv⟩ | ⟨hs, hi, hinv⟩ | ⟨hs, hi, hinv⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      simp [normTr]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      exact absurd (hcontra (fold i) (one_le_fold i) hinv) not_false
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      simp [normTr]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      simp [normTr]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      by_cases hi0 : i = -1
      · subst hi0
        have hz : fold (-1 + 1) - 1 = 0 := by norm_num [fold_zero]
        rw [hz] at hinv
        have hhd : t.head = some Mk := by simpa using hinv.head_eq_Mk
        simp [normTr, hhd]
      · have hi1 : 0 ≤ i := by omega
        have hz : fold (i + 1) - 1 = fold i + 1 := by
          have := fold_succ_of_nonneg hi1; omega
        rw [hz] at hinv
        exact absurd (hcontra (fold i + 1) (by have := one_le_fold i; omega) hinv) not_false
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      have hneg : i - 1 < 0 := by omega
      have h2 : fold (i - 1) = -2 * (i - 1) := fold_of_neg hneg
      exact absurd (hcontra (fold (i - 1) - 1) (by omega) hinv) not_false
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj hs)
      rw [normTr]
      split <;> simp

end DiagonaLean.Foundations.Normalize
