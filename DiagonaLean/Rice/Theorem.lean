/-
Copyright (c) 2026 Kshitij Salunke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke
-/

import DiagonaLean.Rice.Basic
import DiagonaLean.Synthetic.ReductionChain
import DiagonaLean.Halt.Encoding

namespace DiagonaLean.Rice

open DiagonaLean.Halt Cslib.Turing
open DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation
open DiagonaLean.Synthetic.ReductionChain
open Classical

/-- A property of Turing machines. -/
def Property := SingleTapeTM Bool → Prop

/-- A property is semantic if it depends only on the language recognized by the TM. -/
def IsSemantic (P : Property) : Prop :=
  ∀ (M1 M2 : SingleTapeTM Bool), Lang M1 = Lang M2 → (P M1 ↔ P M2)

/-- A property is non-trivial if there is some TM that has the property and some TM that does not. -/
def IsNonTrivial (P : Property) : Prop :=
  (∃ M_T, P M_T) ∧ (∃ M_F, ¬ P M_F)

/--
Rice's Theorem (Synthetic version via classical choice).
Any non-trivial property of Turing machines is undecidable.
-/
theorem rices_theorem {P : Property} (_h_sem : IsSemantic P) (h_nt : IsNonTrivial P)
    (h_halt : ¬ SDecidable DiagonaLean.Synthetic.Notation.HALT) :
    ¬ SDecidable P := by
  unfold IsNonTrivial at h_nt
  obtain ⟨M_T, h_T⟩ := h_nt.1
  obtain ⟨M_F, h_F⟩ := h_nt.2

  intro h_dec_P
  have halt_reduces_to_P : DiagonaLean.Synthetic.Notation.HALT ⪯ₘ P := by
    refine ⟨fun ⟨M, w⟩ => if Halts M w then M_T else M_F, fun ⟨M, w⟩ => ?_⟩
    simp only [DiagonaLean.Synthetic.Notation.HALT]
    constructor
    · intro h
      simp [h, h_T]
    · intro h
      by_contra h_not_halt
      simp [h_not_halt] at h
      exact h_F h

  exact h_halt (dec_red halt_reduces_to_P h_dec_P)

end DiagonaLean.Rice
