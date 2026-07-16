/-
Copyright (c) 2026 Kshitij Salunke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke
-/

import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.Undecidability

namespace DiagonaLean.Rice

open DiagonaLean.Synthetic.Notation DiagonaLean.Synthetic.Definitions
open DiagonaLean.Halt Cslib.Turing

/-! ## Core Definitions -/

/-- A TM M accepts input w iff it outputs [true] on w. -/
def Accepts (M : SingleTapeTM Bool) (w : List Bool) : Prop :=
  SingleTapeTM.Outputs M w [true]

/-- The language of a TM: the set of inputs it accepts. -/
def Lang (M : SingleTapeTM Bool) : List Bool → Prop :=
  Accepts M

/-- A TM has the empty language property iff it accepts no input. -/
def isEmptyLang (M : SingleTapeTM Bool) : Prop :=
  ∀ w, ¬ Accepts M w

/-- A TM has the non-empty language property iff it accepts at least one input. -/
def isNonEmptyLang (M : SingleTapeTM Bool) :=
  ∃ w, Accepts M w

theorem isEmptyLang_complement :
    complement (isEmptyLang) = isNonEmptyLang := by
  funext w
  simp [isEmptyLang, isNonEmptyLang, complement]

/-! ## Witness TMs -/

/-- A TM that loops forever on every input. Its only state is `()`,
    and the transition writes nothing, doesn't move, and stays in `()`.
    Since the state never becomes `none`, this TM never halts. -/
def neverHaltTM : SingleTapeTM Bool where
  State := PUnit
  q₀ := ()
  tr _ _ := (⟨none, none⟩, some ())

/-- A TM that accepts the empty input `[]`:
    - In state `true` (initial), on a blank head (`none`), writes `true` and halts.
    - In state `true`, on a non-blank head (`some _`), enters state `false`.
    - In state `false`, loops forever regardless of the head symbol. -/
def acceptsEmptyTM : SingleTapeTM Bool where
  State := Bool
  q₀ := true
  tr
    | true, none     => (⟨some true, none⟩, none)
    | true, some _   => (⟨none, none⟩, some false)
    | false, _       => (⟨none, none⟩, some false)

end DiagonaLean.Rice
