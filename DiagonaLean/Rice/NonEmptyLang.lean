/-
Copyright (c) 2026 Kshitij Salunke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke
-/

import DiagonaLean.Rice.Basic
import DiagonaLean.Synthetic.ReductionChain
import DiagonaLean.Halt.Encoding
import DiagonaLean.Rice.EmptyLang
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding
open DiagonaLean.Rice
open DiagonaLean.Halt Cslib.Turing
open DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation
open DiagonaLean.Synthetic.ReductionChain
open Classical

namespace DiagonaLean.Rice

/--
The non-empty language property is recursively enumerable (semi-decidable)
using the classical synthetic framework.
-/
theorem isNonEmptyLang_recursively_enumerable : semi_decidable isNonEmptyLang := by
  use fun M _n => if Classical.propDecidable (isNonEmptyLang M) |>.decide then true else false
  intro M
  constructor
  · intro hM
    use 0
    simp [hM]
  · rintro ⟨n, hn⟩
    dsimp only at hn
    split at hn
    · next h => simpa using h
    · contradiction

/--
Reduction from HALT to isNonEmptyLang.
-/
noncomputable def nonEmptyLangReduction : SingleTapeTM Bool × List Bool → SingleTapeTM Bool :=
  fun ⟨M, w⟩ => if Halts M w then acceptsEmptyTM else neverHaltTM

/--
HALT many-one reduces to isNonEmptyLang.
-/
theorem halt_reduces_to_isNonEmptyLang : DiagonaLean.Synthetic.Notation.HALT ⪯ₘ isNonEmptyLang := by
  refine ⟨nonEmptyLangReduction, fun ⟨M, w⟩ => ?_⟩
  simp only [DiagonaLean.Synthetic.Notation.HALT, nonEmptyLangReduction]
  constructor
  · intro h
    simp [h]
    use []
    exact acceptsEmptyTM_accepts_nil
  · intro h
    by_contra h_not_halt
    simp [h_not_halt] at h
    obtain ⟨w', hw'⟩ := h
    exact neverHaltTM_not_halts w' ⟨BiTape.mk₁ [true], hw'⟩

/--
If HALT is undecidable, then isNonEmptyLang is not recursive (not SDecidable).
-/
theorem isNonEmptyLang_not_recursive (h_halt : ¬ SDecidable DiagonaLean.Synthetic.Notation.HALT) :
    ¬ SDecidable isNonEmptyLang := by
  intro h_dec
  apply h_halt
  exact dec_red halt_reduces_to_isNonEmptyLang h_dec

end DiagonaLean.Rice
