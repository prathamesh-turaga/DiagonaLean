/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Akhilesh Balaji
-/

import DiagonaLean.Foundations.UniversalTuringMachine.Basic

/-! # The Universal Turing Machine Halting Problem: Basic Definitions

The central notions used in the proof that the UTM halting problem is undecidable.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

@[expose] public section

namespace DiagonaLean.UTMHalt

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
     DiagonaLean.Halt.Helpers DiagonaLean.Foundations.UniversalTuringMachine

/-- `D` decides the halting problem of the fixed machine `U` if, on every input string
  `x`, it outputs `[true]` when `U` halts on `x` and `[false]` when it does not. -/
def IsHaltDeciderFor (U D : SingleTapeTM Bool) : Prop :=
  ∀ x : List Bool, (Halts U x → D.Outputs x [true]) ∧ (¬ Halts U x → D.Outputs x [false])

/-- The `Halts` predicate for UTMs. -/
def UTMHalts (U : SingleTapeTM Bool) (_hU : IsWeaklyUniversal U) (M : SingleTapeTM Bool)
  (w : List Bool) [DecidableEq M.State] := Halts U (instanceEncoding M w)

/-- The halting problem of the fixed UTM `U`. -/
abbrev UniversalHaltProblem : ({U : SingleTapeTM Bool // IsWeaklyUniversal U} ×
    Σ (M : SingleTapeTM Bool), DecidableEq M.State × List Bool) → Prop := 
  fun ⟨⟨U, hU⟩, ⟨M, _inst, w⟩⟩ ↦ UTMHalts U hU M w

end DiagonaLean.UTMHalt
