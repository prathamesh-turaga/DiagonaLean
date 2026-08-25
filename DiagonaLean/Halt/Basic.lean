/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Akhilesh Balaji
-/

import DiagonaLean.Halt.Encoding

/-! # The Halting Problem: Basic Definitions

The central notions used in the proof that the halting problem is
undecidable: the `Halts`, `IsSelfHaltDecider`, and `IsHaltDecider` predicates for TMs
are used in the statement of the headline theorems of `DiagonaLean.Halt`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding

namespace DiagonaLean.Halt



/-- `tm` halts on input `w` if there exists a final tape configuration reachable from
the initial configuration via zero or more transition steps. -/
def Halts (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩

/-- `tm` halts on input `w` within `n` transition steps. -/
def HaltsWithinTime (tm : SingleTapeTM Symbol) (w : List Symbol) (n : ℕ) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.RelatesWithinSteps tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩ n

/-- `tm` halts on `w` iff it halts within some finite number of steps. -/
theorem halts_iff_exists_n_haltsWithinTime (tm : SingleTapeTM Symbol)
    (w : List Symbol) :
    Halts tm w ↔ ∃ n, HaltsWithinTime tm w n := by
  constructor
  · rintro ⟨tape, h⟩
    obtain ⟨n, hn⟩ := h.relatesInSteps
    exact ⟨n, tape, .of_relatesInSteps hn⟩
  · rintro ⟨n, tape, m, _, hm⟩
    exact ⟨tape, hm.reflTransGen⟩

/-- `D` is a halt decider if, given the encoding of any TM `tm` paired with any input `w`,
it outputs `[true]` if `tm` halts on `w` and `[false]` otherwise. -/
def IsHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool),
    (Halts tm w →
      SingleTapeTM.Outputs D (encodePair (encodeBoolTM tm) w) [true]) ∧
    (¬ Halts tm w →
      SingleTapeTM.Outputs D (encodePair (encodeBoolTM tm) w) [false])

/-- `D` is a self-halt decider if, given the encoding of any TM `tm`, it outputs `[true]`
if `tm` halts on its own encoding and `[false]` otherwise. -/
def IsSelfHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [DecidableEq tm.State],
    (Halts tm (encodeBoolTM tm) →
      SingleTapeTM.Outputs D (encodeBoolTM tm) [true]) ∧
    (¬ Halts tm (encodeBoolTM tm) →
      SingleTapeTM.Outputs D (encodeBoolTM tm) [false])

/-- The halting problem: does `tm` halt on input `w`? -/
abbrev HaltProblem : SingleTapeTM Bool × List Bool → Prop := fun ⟨a, b⟩ ↦ Halts a b

end DiagonaLean.Halt
