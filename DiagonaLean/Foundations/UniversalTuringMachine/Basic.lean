/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Halt.Undecidable

/-! # Universal Turing Machines

A universal Turing machine is a single machine that can simulate every other machine.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

@[expose] public section

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
     DiagonaLean.Halt.Helpers

namespace DiagonaLean.Foundations.UniversalTuringMachine

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A way of packaging the encoding of a machine together with an input string into a
single input string for a universal machine. -/
abbrev InstanceEncoding := List Bool → List Bool → List Bool

/-- The string `⟨tm, w⟩` handed to a universal machine: the Hopcroft-Ullman encoding of
`tm`, paired with the input `w`. -/
noncomputable def instanceEncoding (tm : EncodableTM Bool)
    (w : List Bool) : List Bool := encodePair (encodeBoolTM tm) w

/-- `U` is *weakly universal* with respect to the pairing `pair` if, for every machine
`tm` and input `w`, it halts on `pair ⟪tm⟫ w` exactly when `tm` halts on `w`. -/
def IsWeaklyUniversalWrt (pair : InstanceEncoding) (U : SingleTapeTM Bool) : Prop :=
  ∀ (tm : EncodableTM Bool) (w : List Bool),
    Halts U (pair (encodeBoolTM tm) w) ↔ Halts tm.toSingleTapeTM w

/-- `U` is *universal* with respect to the pairing `pair` if, for every machine `tm` and
input `w`, it halts on `pair ⟪tm⟫ w` exactly when `tm` halts on `w`, and it outputs `v`
on `pair ⟪tm⟫ w` exactly when `tm` outputs `v` on `w`. -/
def IsUniversalWrt (pair : InstanceEncoding) (U : SingleTapeTM Bool) : Prop :=
  ∀ (tm : EncodableTM Bool) (w : List Bool),
    (Halts U (pair (encodeBoolTM tm) w) ↔ Halts tm.toSingleTapeTM w) ∧
      ∀ v : List Bool, (U.Outputs (pair (encodeBoolTM tm) w) v ↔ tm.toSingleTapeTM.Outputs w v)

/-- A weakly universal machine: one reproducing the halting behaviour of every machine,
on inputs encoded by the standard pairing `encodePair`. -/
abbrev IsWeaklyUniversal (U : SingleTapeTM Bool) : Prop :=
  IsWeaklyUniversalWrt encodePair U

/-- A universal machine: one reproducing the halting *and* the input/output behaviour of
every machine, on inputs encoded by the standard pairing `encodePair`. -/
abbrev IsUniversal (U : SingleTapeTM Bool) : Prop :=
  IsUniversalWrt encodePair U

variable {pair : InstanceEncoding} {U : SingleTapeTM Bool}

/-- A universal machine is weakly universal. -/
theorem IsUniversalWrt.weakly (hU : IsUniversalWrt pair U) : IsWeaklyUniversalWrt pair U :=
  fun tm w => (hU tm w).1

/-- Halting of a universal machine on `pair ⟪tm⟫ w` is halting of `tm` on `w`. -/
theorem IsUniversalWrt.halts_iff (hU : IsUniversalWrt pair U)
    (tm : EncodableTM Bool) (w : List Bool) :
    Halts U (pair (encodeBoolTM tm) w) ↔ Halts tm.toSingleTapeTM w := (hU tm w).1

/-- The output of a universal machine on `pair ⟪tm⟫ w` is the output of `tm` on `w`. -/
theorem IsUniversalWrt.outputs_iff (hU : IsUniversalWrt pair U)
    (tm : EncodableTM Bool) (w v : List Bool) :
    U.Outputs (pair (encodeBoolTM tm) w) v ↔ tm.toSingleTapeTM.Outputs w v := (hU tm w).2 v

/-- Halting of a universal machine on the encoded instance `⟨tm, w⟩` is halting of `tm` on `w`. -/
theorem IsUniversal.halts_instanceEncoding_iff (hU : IsUniversal U)
    (tm : EncodableTM Bool) (w : List Bool) :
    Halts U (instanceEncoding tm w) ↔ Halts tm.toSingleTapeTM w := (hU tm w).1

/-- The output of a universal machine on the encoded instance `⟨tm, w⟩` is the output of
`tm` on `w`. -/
theorem IsUniversal.outputs_instanceEncoding_iff (hU : IsUniversal U)
    (tm : EncodableTM Bool) (w v : List Bool) :
    U.Outputs (instanceEncoding tm w) v ↔ tm.toSingleTapeTM.Outputs w v := (hU tm w).2 v

/-- Any two universal machines have the same behaviour on encoded instances. -/
theorem IsUniversalWrt.behaviour_congr {U₁ U₂ : SingleTapeTM Bool}
    (h₁ : IsUniversalWrt pair U₁) (h₂ : IsUniversalWrt pair U₂)
    (tm : EncodableTM Bool) (w : List Bool) :
    (Halts U₁ (pair (encodeBoolTM tm) w) ↔ Halts U₂ (pair (encodeBoolTM tm) w)) ∧
      ∀ v : List Bool,
        (U₁.Outputs (pair (encodeBoolTM tm) w) v ↔ U₂.Outputs (pair (encodeBoolTM tm) w) v) :=
  ⟨((h₁ tm w).1).trans ((h₂ tm w).1).symm,
    fun v => ((h₁ tm w).2 v).trans (((h₂ tm w).2 v).symm)⟩

end DiagonaLean.Foundations.UniversalTuringMachine
