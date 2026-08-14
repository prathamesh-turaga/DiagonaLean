/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.UTMHalt.Basic

/-! # Halt ⪯ₘ UTMHalt

Given (an encoding of) a machine `tm` together with an input `w`, it halts exactly when `tm` halts
on `w`, and produces exactly the output that `tm` produces on `w`.
-/

@[expose] public section

namespace DiagonaLean.UTMHalt.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Helpers
  DiagonaLean.Foundations.UniversalTuringMachine DiagonaLean.Halt.Undecidable

/-- A weakly universal machine halts on at least one input. -/
theorem IsWeaklyUniversalWrt.exists_halts (hU : IsWeaklyUniversalWrt pair U) :
    ∃ x : List Bool, Halts U x :=
  ⟨pair (encodeBoolTM haltTM) [], (hU haltTM []).mpr (halts_haltTM [])⟩

/-- A weakly universal machine diverges on at least one input: it is not a total machine. -/
theorem IsWeaklyUniversalWrt.exists_not_halts (hU : IsWeaklyUniversalWrt pair U) :
    ∃ x : List Bool, ¬ Halts U x :=
  ⟨pair (encodeBoolTM loopTM) [], fun h => not_halts_loopTM [] ((hU loopTM []).mp h)⟩

/-- A machine deciding the halting problem of a weakly universal machine decides the
general halting problem. -/
theorem isHaltDecider_of_isHaltDeciderFor {D : SingleTapeTM Bool}
    (hU : IsWeaklyUniversal U) (hD : IsHaltDeciderFor U D) : IsHaltDecider D := by
  intro tm _ w
  refine ⟨fun h => (hD _).1 ((hU tm w).mpr h), fun h => (hD _).2 ?_⟩
  exact fun h' => h ((hU tm w).mp h')

/-- The halting problem of a single weakly universal machine is undecidable. -/
theorem not_exists_haltDeciderFor_of_isWeaklyUniversal (hU : IsWeaklyUniversal U) :
    ¬ ∃ D : SingleTapeTM Bool, IsHaltDeciderFor U D := by
  rintro ⟨D, hD⟩
  exact halt_undecidable
    ⟨D, isHaltDecider_of_isHaltDeciderFor hU hD⟩

/-- The halting problem many-one reduces to the halting problem of any weakly universal
machine: an instance `(M, w)` is mapped to the encoded instance `⟪ M ⟫ w`. -/
theorem halt_iff_utmhalt (hU : IsWeaklyUniversal U) (M : SingleTapeTM Bool)
    (w : List Bool) [DecidableEq M.State] :
    Halts M w ↔ UTMHalts U hU M w :=
  (hU M w).symm

end DiagonaLean.UTMHalt.Reduction
