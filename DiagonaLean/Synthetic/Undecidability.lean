/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Definitions

@[expose] public section

namespace DiagonaLean.Synthetic.Notation
open DiagonaLean.Halt Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- The Turing machine halting problem. -/
def HALT : SingleTapeTM Bool × List Bool → Prop := fun ⟨M, w⟩ => Halts M w

/-- `p` is undecidable: deciding `p` would make `complement HALT` enumerable,
    which combined with enumerability of HALT would make HALT decidable. -/
def undecidable (p : X → Prop) : Prop :=
  SDecidable p → SEnumerable (complement HALT)

-- ── Auxiliary ────────────────────────────────────────────────────────────

private lemma dec_compl {X : Type*} {p : X → Prop}
    (h : SDecidable p) : SDecidable (complement p) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun x => !f x, fun x => ?_⟩
  constructor
  · intro hn
    dsimp only
    cases hfx : f x
    · rfl
    · exact absurd ((hf x).mpr hfx) hn
  · intro hfx hp
    dsimp only at hfx
    have : f x = true := (hf x).mp hp
    simp [this] at hfx

private lemma dec_compl' {p : X → Prop}
    (h : SDecidable (complement (complement p))) : SDecidable p := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun x => ?_⟩
  have key : ¬¬p x ↔ f x = true := by simpa [complement, reflects] using hf x
  exact ⟨fun hpx => key.mp (fun hn => hn hpx),
         fun hfx => Classical.byContradiction (key.mpr hfx)⟩

-- ── Main lemmas ───────────────────────────────────────────────────────────

/-- Undecidability propagates upward along many-one reductions. -/
lemma undecidability_from_reducibility {p : X → Prop} {q : Y → Prop}
    (hp : undecidable p) (hpq : p ⪯ₘ q) : undecidable q := by
  obtain ⟨f, hf⟩ := hpq
  intro ⟨d, hd⟩
  exact hp ⟨fun x => d (f x), fun x => (hf x).trans (hd (f x))⟩

/-- If `¬p` is undecidable then so is `p`. -/
lemma undecidability_from_complement {p : X → Prop}
    (h : undecidable (complement p)) : undecidable p :=
  fun hp => h (dec_compl hp)

/-- If `¬p` is undecidable then so is `¬¬p`. -/
lemma undecidability_to_complement {p : X → Prop}
    (h : undecidable (complement p)) : undecidable (complement (complement p)) :=
  fun hcc => h (dec_compl (dec_compl' hcc))

-- ── Tactic sugar ──────────────────────────────────────────────────────────

macro "undec" "from" H:term : tactic =>
  `(tactic| apply undecidability_from_reducibility $H)

end DiagonaLean.Synthetic.Notation
