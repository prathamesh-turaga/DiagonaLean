/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Definitions

/-! # Core undecidability definitions

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/


namespace DiagonaLean.Synthetic.Notation
open DiagonaLean.Halt DiagonaLean.Halt.Encoding Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- The Turing machine halting problem. -/
def HALT : EncodableTM Bool × List Bool → Prop := fun ⟨M, w⟩ => Halts M.toSingleTapeTM w

/-- `p` is undecidable: `HALT` many-one reduces to `p`, so any decider for `p` would yield one
for `HALT`. `HALT ⪯ₘ p` is itself data (see `ManyOneReduces`), so it's wrapped in `Nonempty`
here to keep `Undecidable` a `Prop`, matching its role as the fact one states/cites, not as a
value one unpacks for its reduction witness. This relies on `⪯ₘ` actually carrying algorithmic
content -- see the convention noted on `ManyOneReduces` -- since otherwise `HALT ⪯ₘ p` would
hold classically for essentially every non-trivial `p`, making this predicate vacuous the way
`SDecidable` already is. -/
def Undecidable (p : X → Prop) : Prop := Nonempty (HALT ⪯ₘ p)

/-- If a predicate `p` is synthetically decidable, then its complement is also synthetically decidable. -/
private lemma dec_compl {X : Type*} {p : X → Prop}
    (h : SDecidable p) : SDecidable (Complement p) := by
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

/-- If the double complement of a predicate `p` is synthetically decidable, then `p` itself is synthetically decidable. -/
private lemma dec_compl' {p : X → Prop}
    (h : SDecidable (Complement (Complement p))) : SDecidable p := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun x => ?_⟩
  have key : ¬¬p x ↔ f x = true := Iff.symm ((fun {a b} => iff_comm.mp) (hf x))
  exact ⟨fun hpx => key.mp (fun hn => hn hpx),
         fun hfx => Classical.byContradiction (key.mpr hfx)⟩

/-- Undecidability propagates upward along many-one reductions. -/
lemma undecidability_from_reducibility {p : X → Prop} {q : Y → Prop}
    (hp : Undecidable p) (hpq : p ⪯ₘ q) : Undecidable q := by
  obtain ⟨r⟩ := hp
  exact ⟨⟨hpq.f ∘ r.f, fun x => (r.hf x).trans (hpq.hf (r.f x))⟩⟩


/-- If `¬p` is undecidable then so is `p`.
lemma undecidability_from_complement {p : X → Prop}
    (h : Undecidable (Complement p)) : Undecidable p :=
  fun hp => h (dec_compl hp)


/-- If `¬p` is undecidable then so is `¬¬p`. -/
lemma undecidability_to_complement {p : X → Prop}
    (h : Undecidable (Complement p)) : Undecidable (Complement (Complement p)) :=
  fun hcc => h (dec_compl (dec_compl' hcc))

 Tactic to prove undecidability by reduction from another undecidable problem.
    Translates `undec from H` to `apply undecidability_from_reducibility H`. -/

macro "undec" "from" H:term : tactic =>
  `(tactic| apply undecidability_from_reducibility $H)

end DiagonaLean.Synthetic.Notation
