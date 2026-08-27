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
open DiagonaLean.Halt Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- The Turing machine halting problem. -/
def HALT : SingleTapeTM Bool × List Bool → Prop := fun ⟨M, w⟩ => Halts M w

/-- `p` is undecidable: deciding `p` would make `complement HALT` enumerable,
    which combined with enumerability of HALT would make HALT decidable. def Undecidable (p : X → Prop) : Prop :=
  SDecidable p → SEnumerable (Complement HALT)
  -/

def Undecidable (p : X → Prop): Prop := (HALT ⪯ₘ p)

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
  obtain ⟨f, hf⟩ := hpq
  simp[Undecidable] at hp
  simp[Undecidable]
  simp_all [ManyOneReduces]
  obtain ⟨f_1, hf_1⟩ := hp
  use (f ∘ f_1)
  simpa


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
