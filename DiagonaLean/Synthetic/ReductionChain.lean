/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Synthetic.Definitions

/-! # Pre-Order Properties of Many-One Reductions

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

@[expose] public section

namespace DiagonaLean.Synthetic.ReductionChain
open DiagonaLean.Halt Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y Z : Type*}

/-- Many-one reducibility is reflexive. -/
theorem reduces_reflexive (P : X → Prop) : P ⪯ₘ P :=
  ⟨id, fun _ => Iff.rfl⟩

/-- Many-one reducibility is transitive. -/
theorem reduces_transitive {P : X → Prop} {Q : Y → Prop} {R : Z → Prop}
    (hPQ : P ⪯ₘ Q) (hQR : Q ⪯ₘ R) : P ⪯ₘ R := by
  obtain ⟨f, hf⟩ := hPQ
  obtain ⟨g, hg⟩ := hQR
  exact ⟨g ∘ f, fun x => (hf x).trans (hg (f x))⟩

/-- Equivalent dependent formulation. -/
theorem reduces_dependent {P : X → Prop} {Q : Y → Prop} :
    (P ⪯ₘ Q) ↔ Nonempty (∀ x, { y // P x ↔ Q y }) := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨fun x => ⟨f x, hf x⟩⟩
  · rintro ⟨f⟩
    exact ⟨fun x => (f x).val, fun x => (f x).property⟩

/-- If `P` reduces to `Q`, then the complement of `P` reduces to the complement of `Q`. -/
theorem reduces_complement {P : X → Prop} {Q : Y → Prop}
    (h : P ⪯ₘ Q) : Complement P ⪯ₘ Complement Q := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun x => not_congr (hf x)⟩

/-- If `p` many-one reduces to `q` and `q` is synthetically decidable, then `p` is also synthetically decidable. -/
theorem dec_red {p : X → Prop} {q : Y → Prop}
    (hred : p ⪯ₘ q) (hdec : SDecidable q) : SDecidable p := by
  obtain ⟨f, hf⟩ := hred
  obtain ⟨d, hd⟩ := hdec
  exact ⟨d ∘ f, fun x => (hf x).trans (hd (f x))⟩

/-- Alias for `reduces_complement`. If `p` reduces to `q`, then the complement of `p` reduces to the complement of `q`. -/
theorem red_comp {p : X → Prop} {q : Y → Prop}
    (h : p ⪯ₘ q) : Complement p ⪯ₘ Complement q :=
  reduces_complement h

/-- Close a reduction goal by chaining through a list of known reductions. -/
macro "reduce_chain" H:term : tactic =>
  `(tactic| repeat (first | exact reduces_reflexive _ | apply reduces_transitive $H))

end DiagonaLean.Synthetic.ReductionChain
