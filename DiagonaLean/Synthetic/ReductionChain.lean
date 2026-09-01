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

/-- `id` witnesses that many-one reducibility is reflexive. -/
theorem reduces_reflexive_spec (P : X → Prop) : P ⪯ₘ[id] P :=
  fun _ => Iff.rfl

/-- Many-one reducibility is reflexive. `⪯ₘ` is data (see `ManyOneReduces`), so building one is
a `def`, not a `theorem`. -/
def reduces_reflexive (P : X → Prop) : P ⪯ₘ P :=
  ⟨id, reduces_reflexive_spec P⟩

/-- `hQR.f ∘ hPQ.f` -- the composition of the two witness functions -- witnesses that
many-one reducibility is transitive. -/
theorem reduces_transitive_spec {P : X → Prop} {Q : Y → Prop} {R : Z → Prop}
    (hPQ : P ⪯ₘ Q) (hQR : Q ⪯ₘ R) : P ⪯ₘ[hQR.f ∘ hPQ.f] R :=
  fun x => (hPQ.hf x).trans (hQR.hf (hPQ.f x))

/-- Many-one reducibility is transitive: compose the two witness functions. -/
def reduces_transitive {P : X → Prop} {Q : Y → Prop} {R : Z → Prop}
    (hPQ : P ⪯ₘ Q) (hQR : Q ⪯ₘ R) : P ⪯ₘ R :=
  ⟨hQR.f ∘ hPQ.f, reduces_transitive_spec hPQ hQR⟩

/-- Equivalent dependent formulation. -/
def reduces_dependent {P : X → Prop} {Q : Y → Prop} :
    (P ⪯ₘ Q) ≃ (∀ x, { y // P x ↔ Q y }) where
  toFun h x := ⟨h.f x, h.hf x⟩
  invFun g := ⟨fun x => (g x).val, fun x => (g x).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `h.f` -- the same witness function -- also witnesses that the complement of `P` reduces to
the complement of `Q`. -/
theorem reduces_complement_spec {P : X → Prop} {Q : Y → Prop}
    (h : P ⪯ₘ Q) : Complement P ⪯ₘ[h.f] Complement Q :=
  fun x => not_congr (h.hf x)

/-- If `P` reduces to `Q`, then the complement of `P` reduces to the complement of `Q`. -/
def reduces_complement {P : X → Prop} {Q : Y → Prop}
    (h : P ⪯ₘ Q) : Complement P ⪯ₘ Complement Q :=
  ⟨h.f, reduces_complement_spec h⟩

/-- If `p` many-one reduces to `q` and `q` is synthetically decidable, then `p` is also synthetically decidable. -/
theorem dec_red {p : X → Prop} {q : Y → Prop}
    (hred : p ⪯ₘ q) (hdec : SDecidable q) : SDecidable p := by
  obtain ⟨f, hf⟩ := hred
  obtain ⟨d, hd⟩ := hdec
  exact ⟨d ∘ f, fun x => (hf x).trans (hd (f x))⟩

/-- Alias for `reduces_complement`. If `p` reduces to `q`, then the complement of `p` reduces to the complement of `q`. -/
def red_comp {p : X → Prop} {q : Y → Prop}
    (h : p ⪯ₘ q) : Complement p ⪯ₘ Complement q :=
  reduces_complement h

/-- Close a reduction goal by chaining through a list of known reductions. -/
macro "reduce_chain" H:term : tactic =>
  `(tactic| repeat (first | exact reduces_reflexive _ | apply reduces_transitive $H))

end DiagonaLean.Synthetic.ReductionChain
