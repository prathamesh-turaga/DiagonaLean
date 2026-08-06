/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic

/-! # Core synthetic computability definitions

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

@[expose] public section

namespace DiagonaLean.Synthetic.Definitions
open DiagonaLean.Halt Cslib.Turing

variable {X Y Z : Type*}

/-- `Complement P` is the complement decision problem. -/
def Complement (P : X → Prop) : X → Prop := fun x => ¬P x

/-- `Reflects b p` means provability of `p` coincides with `b = true`. -/
def Reflects (b : Bool) (p : Prop) : Prop := p ↔ b = true

/-- `Decider f P` means `f` pointwise reflects `P` via `reflects`. -/
def Decider (f : X → Bool) (P : X → Prop) : Prop :=
  ∀ x, Reflects (f x) (P x)

/-- `decidable P` means there exists a total Boolean decider for `P`. -/
def SDecidable (P : X → Prop) : Prop :=
  ∃ f : X → Bool, Decider f P

/-- `enumerator f P` means `f` surjects onto the positive instances of `P`. -/
def Enumerator (f : ℕ → Option X) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f n = some x

/-- `enumerable P` means there exists an enumerator for `P`. -/
def SEnumerable (P : X → Prop) : Prop :=
  ∃ f : ℕ → Option X, Enumerator f P

/-- `semi_decider f P` means `f` semi-decides `P` via Boolean sequences. -/
def SemiDecider (f : X → ℕ → Bool) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f x n = true

/-- `semi_decidable P` means there exists a semi-decider for `P`. -/
def SemiDecidable (P : X → Prop) : Prop :=
  ∃ f : X → ℕ → Bool, SemiDecider f P

/-- `reduction f P Q` means `f` many-one reduces `P` to `Q`. -/
def Reduction (f : X → Y) (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∀ x, P x ↔ Q (f x)

/-- Many-one reducibility. -/
def ManyOneReduces (p : X → Prop) (q : Y → Prop) : Prop :=
  ∃ f : X → Y, ∀ x, p x ↔ q (f x)

/-- If `p` many-one reduces to `q` then we write `p ⪯ₘ q`. -/
notation:50 p " ⪯ₘ " q => ManyOneReduces p q

end DiagonaLean.Synthetic.Definitions
