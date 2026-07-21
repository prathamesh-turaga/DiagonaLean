/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

import DiagonaLean.Halt.Basic

@[expose] public section

namespace DiagonaLean.Synthetic.Definitions
open DiagonaLean.Halt Cslib.Turing

variable {X Y Z : Type*}

/-! ## Core synthetic computability definitions -/

/-- `complement P` is the complement decision problem. -/
def complement (P : X → Prop) : X → Prop := fun x => ¬P x

/-- `reflects b p` means provability of `p` coincides with `b = true`. -/
def reflects (b : Bool) (p : Prop) : Prop := p ↔ b = true

/-- `decider f P` means `f` pointwise reflects `P` via `reflects`. -/
def decider (f : X → Bool) (P : X → Prop) : Prop :=
  ∀ x, reflects (f x) (P x)

/-- `decidable P` means there exists a total Boolean decider for `P`. -/
def SDecidable (P : X → Prop) : Prop :=
  ∃ f : X → Bool, decider f P

/-- `enumerator f P` means `f` surjects onto the positive instances of `P`. -/
def enumerator (f : ℕ → Option X) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f n = some x

/-- `enumerable P` means there exists an enumerator for `P`. -/
def SEnumerable (P : X → Prop) : Prop :=
  ∃ f : ℕ → Option X, enumerator f P

/-- `semi_decider f P` means `f` semi-decides `P` via Boolean sequences. -/
def semi_decider (f : X → ℕ → Bool) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f x n = true

/-- `semi_decidable P` means there exists a semi-decider for `P`. -/
def semi_decidable (P : X → Prop) : Prop :=
  ∃ f : X → ℕ → Bool, semi_decider f P

/-- `reduction f P Q` means `f` many-one reduces `P` to `Q`. -/
def reduction (f : X → Y) (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∀ x, P x ↔ Q (f x)

/-- Many-one reducibility. -/
def ManyOneReduces (p : X → Prop) (q : Y → Prop) : Prop :=
  ∃ f : X → Y, ∀ x, p x ↔ q (f x)

notation:50 p " ⪯ₘ " q => ManyOneReduces p q


end DiagonaLean.Synthetic.Definitions
