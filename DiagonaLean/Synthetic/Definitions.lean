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

/-- `D` is a Turing-machine decider for `P` under the encoding `enc : X → List Bool`: it halts
on `enc x` with output `[true]` when `P x` holds, and `[false]` when it does not. -/
def TMDeciderFor (D : SingleTapeTM Bool) (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∀ x, (P x → SingleTapeTM.Outputs D (enc x) [true]) ∧
       (¬ P x → SingleTapeTM.Outputs D (enc x) [false])

/-- `P` is machine-decidable under `enc` if some `SingleTapeTM Bool` decides it via
`TMDeciderFor`. Unlike `SDecidable`, the witness here is an actual Turing machine, so this
predicate is not classically vacuous: `SDecidable P` holds for every `P` (via
`Classical.propDecidable`), but `MachineDecidable enc P` genuinely requires `P` to be
algorithmically decidable. -/
def MachineDecidable (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∃ D : SingleTapeTM Bool, TMDeciderFor D enc P

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

/-- Many-one reducibility: `f` witnesses `p ⪯ₘ q` when `p x ↔ q (f x)` for every `x`.

**Convention (not enforced by the type above).** Lean's logic is classical, so this bare
`∃ f, ...` is satisfiable by excluded-middle-style case splits on `p x` itself: pick a positive
witness of `q` when `p x` holds and a negative one otherwise, producing an `f` with no
algorithmic content that "reduces" almost any non-trivial `p` to almost any non-trivial `q`.
To keep `⪯ₘ` meaningful, every witness must be a function built from the *data* of `x` (and,
where needed, other data-level facts, such as an `Encodable` instance or a normalized-machine
witness) -- never one that inspects `p` or `q` to decide what to return. Noncomputability from
unrelated data-level choices is fine (see e.g. `PCP.Reduction.pcpRed`'s use of a classically
chosen `Encodable` instance for a TM's state type); noncomputability that comes from deciding
`p` or `q` is exactly the failure mode this rules out.
`scripts/check-classical-reductions.sh` gives a best-effort automated check for the most direct
form of this (see its header for what it does and does not catch). -/
def ManyOneReduces (p : X → Prop) (q : Y → Prop) : Prop :=
  ∃ f : X → Y, ∀ x, p x ↔ q (f x)

/-- If `p` many-one reduces to `q` then we write `p ⪯ₘ q`. -/
notation:50 p " ⪯ₘ " q => ManyOneReduces p q

end DiagonaLean.Synthetic.Definitions
