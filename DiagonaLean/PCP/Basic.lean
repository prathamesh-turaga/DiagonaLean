/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

@[expose] public section

/-!
# Post Correspondence Problem (PCP)

Core data and definition of PCP.

A PCP *instance* is a finite list of *tiles*, each pairing a top word with a
bottom word over an alphabet `α`. The instance is solvable iff some non-empty
sequence of tiles (with repetition allowed) yields equal concatenations of
tops and bottoms.

We use the Stack-based representation throughout — the same representation
used by Forster, Heiter, Smolka in their Coq formalisation in the
`coq-library-undecidability`. This style is well-suited to structural
induction and is the basis of the MPCP → PCP reduction in `PCP.Reduction`.
-/

namespace DiagonaLean.PCP

variable {α : Type}

/-! ## Core types -/

/-- A word over alphabet `α` is a list of symbols. -/
abbrev Word (α : Type) := List α

/-- A PCP tile pairs a top word with a bottom word. -/
structure Tile (α : Type) where
  top : Word α
  bot : Word α
  deriving DecidableEq, Repr

/-- A *stack* (PCP instance) is a list of tiles. -/
abbrev Stack (α : Type) := List (Tile α)

/-! ## Concatenation along a stack -/

/-- Concatenate the top words of a stack. -/
def τ1 : Stack α → Word α
  | []      => []
  | t :: A  => t.top ++ τ1 A

/-- Concatenate the bottom words of a stack. -/
def τ2 : Stack α → Word α
  | []      => []
  | t :: A  => t.bot ++ τ2 A

@[simp]
theorem τ1_nil : τ1 ([] : Stack α) = [] := rfl

@[simp]
theorem τ2_nil : τ2 ([] : Stack α) = [] := rfl

@[simp]
theorem τ1_cons (t : Tile α) (A : Stack α) :
  τ1 (t :: A) = t.top ++ τ1 A := rfl

@[simp]
theorem τ2_cons (t : Tile α) (A : Stack α) :
  τ2 (t :: A) = t.bot ++ τ2 A := rfl

@[simp]
theorem τ1_append (A B : Stack α) :
    τ1 (A ++ B) = τ1 A ++ τ1 B := by
  induction A with
  | nil => simp
  | cons t A ih => simp [ih, List.append_assoc]

@[simp]
theorem τ2_append (A B : Stack α) :
    τ2 (A ++ B) = τ2 A ++ τ2 B := by
  induction A with
  | nil => simp
  | cons t A ih => simp [ih, List.append_assoc]

/-! ## The PCP predicate -/

/-- `HasSolution P` holds iff some non-empty sub-stack `A` of `P` satisfies
`τ1 A = τ2 A`. -/
def HasSolution (P : Stack α) : Prop :=
  ∃ A : Stack α, A ≠ [] ∧ (∀ t ∈ A, t ∈ P) ∧ τ1 A = τ2 A

abbrev PCP : Stack Bool → Prop := HasSolution

end DiagonaLean.PCP
