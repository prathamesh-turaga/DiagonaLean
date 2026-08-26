/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-! # Post Correspondence Problem

Central notions/types and the solvability predicate for the Post Correspondence Problem.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHSmolka2019]
-/

@[expose] public section

namespace DiagonaLean.PCP

variable {α : Type}

/-- A PCP tile pairs a top word with a bottom word. -/
structure Tile (α : Type) where
  /-- The top word of the PCP tile -/
  top : List α
  /-- The bottom word of the PCP tile -/
  bot : List α
  deriving DecidableEq, Repr

/-- A PCP instance is a list of tiles. -/
abbrev Stack (α : Type) := List (Tile α)

/-- Concatenation of the top words of a stack. -/
def τ1 (A : Stack α) : List α := (A.map Tile.top).flatten

/-- Concatenation of the bottom words of a stack. -/
def τ2 (A : Stack α) : List α := (A.map Tile.bot).flatten

/-- `τ1` of the empty stack is the empty word. -/
@[simp]
theorem τ1_nil : τ1 ([] : Stack α) = [] := rfl

/-- `τ2` of the empty stack is the empty word. -/
@[simp]
theorem τ2_nil : τ2 ([] : Stack α) = [] := rfl

/-- `τ1` of a cons stack prepends the head tile's top word. -/
@[simp]
theorem τ1_cons (t : Tile α) (A : Stack α) :
    τ1 (t :: A) = t.top ++ τ1 A := rfl

/-- `τ2` of a cons stack prepends the head tile's bottom word. -/
@[simp]
theorem τ2_cons (t : Tile α) (A : Stack α) :
    τ2 (t :: A) = t.bot ++ τ2 A := rfl

/-- `τ1` distributes over stack concatenation. -/
@[simp]
theorem τ1_append (A B : Stack α) :
    τ1 (A ++ B) = τ1 A ++ τ1 B := by
  induction A with
  | nil => simp
  | cons t A ih => simp [ih, List.append_assoc]

/-- `τ2` distributes over stack concatenation. -/
@[simp]
theorem τ2_append (A B : Stack α) :
    τ2 (A ++ B) = τ2 A ++ τ2 B := by
  induction A with
  | nil => simp
  | cons t A ih => simp [ih, List.append_assoc]

/-- `P` has a solution if some non-empty subsequence `A` of `P` satisfies `τ1 A = τ2 A`. -/
def DecisionProblem (P : Stack α) : Prop :=
  ∃ A : Stack α, A ≠ [] ∧ (∀ t ∈ A, t ∈ P) ∧ τ1 A = τ2 A

/-- The PCP decision problem over `Bool`. -/
abbrev PCP_Problem : Stack Bool → Prop := DecisionProblem

end DiagonaLean.PCP
