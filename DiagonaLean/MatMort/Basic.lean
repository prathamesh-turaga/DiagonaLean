/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Data.Matrix.Basic

/-! # The Matrix Mortality Problem

Central notions/types and the solvability predicate for the Post Correspondence Problem.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

@[expose] public section

namespace DiagonaLean.MatMort
open Matrix

/-- A set of matrices has a mortality solution if there exists a finite sequence 
  (list) of matrices drawn from the set such that their product is the zero matrix. -/
def DecisionProblem (Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)) : Prop :=
  ∃ Ms' : List (Matrix (Fin 3) (Fin 3) ℤ), (∀ M ∈ Ms', M ∈ Ms) ∧ Ms'.prod = 0

/-- The formal definition of the Matrix Mortality Problem for 3×3 integer matrices.
  Given a finite set of matrices `Ms`, does there exist a sequence of matrices
  in `Ms` that multiply to zero? -/
abbrev MatMortProblem : (Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)) → Prop := DecisionProblem

end DiagonaLean.MatMort
