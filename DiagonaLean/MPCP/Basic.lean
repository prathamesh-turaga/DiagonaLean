/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.PCP.Basic

/-! # Modified Post Correspondence Problem

Central notions/types and the solvability predicate for the Post Correspondence Problem.
MPCP is PCP with a designated start tile: every solution must begin with it.
MPCP serves as the intermediate step in the reduction chain `Halt ⪯ₘ MPCP ⪯ₘ PCP`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

@[expose] public section

namespace DiagonaLean.MPCP

open DiagonaLean.PCP

variable {α : Type}

/-- `MHasSolution c P` holds iff there exists a stack `A` drawn from `c :: P`
such that `c.top ++ τ1 A = c.bot ++ τ2 A`. The full solution is `c :: A`;
`c` is the forced start tile. -/
def DecisionProblem (c : Tile α) (P : Stack α) : Prop :=
  ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: P) ∧
    c.top ++ τ1 A = c.bot ++ τ2 A

/-- The MPCP decision problem over `Bool`. -/
abbrev MPCP_Problem : Tile Bool × Stack Bool → Prop := fun ⟨c, P⟩ => DecisionProblem c P

end DiagonaLean.MPCP
