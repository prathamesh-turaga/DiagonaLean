/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.PCP.Basic

@[expose] public section

/-!
# Modified Post Correspondence Problem (MPCP)

MPCP is PCP with a designated *start tile*: every solution must begin with
the start tile.  MPCP serves as the intermediate step in the undecidability
reduction chain `Halt ≤_m MPCP ≤_m PCP`.
-/

namespace DiagonaLean.MPCP
open DiagonaLean.PCP


variable {α : Type}

/-- `MHasSolution c P` holds iff there is some stack `A` (possibly empty)
drawn from `c :: P` such that prepending `c` makes the top and bottom
concatenations agree:

  `c.top ++ τ1 A = c.bot ++ τ2 A`.

The full MPCP solution is `c :: A` — `c` is the forced start tile. -/
def MHasSolution (c : Tile α) (P : Stack α) : Prop :=
  ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: P) ∧
    c.top ++ τ1 A = c.bot ++ τ2 A

abbrev MPCP : Tile Bool × Stack Bool → Prop := fun ⟨c, P⟩ => MHasSolution c P

end DiagonaLean.MPCP
