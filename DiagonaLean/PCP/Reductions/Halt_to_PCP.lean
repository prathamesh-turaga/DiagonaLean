/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP

@[expose] public section

/-!
# `Halt ≤_m PCP` — composing the two reductions

both finite and computably constructed from `tm` and `w`.

This is the mathematical core of the standard Hopcroft–Ullman reduction
from the halting problem to PCP. Concluding "PCP is undecidable" from
here requires (a) a proof or axiom that `Halts` is itself undecidable —
not provided in this repository or in cslib — and (b) HUM normalisation
to remove the `NoBlankWrites` / `NoLeftBoundary` side conditions.
-/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction DiagonaLean.Halt

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- **`Halt ≤_m PCP`**: a TM `tm` halts on input `w` iff the explicit
PCP instance `mpcpToPcp (startTile tm w) (haltTiles tm)` has a solution.

Both directions rely on the HUM side conditions:
* `NoBlankWrites tm` — `tm.tr` never writes the blank symbol.
* `NoLeftBoundary tm w` — no reachable cfg invokes a left-move at the
  left tape boundary.

Lifting these is the subject of a future `PCP.Normalize` module. -/
theorem halt_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm)) :=
  (halt_iff_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)

end DiagonaLean.PCP.Reduction
