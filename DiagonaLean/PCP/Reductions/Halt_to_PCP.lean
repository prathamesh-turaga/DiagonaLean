/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP

/-! # Halt ⪯ₘ PCP

The composition `Halt ≤ₘ MPCP ≤ₘ PCP`, giving a direct equivalence between
halting of a TM `tm` on input `w` and solvability of the PCP instance
`mpcpToPcp (startTile tm w) (haltTiles tm)`.

The reduction is subject to two side conditions (`NoBlankWrites` and
`NoLeftBoundary`) which can be removed by a normalisation construction;
this is left to a future `PCP.Normalize` module.
-/

@[expose] public section

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP.Reduction
     DiagonaLean.MPCP.Reduction DiagonaLean.Halt

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- `tm` halts on `w` iff the PCP instance `mpcpToPcp (startTile tm w) (haltTiles tm)`
has a solution, subject to `NoBlankWrites tm` and `NoLeftBoundary tm w`. -/
theorem halt_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm)) :=
  (halt_iff_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)

end DiagonaLean.PCP.Reduction
