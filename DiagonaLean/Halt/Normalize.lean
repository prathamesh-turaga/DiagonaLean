import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
import Cslib.Foundations.Data.BiTape
import DiagonaLean.Halt.Basic
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.Halt.Normalize.Properties

/-! # Normalisation of Turing machines

The reduction from the halting problem to MPCP in
`DiagonaLean.MPCP.Reductions.Halt_to_MPCP` assumes that the machine never writes a blank
(`NoBlankWrites`) and never moves left at the left end of its tape (`NoLeftBoundary`).

`normalize_tm` removes both assumptions: every machine over the alphabet `Bool` can be
replaced, together with its input, by a machine over the alphabet `Bool × Bool` satisfying
both conditions and halting exactly when the original machine halts.

The witnesses are the explicit construction `normTM` (see `Normalize.Machine`) together with
the encoded input `encInput`: the tape of `normTM tm` carries a marker in its leftmost cell
and the bi-infinite tape of `tm` folded onto the cells to the right of the marker, with a
blank written by `tm` represented by a dedicated non-blank symbol.
-/

open Cslib.Turing SingleTapeTM

namespace DiagonaLean.Normalize

open MPCP.Reduction DiagonaLean.Halt

/-- Every Turing machine `tm` over `Bool` and input `w` can be normalised: there are a
machine `tm'` over `Bool × Bool` and an input `w'` such that `tm'` never writes a blank,
never moves left at the left end of its tape on input `w'`, and halts on `w'` exactly when
`tm` halts on `w`. -/
theorem normalize_tm (tm : SingleTapeTM Bool) (w : List Bool) :
    ∃ (tm' : SingleTapeTM (Bool × Bool)) (w' : List (Bool × Bool)),
      NoBlankWrites tm' ∧ NoLeftBoundary tm' w' ∧ (Halts tm w ↔ Halts tm' w') :=
  ⟨normTM tm, encInput w, normTM_noBlankWrites tm, normTM_noLeftBoundary tm w,
    halts_normTM_iff tm w⟩

end DiagonaLean.Normalize
