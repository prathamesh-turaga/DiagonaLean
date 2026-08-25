# Summary of changes for run 4769b0dc-c95c-4b61-8a36-25fcf138747a
**Result: the `sorry` in `Normalize.lean` is gone — `normalize_tm` is proved in full, with no `sorry`, no new axioms (only `propext`, `Classical.choice`, `Quot.sound`), and a clean, warning-free build.**

**Project setup.** The file imported `Cslib` and `DiagonaLean`, which the project did not depend on, so it could not compile at all. I set the toolchain to `leanprover/lean4:v4.33.0-rc2`, added `DiagonaLean` (which brings in `cslib` and Mathlib) as a dependency in `lakefile.toml`, and wrote a matching `lake-manifest.json` pinned to the upstream revisions, so the project builds as `lake build`.

**What was proved.** Rather than a non-constructive argument, `normalize_tm` is witnessed by an explicit machine and input:

- `normTM tm` (in `Normalize/Machine.lean`) simulates `tm` on a *folded* tape: cell `0` holds a left-end marker, cell `j ≥ 0` of `tm` is stored at cell `2j+1` and cell `j < 0` at cell `-2j`. A blank written by `tm` is represented by a dedicated non-blank symbol, so the machine never writes a blank; the marker lets it detect the fold point, which is the only place where the head bookkeeping is irregular. Auxiliary control states simulate one step of `tm` in one to three steps.
- `encInput w` is the marker followed by `w` interleaved with the blank-representing symbol.

The three required facts are proved separately and combined:
- `normTM_noBlankWrites` : the machine never writes a blank;
- `normTM_noLeftBoundary` : on `encInput w` no reachable configuration performs a left move at the left end of the tape;
- `halts_normTM_iff` : `normTM tm` halts on `encInput w` iff `tm` halts on `w` (forward simulation for one direction, and a reachability invariant showing every reachable configuration is a live simulation configuration for the other).

**Supporting development** (about 1250 lines total, split across files): `Normalize/Cell.lean` gives a cell-wise (`ℤ`-indexed) view of `BiTape` with its behaviour under `write`/`move`/`mk₁`; `Normalize/Invariant.lean` defines the simulation invariant relating the two tapes and its transformation lemmas; `Normalize/Steps.lean` describes one step from each control state; `Normalize/Sim.lean` assembles these into one step of `tm`; `Normalize/Input.lean` proves the invariant for the initial tape; `Normalize/Halting.lean` and `Normalize/Properties.lean` derive the reachability invariant, the halting equivalence, and the two normalisation conditions.

I also sanity-checked the construction computationally (a machine that moves left twice and halts, and a machine that loops moving left forever): the simulation halts exactly when the original does, and the head never leaves the region right of the marker.

This fills the gap noted upstream in `Halt_to_PCP`, where the side conditions `NoBlankWrites` and `NoLeftBoundary` are said to be removable "by a normalisation construction".