```
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `MPCP.Reductions`: The Modified Post's Correspondence Problem
1. [`Halt ⪯ₘ MPCP`](#halt-ₘ-mpcp)

## `Halt ⪯ₘ MPCP`
Given a TM `tm` and input `w`, construct an MPCP instance `(startTile tm w, haltTiles tm)` such that `Halts tm w  ↔  MHasSolution (startTile tm w) (haltTiles tm)`, subject to two HUM side conditions: `NoBlankWrites tm` (the transition function never writes a blank) and `NoLeftBoundary tm w` (no reachable configuration invokes a left-move at the left tape boundary).

## Proof Sketch
### Alphabet
The tape alphabet is extended to `Alpha Q S` with four constructors:

| Symbol | Notation | Meaning |
|---|---|---|
| `tape s` | `↟ₜs` | lifted tape symbol |
| `state q` | `↟ₛq` | TM state (marks head position) |
| `halt` | `h⊥` | halted-TM marker |
| `sep` | `#` | configuration separator |

### Configuration Encoding
A running configuration `⟨some q, t⟩` is encoded as
```
t.left.reverse ++ [↟ₛq] ++ [↟ₜt.head] ++ t.right
```
with the state symbol placed immediately before the head symbol. A halted configuration `⟨none, t⟩` uses `h⊥` in place of the state symbol. Each configuration block is wrapped in `#…#` separators.

### Tile Families
Five families of tiles are used:

| Tile | Top | Bottom | Role |
|---|---|---|---|
| `startTile tm w` | `[#]` | `# :: encodeCfg(initCfg) ++ [#]` | Seeds the bottom with the initial configuration |
| `copyTile tm a` | `[↟ₜa]` | `[↟ₜa]` | Copies an unchanged tape symbol |
| `sepTile tm` | `[#]` | `[#]` | Copies the configuration separator |
| Transition tiles | local window (top) | rewritten window (bot) | Advances the head by one TM step |
| `absorbLeftTile`, `absorbRightTile`, `finalTile` | — | — | Shrinks the halted encoding down to `[h⊥]` and closes the match |

The four transition tile constructors handle the four reachable TM-step cases:

| Case | Tile | Top | Bottom |
|---|---|---|---|
| No movement | `noMoveTile q a qNew w` | `[↟ₛq, ↟ₜa]` | `[stateMarker qNew, ↟ₜw]` |
| Right, interior | `rightMoveTile q a qNew w` | `[↟ₛq, ↟ₜa]` | `[↟ₜw, stateMarker qNew]` |
| Right, boundary | `rightMoveBoundaryTile q a qNew w` | `[↟ₛq, ↟ₜa, #]` | `[↟ₜw, stateMarker qNew, ↟ₜnone, #]` |
| Left, interior | `leftMoveTile q a qNew w b` | `[↟ₜb, ↟ₛq, ↟ₜa]` | `[stateMarker qNew, ↟ₜb, ↟ₜw]` |

where `stateMarker qNew = ↟ₛq'` if `qNew = some q'`, and `h⊥` if `qNew = none`.

`NoBlankWrites` ensures `w ≠ none` throughout, preventing blank-stripping
degeneracy in Cslib's `BiTape`. `NoLeftBoundary` ensures the left-boundary
case is never reached, so `leftMoveBoundaryTile` is omitted from `haltTiles`.

### Simulation Invariant
Throughout a matching solution, the bottom string is one configuration ahead of the top:
```
bot = top ++ encodeCfg(next config) ++ [#]
```
The `startTile` establishes this offset with `top = [#]` and `bot = # :: encodeCfg(initCfg) ++ [#]`. Each TM step is realised by a canonical tile block whose `τ1` reproduces the current configuration block and whose `τ2` extends the bottom by the next configuration block.

### Forward Direction (`mHasSolution_if_halt`)
Given a halting trace `initCfg →ⁿ ⟨none, tape⟩`, construct the solution
by induction on `n`:

Base case (`n = 0`, already halted): apply `absorbAndFinish`, which iteratively absorbs tape symbols around `h⊥` using `absorbLeftTile` and `absorbRightTile`, then closes with `finalTile`. The matching invariant `τ1 = encodeHaltList ++ [#] ++ τ2` is proved by structural induction (`absorbAndFinish_matching`).

Inductive step: prepend the canonical step tile block for the current TM step (`stepTiles tm q t`) whose `τ1` reproduces the current configuration block and whose `τ2` produces the next. `stepTiles_subset_haltTiles` confirms membership; `NoLeftBoundary` discharges the left-boundary sub-case.

> NOTE: `stepTilesLeftBoundary_subset_haltTiles` is intentionally not provided. Following Hopcroft–Ullman–Motwani's one-sided tape design, `leftMoveBoundaryTile` is *not* in `haltTiles`, so the sequence `stepTilesLeftBoundary` is not a subsequence of `haltTiles` either. The forward direction is gated by `NoLeftBoundary`, which ensures the dispatcher (`stepTilesAux`) never enters the left-boundary branch in a reachable configuration.

### Backward Direction (`halt_if_mHasSolution`)
The backward direction proceeds in two layers:

Layer 1 (Structural forcing) (strong-A form, `backward_aux`): given `A ⊆ haltTiles tm`, strong induction on `A.length` peels one canonical step block per TM step:
- `copy_prefix_forced`: the `liftTape L` prefix of `τ1 A` forces copy tiles for `L`.
- `transition_forced`: the `↟ₛq :: ↟ₜa` lead forces a transition tile for `(q, a)`.
- `copy_prefix_forced_state_lead`: the right-tape suffix forces copy tiles up to `#`.
- `sep_forced`: the `#` lead forces `sepTile`.

The right-boundary alternative (`rightMoveTile` vs `rightMoveBoundaryTile`) is resolved by `no_tile_for_state_sharp`: a `rightMoveTile` decomposition would expose `↟ₛq :: # :: …` in a residual `τ1`, which no tile of `haltTiles` can consume. The halt-now sub-case (`qNew = none`, boundary) is handled directly by a single TM step.

Layer 2 (Queue-based extras) (`backward_aux_weak`): generalises Layer 1 to admit `A ⊆ startTile :: haltTiles tm`. A chain-tracked cfg queue threads reachability proofs `initCfg →* c` for each pending configuration `c`. When `startTile` appears mid-stream, it pushes both `stepResult` and a fresh `initCfg` (with `refl` chain) onto the queue. The key structural property `τ1_no_state_marker_then_sharp` (`τ1 A` never contains `↟ₛq :: # :: …` as a sub-list) discharges the alternative `rightMoveTile` path in the boundary case even with a nonempty queue.
