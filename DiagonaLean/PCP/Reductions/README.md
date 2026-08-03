```
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `PCP.Reductions`: Post's Correspondence Problem
1. [`MPCP ⪯ₘ PCP`](#mpcp-ₘ-pcp)
2. [`Halt ⪯ₘ PCP`](#halt-ₘ-pcp)

## `MPCP ⪯ₘ PCP`
Given an MPCP instance `(c, R)` (a distinguished tile `c` and a stack `R`), we construct a PCP instance `mpcpToPcp c R` such that `MHasSolution c R ↔ HasSolution (mpcpToPcp c R)`.

### Alphabet Extension
The alphabet `α` is extended with two fresh markers, `Ext α = α | # | ₹`, where `{⋕,₹} ∩ α = ∅` by construction.

### Interleaving Functions
Two functions interleave `#` into a word:
```
hashL [a₀, …, aₙ] = [#, ↟a₀, #, ↟a₁, …, #, ↟aₙ]
hashR [a₀, …, aₙ] = [↟a₀, #, ↟a₁, #, …, ↟aₙ, #]
```
The key duality being:
```
hashL x ++ [#] = # :: hashR x
```
This identity (`hashL_snoc_eq`) is what allows the end tile to close a solution.

### Tile Construction
Three tile roles are assigned:

| Tile | Top | Bottom | Role |
|---|---|---|---|
| `tileStart c` | `₹ :: hashL c.top` | `₹ :: # :: hashR c.bot` | Forces every solution to start here |
| `tileReg t` | `hashL t.top` | `hashR t.bot` | Encodes one MPCP card |
| `tileEnd` | `[#, ₹]` | `[₹]` | Closes the match via `hashL_snoc_eq` |

The reduced instance is thus:
```
mpcpToPcp c R = tileStart c :: regsOf (c :: R) ++ [tileEnd]
```
Here, `regsOf` filters out empty cards (which would otherwise produce spurious solutions).

### Forward Direction (`mpcp_to_pcp_solution`)
Given an MPCP solution `A` with `c.top ++ τ1 A = c.bot ++ τ2 A`, the PCP solution is `tileStart c :: regsOf A ++ [tileEnd]`.

Note that:
```
τ1 = ₹ :: hashL c.top ++ τ1 A ++ [#, ₹]
τ2 = ₹ :: # :: hashR c.bot ++ τ2 A ++ [₹]
```
Since `c.top ++ τ1 A = c.bot ++ τ2 A` and `hashL_snoc_eq` converts the trailing `[#, ₹]` on the top into the leading `#` on the bottom, the two sides match.

### Backward Direction (`pcp_to_mpcp_solution`)
`match_start`: any matching PCP solution must begin with `tileStart c`. The argument is by character analysis:
- All tile tops begin with `₹` (start tile), `#` (regular or end tile), or are empty.
- All tile bottoms begin with `₹` (start or end tile), `\hat{a}` (regular tile), or are empty.
- A regular tile as the first tile would force `τ1` to begin with `#` and
  `τ2` to begin with `↟a`, which cannot match.
- The end tile as the first tile forces an immediate contradiction.

(`pcp_to_mpcp_solution_gen`): after stripping the start tile, the residual satisfies
```
hashL c.top ++ τ1 B' = # :: hashR c.bot ++ τ2 B'
```
The generalized lemma proceeds by induction on the remaining stack, maintaining a matching state `(u, v)` for accumulated tops and bottoms:
- Start tile midstream: ruled out by `hashL_append_dollar_ne`.
- End tile: `hashR_append_dollar_inj` forces `u = v`, closing the match with an empty MPCP solution.
- Regular tile `tileReg s`: extend `u ← u ++ s.top` and `v ← v ++ s.bot` and recurse.

## `Halt ⪯ₘ PCP`
Follows trivially from the transitivity of many-one reductions.
