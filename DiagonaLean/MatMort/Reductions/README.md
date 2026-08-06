```
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `MatMort.Reductions`: The `3 × 3` Matrix Mortality Problem
1. [`PCP ⪯ₘ MatMort`](#pcp-ₘ-matmort)

## `PCP ⪯ₘ MatMort`
Given a PCP instance `K : Stack S23` (tiles over `{2, 3} = Fin 2`), define the matrix set
```
H(K) = {S, T} ∪ {W(liftS23 t.top, liftS23 t.bot)   | t ∈ K}
              ∪ {W(liftS23 t.top, 1 :: liftS23 t.bot) | t ∈ K}
```
where:
**`S`** (initialization):
```
S = [[1, 0, 1],
     [0, 0, 0],
     [0, 0, 0]]
```
Left-multiplying by `[a, b, c]` projects the first coordinate and produces `a · [1, 0, 1]`.

**`T`** (termination):
```
T = [[ 1, -1, 0],
     [-1,  1, 0],
     [ 0,  0, 0]]
```
Left-multiplying by `[a, b, c]` produces `(a - b) · [1, -1, 0]`, which is zero iff `a = b`.

**`W(U, V)`** (tile matrix): for words `U, V` over `{1, 2, 3}` with integer values `q = wordToInt U`, `p = 10^|U|`, `s = wordToInt V`, `r = 10^|V|`:
```
W(U, V) = [[p, 0, 0],
            [0, r, 0],
            [q, s, 1]]
```
Left-multiplying by `[x, y, 1]` appends `U` to the first coordinate and `V`
to the second: `[x, y, 1] · W(U, V) = [wordToInt(X ++ U), wordToInt(Y ++ V), 1]`.

Integers are encoded in base 10 using digits `{1, 2, 3}` (so no leading-zero ambiguity), lifted from `{2, 3}` via `liftS23`. The extra `1` prefix in `W(U, 1 :: V)` marks the start tile, needed to extract the unique `one₁₂₃` separator in the backward direction.

A sequence of `W`-matrices from `H(K)` left-multiplied by `[1, 0, 1]` accumulates the concatenation of top-words in coordinate 0 and bottom-words in coordinate 1 (`row_mul_prod`, `concatenation_mortal`).

### Forward Direction (`HasSolution K → Mortal H(K)`)
Given a solution `A = [t₀, t₁, …, tₖ]` with `τ1 A = τ2 A`, build the matrix sequence:
```
S · W(top(t₀), 1 :: bot(t₀)) · W(top(t₁), bot(t₁)) · ⋯ · W(top(tₖ), bot(tₖ)) · T
```
The product with `[1, 0, 1]` yields `[n, n, 1]` for some `n > 0` (since `τ1 A = τ2 A` and both encode to equal integers). By `S_prod_T_eq_zero`, `S · (W-product) · T = 0`.

### Backward Direction (`Mortal H(K) → HasSolution K`)
Step 1 (`mortal_extract`): given any sequence from `{S, T} ∪ Ws` with `[1, 0, 1] · product = 0`, extract a contiguous `W`-only subsequence `Run` satisfying `[1, 0, 1] · Run.prod = [h, h, 1]` for some `h > 0`. The proof traces the accumulated row vector through the sequence, handling `S` (resets to `a · [1, 0, 1]`) and `T` (collapses `(a - b) · [1, -1, 0]` to zero iff `a = b`) by strong induction.

Step 2 (`mortal_iff_exists_prod_of_Ws`): equivalence between mortality and the existence of a `W`-sequence with equal coordinates.

Step 3 (`exists_solution_from_prod`, `bots_eq_of_word`): from a `W`-sequence with `[1, 0, 1] · prod = [h, h, 1]`, recover the tile sequence. The key lemma `bots_eq_of_word` uses the unique occurrence of the leading `1`-marker (from `W(U, 1 :: V)`) to split the accumulated string and show `τ1 A = τ2 A`. The base-10 encoding ensures `wordToInt` is injective (`wordToInt_injective`), so equal integer coordinates imply equal words.

The main result is `pcp_iff_matmort`: for any PCP instance `K` over alphabet `{2, 3}`, `K` has a solution iff the explicitly constructed matrix set `H(K)` is mortal.
