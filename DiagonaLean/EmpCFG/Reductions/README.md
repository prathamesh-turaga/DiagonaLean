```
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `EmpCFG.Reductions`: Deciding the Emptiness of the Intersection of CFGs
1. [`PCP ⪯ₘ EmpCFG`](#pcp-ₘ-empcfg)

## `PCP ⪯ₘ EmpCFG`
Given a PCP instance `P : Stack α`, construct two single-nonterminal grammars `topCFG P` and `botCFG P` over the terminal alphabet `α ⊕ Tile α`, where `α`-symbols sit on the `.inl` side and tile markers on the `.inr` side.

Each grammar has two rules per tile `t ∈ P`:

| Grammar | Recursive rule | Base rule |
|---|---|---|
| `topCFG` | `S → t.top.inl ++ S ++ [⌊t⌋]` | `S → t.top.inl ++ [⌊t⌋]` |
| `botCFG` | `S → t.bot.inl ++ S ++ [⌊t⌋]` | `S → t.bot.inl ++ [⌊t⌋]` |

where `⌊t⌋` denotes `Sum.inr t`. The recursive rule shape forces outer tiles to sit at the outer ends: a derivation from `S` tracing tiles `t₁, t₂, …, tₖ` produces the canonical string,
```
τ(A).map Sum.inl  ++  A.reverse.map Sum.inr
```
where `τ` is either `τ1` (for `topCFG`) or `τ2` (for `botCFG`).

### Forward Direction (`HasSolution P → IntersectionNonempty`)
Given a PCP solution `A` with `τ1 A = τ2 A`, both grammars derive the same canonical string `canonString Tile.top A = canonString Tile.bot A`. Hence, the intersection is nonempty.

### Backward Direction (`IntersectionNonempty → HasSolution P`)
The language characterization (`mem_language_iff_canonString`) shows that every word in `(genCFG proj P).language` is `canonString proj A` for some nonempty `A ⊆ P`. This is proved via the `Form` invariant: any string reachable from `[S]` is either in the intermediate form
```
embedA (τProj proj A) ++ [S] ++ embedT A.reverse
```
or the terminal form `embedA (τProj proj A) ++ embedT A.reverse`. The invariant is preserved by each `Produces` step by case analysis on the applied rule.

Given a word `w` in both languages, we get stacks `A_top` and `A_bot` with `canonString Tile.top A_top = canonString Tile.bot A_bot`. The `.inl`/`.inr` split lemma (`list_inl_inr_split`) uniquely decomposes the shared word,
forcing `τ1 A_top = τ2 A_bot` and `A_top = A_bot`; hence, a PCP solution.
