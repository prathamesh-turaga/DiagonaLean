```
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `UTMHalt`: The Universal Turing Machine Halting Problem Reductions
1. [`Halt ⪯ₘ UTMHalt`](#halt-ₘ-utmhalt)

## `Halt ⪯ₘ UTMHalt`
The reduction is immediate from the definition of weak universality: `hU M w` gives the equivalence directly.

### Non-existence of a Halt Decider (`not_exists_haltDeciderFor_of_isWeaklyUniversal`)
If `D` decided `UTMHalt U`, then `isHaltDecider_of_isHaltDeciderFor` would promote `D` to a general halt decider: on input `(M, w)`, simulate `D` on `pair (encodeBoolTM M) w`, using universality to transfer the result back to `Halts M w`. This contradicts `halt_undecidable`.

### Supporting Results
| Lemma | Statement |
|---|---|
| `IsWeaklyUniversalWrt.exists_halts` | `U` halts on at least one input (witnessed by `haltTM`) |
| `IsWeaklyUniversalWrt.exists_not_halts` | `U` diverges on at least one input (witnessed by `loopTM`) |
| `isHaltDecider_of_isHaltDeciderFor` | a decider for `UTMHalt U` is a decider for `HaltProblem` |
