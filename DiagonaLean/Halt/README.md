```
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `Halt`: The Turing Machine Halting Problem

## Problem Statement
Does there exist a Turing Machine (TM) `D` (over the alphabet `Option Bool`, *TODO: generalize this to Option Symbol*) that satisfies the following specification?

The specification: it takes as input an encoding of a different TM `D'` and an input to `D'`, `w`, and outputs `true` on the tape if `D'` halts on input `w`, and `false` if it does not halt on input `w`.

We show the nonexistence of the decider `D` for the halting problem of `D'` on input `w`, which means that the halting problem is *undecidable*.

## Proof Outline
The main result is:
```
theorem halt_undecidable : ¬ ∃ D : SingleTapeTM Bool, IsHaltDecider D
```
where `IsHaltDecider D` asserts that for every TM `M` and input `w`, `D` outputs `[true]` from input `encodePair (encodeBoolTM M) w` if `M` halts on `w`, and `[false]` otherwise.

### Encodings
We first define encodings of TMs as Boolean strings as described in [HopcroftMotwaniUllman2006]. TMs over `Bool` are encoded as binary strings via `encodeBoolTM`:
```
encodeBoolTM : (tm : SingleTapeTM Bool) → [DecidableEq tm.State] → List Bool
```
The encoding records the initial state index and the transition table.

States, tape symbols, and directions are assigned unary indices separated by
`true`. A transition `δ(q, x) = (q', sym, dir)` is encoded as five
unary fields separated by single `true` bits. The full transition table is
encoded as a sequence of transition encodings separated by `[true, true]`.
The machine encoding prepends the initial state index. The number of
consecutive `true` bits indicates nesting depth:

| Separator | Occurrence |
|---|---|
| `[true]` | between fields within a transition |
| `[true, true]` | between transitions in the table |
| `[true, true, true]` | between initial state and transition count |
| `[true, true, true, true]` | between transition count and transition table |

The full TM encoding is:
```
q₀ ++ [true,true,true] ++ n ++ [true,true,true,true] ++ transition_table
```

Pairs of inputs are encoded via:
```
encodePair (a b : List Bool) : List Bool := a ++ [true, true] ++ b
```

For completeness, we also define decodings, show that the encodings satisfy `decode*(encode* w) = some w`, and prove the injectivity of the encodings, though these are not strictly required in the proof of the undecidability of the Halting problem.

### Diagonalization
#### Self-Halting
The self-halting problem asks whether a TM `M` halts when run on its own
encoding `encodeBoolTM M`. We first prove this is undecidable:

```
theorem self_halt_undecidable : ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```

Assume `D` is a self-halt decider. Construct `diagTM D`, which on input `w`:
1. Simulates `D` on `w` (treating `w` as an encoding of a TM).
2. If `D` outputs `[true]`, loops forever.
3. If `D` outputs `[false]`, halts immediately.

Now consider running `diagTM D` on `encodeBoolTM (diagTM D)`:
- If `diagTM D` halts on `encodeBoolTM (diagTM D)`: by `IsSelfHaltDecider`,
  `D` outputs `[true]`, so by construction `diagTM D` loops. This is a contradiction (from `lemma diagTM_loops_of_outputs_true {w : List Bool} (h : SingleTapeTM.Outputs D w [true]) : ¬ Halts (diagTM D) w`)
- If `diagTM D` does not halt on `encodeBoolTM (diagTM D)`: by
  `IsSelfHaltDecider`, `D` outputs `[false]`, so by construction `diagTM D`
  halts. This is also a contradiction (from `lemma diagTM_halts_of_outputs_false {w : List Bool} (h : SingleTapeTM.Outputs D w [false]) : Halts (diagTM D) w `).

Thus, we prove `self_halt_undecidable`.

#### Halting
A halt decider for `(M, w)` immediately yields a self-halt decider, because we can set `w` to be the encoding of `M`.

```
lemma self_halt_decider_if_halt_decider : IsHaltDecider D → ∃ D' : SingleTapeTM Bool, IsSelfHaltDecider D'
```

The machine `D'` is thus `pairSelfTM` composed with `D`, where `pairSelfTM` maps
tape `encodeBoolTM M` to `encodePair (encodeBoolTM M) (encodeBoolTM M)` before handing off to `D`.

The contrapositive of this lemma tells us that there is no TM which is a halt-decider. ∎
