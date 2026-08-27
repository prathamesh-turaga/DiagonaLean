/-
Copyright (c) 2026 Prathamesh Turaga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.PCP.Reductions.Halt_to_PCP
import DiagonaLean.PCP.Basic

/-! # The `reduceFromPCP` tactic

Every "target problem `Q` is undecidable by reduction from PCP" proof in this development
follows the same three steps:

1. `apply undecidability_from_reducibility (p := PCP.DecisionProblem)`;
2. `apply pcp_undecidable (α := ⟨alphabet⟩)`;
3. supply the reduction data — a function `f : Stack α → InstanceType Q` and, for every
   `K`, an equivalence `PCP.DecisionProblem K ↔ Q (f K)`.

Only step 3 is target-specific. `reduceFromPCP` mechanises the first two steps and, in its
richer forms, the surrounding `intro`/`refine`/`Iff` scaffolding of step 3 as well.

## Variants

| Form                                                      | Remaining goals                                  |
| :-------------------------------------------------------- | :----------------------------------------------- |
| `reduceFromPCP`                                             | `alpha`, `instDecEq`, `instNontrivial`, `f`, `forward`, `backward` |
| `reduceFromPCP over_type α`                                 | `f`, `forward`, `backward`                       |
| `reduceFromPCP over_type α with_red_function f`             | `forward`, `backward`                            |
| `reduceFromPCP over_type α with_red_function f using_lemmas fwd bwd` | none |

In every variant `K` is the current PCP instance, `hPCP : PCP.DecisionProblem K` is
available in the `forward` goal, and `hC : Q (f K)` is available in the `backward` goal.

The `using_lemmas` form matches the naming convention every reduction file already follows,
where the two directions of the correctness equivalence are called `<target>_if_pcp` and
`pcp_if_<target>`.
-/

open DiagonaLean.PCP DiagonaLean.Synthetic.Notation DiagonaLean.PCP.Reduction

/-- Syntax for the `reduceFromPCP` tactic. See the module docstring for the four forms. -/
syntax "reduceFromPCP"
  ("over_type" term ("with_red_function" term ("using_lemmas" term:max term:max)?)?)? : tactic

/-
Hygiene is disabled so that the pattern names `K`, `hPCP`, and `hC` introduced by the
macro expansion are the literal identifiers the caller sees in the residual goals. Under
default hygiene the macro's binders would be renamed to fresh, caller-inaccessible names,
so any follow-up `exact … hPCP` would fail with an "unknown identifier" error. `pcp_undecidable`'s
instance arguments are elaborated with `@` so that their `DecidableEq`/`Nontrivial` goals
surface as named holes rather than being eagerly resolved by typeclass search; when the
alphabet is fixed up front, the tactic then tries `infer_instance` on those goals with a
targeted error on failure.
-/
set_option hygiene false in
macro_rules
  | `(tactic| reduceFromPCP) =>
    `(tactic|
        refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.pcp_undecidable ?alpha ?instDecEq ?instNontrivial)
          ⟨?f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩)
  | `(tactic| reduceFromPCP over_type $alpha) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.pcp_undecidable $alpha ?instDecEq ?instNontrivial)
          ⟨?f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceFromPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceFromPCP`."))
  | `(tactic| reduceFromPCP over_type $alpha with_red_function $f) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.pcp_undecidable $alpha ?instDecEq ?instNontrivial)
          ⟨$f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceFromPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceFromPCP`."))
  | `(tactic| reduceFromPCP over_type $alpha with_red_function $f using_lemmas $fwd $bwd) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.pcp_undecidable $alpha ?instDecEq ?instNontrivial)
          ⟨$f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceFromPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceFromPCP`."
         case forward =>
           first
           | exact $fwd hPCP
           | fail "reduceFromPCP: the forward lemma did not close `⊢ <target> (f K)` from `hPCP : PCP.DecisionProblem K`. Check its statement/argument order, or discharge this goal manually with `case forward => ...`."
         case backward =>
           first
           | exact $bwd hC
           | fail "reduceFromPCP: the backward lemma did not close `⊢ PCP.DecisionProblem K` from `hC : <target> (f K)`. Check its statement/argument order, or discharge this goal manually with `case backward => ...`."))
