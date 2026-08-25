import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.PCP.Reductions.Halt_to_PCP
import DiagonaLean.PCP.Basic

open DiagonaLean.PCP
open DiagonaLean.Synthetic.Notation
open DiagonaLean.PCP.Reduction

/-
reduceToPCP — generalized proof method for "X reduces to PCP" proofs.

DESIGN INSIGHT, confirmed by the matmort_undecidable walkthrough:
every reduction-to-PCP proof in this codebase has the exact same first two
steps, word for word, regardless of target:

  1. apply undecidability_from_reducibility (p := PCP.DecisionProblem)
  2. apply PCP_undecidable_Gen (α := <alphabet>)

Only the THIRD step is ever target-specific:

  3. exact ⟨f, correctness_iff⟩
     -- f : Stack <alphabet> → <target's instance type>
     -- correctness_iff : ∀ K, PCP.DecisionProblem K ↔ target (f K)

This file documents that structure as the reusable "key intermediary goals"
any future reduction-to-PCP proof needs to supply, and gives two tactic
variants automating steps 1-2.
-/

-- ============================================================
-- VARIANT A: goal-based (what was asked for) — alpha as a goal
-- ============================================================
-- CONFIRMED (against a live elaborator): plain `apply ... (α := ?alpha)`
-- fails immediately with "failed to synthesize Nontrivial ?alpha" — typeclass
-- search runs right away and does not wait for a later `case alpha => ...` to
-- pin down the metavariable, so the original design below does not work.
--
-- Fix: apply `PCP_undecidable_Gen` with `@` so *every* argument — including
-- the `[DecidableEq α]`/`[Nontrivial α]` instances — becomes an explicit,
-- named hole instead of triggering automatic instance search. This costs two
-- extra goals (`instDecEq`, `instNontrivial`) that the caller now has to
-- close by hand (typically `infer_instance`, once `case alpha` has fixed the
-- alphabet), but it's what makes the goal-based UX actually elaborate.
--
-- Also folded the two `apply`s + `rotate_left` + `refine` into one `refine`:
-- chaining separate top-level tactics left goal order to fend for itself
-- (fragile under any change to `undecidability_from_reducibility`'s argument
-- order), whereas one `refine` creates every hole in one pass and `case`
-- addresses them by name regardless of order.
--
-- `correctness` further splits: `∀ K, PCP.DecisionProblem K ↔ target (f K)`
-- always starts the same way no matter what `target` is — `intro K`, split
-- the `Iff`, name each direction's hypothesis — so that much is mechanized
-- too, leaving `forward` (context: `K`, `hPCP : PCP.DecisionProblem K`,
-- goal `target (f K)`) and `backward` (context: `K`, `hC : target (f K)`,
-- goal `PCP.DecisionProblem K`). Anything past that point (e.g. `simp`,
-- destructuring `hPCP`/`hC` further) is target-specific and stays with the
-- caller, since `target`'s own shape isn't guaranteed to look like
-- `PCP.DecisionProblem`'s.

syntax "reduceToPCP"
  ("over_type" term ("with_red_function" term ("using_lemmas" term:max term:max)?)?)? : tactic

-- `K`, `hPCP`, `hC` below are meant to be real, literal names the caller's
-- following tactic script can refer to (matching the `case` examples in the
-- doc comments) — without this, macro hygiene renames them to fresh,
-- inaccessible identifiers, and `exact ... hPCP` etc. fails with "unknown
-- identifier" outside the macro's own expansion.
--
-- `over_type $alpha (with_red_function $f (using_lemmas $fwd $bwd)?)?`: when
-- the alphabet is supplied up front, it's a concrete term (not a
-- metavariable) by the time `instDecEq`/`instNontrivial` are elaborated, so —
-- unlike the bare form below — typeclass search for them can actually
-- succeed right here. We still route through `@`-explicit + `infer_instance`
-- (rather than leaving the instance arguments implicit, which would trigger
-- Lean's own eager search and abort with its generic "failed to synthesize"
-- error) so that a genuine failure instead produces our own actionable hint.
-- The bare form can't get this same treatment automatically: `alpha` is
-- still an unassigned metavariable at the point this macro expands, so
-- attempting `infer_instance` there would just fail immediately — before
-- the caller has even had a chance to supply `alpha` via `case alpha`.
-- Automating `instDecEq`/`instNontrivial` therefore requires the alphabet
-- up front; there's no way to defer it to "whenever `case alpha` eventually
-- runs" from inside a plain macro.
--
-- `using_lemmas $fwd $bwd`: every reduction file in this codebase names its
-- two correctness directions `<target>_if_pcp`/`pcp_if_<target>` (see
-- `pcp_if_matmort`/`matmort_if_pcp`, `ambiguous_if_pcp`/`pcp_if_ambiguous`).
-- Once those two lemmas already exist, closing `forward`/`backward` from
-- them is pure boilerplate — `exact $fwd hPCP`/`exact $bwd hC` — so this
-- wires it in directly instead of making every caller retype it. This is
-- purely a "last mile" convenience: it does none of the actual reduction's
-- mathematical work (that's `$fwd`/`$bwd` themselves), it just plugs
-- already-proved lemmas into the two goals they're shaped for. On failure
-- (wrong argument order, a mismatched conclusion, etc.) it falls back to a
-- hint rather than a bare unification error.
set_option hygiene false in
macro_rules
  | `(tactic| reduceToPCP) =>
    `(tactic|
        refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.PCP_undecidable_Gen ?alpha ?instDecEq ?instNontrivial)
          ⟨?f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩)
  | `(tactic| reduceToPCP over_type $alpha) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.PCP_undecidable_Gen $alpha ?instDecEq ?instNontrivial)
          ⟨?f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceToPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceToPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceToPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceToPCP`."))
  | `(tactic| reduceToPCP over_type $alpha with_red_function $f) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.PCP_undecidable_Gen $alpha ?instDecEq ?instNontrivial)
          ⟨$f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceToPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceToPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceToPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceToPCP`."))
  | `(tactic| reduceToPCP over_type $alpha with_red_function $f using_lemmas $fwd $bwd) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.PCP_undecidable_Gen $alpha ?instDecEq ?instNontrivial)
          ⟨$f, fun K => ⟨fun hPCP => ?forward, fun hC => ?backward⟩⟩
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceToPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceToPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceToPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceToPCP`."
         case forward =>
           first
           | exact $fwd hPCP
           | fail "reduceToPCP: the forward lemma did not close `⊢ <target> (f K)` from `hPCP : PCP.DecisionProblem K`. Check its statement/argument order, or discharge this goal manually with `case forward => ...`."
         case backward =>
           first
           | exact $bwd hC
           | fail "reduceToPCP: the backward lemma did not close `⊢ PCP.DecisionProblem K` from `hC : <target> (f K)`. Check its statement/argument order, or discharge this goal manually with `case backward => ...`."))

/-
Usage:

theorem matmort_undecidable :
    Undecidable (fun Ws => HasSolution Ws) := by
  reduceToPCP
  case alpha => exact S23
  case instDecEq => infer_instance
  case instNontrivial => infer_instance
  case f => exact fun K => {S, T} ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot))
  case forward => exact (pcp_iff_matmort K).mp hPCP
  case backward => exact (pcp_iff_matmort K).mpr hC

-- Or, with the alphabet supplied up front — `instDecEq`/`instNontrivial`
-- are resolved automatically and no longer appear as goals:

theorem matmort_undecidable' :
    Undecidable (fun Ws => HasSolution Ws) := by
  reduceToPCP over_type S23
  case f => exact fun K => {S, T} ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot))
  case forward => exact (pcp_iff_matmort K).mp hPCP
  case backward => exact (pcp_iff_matmort K).mpr hC

-- Or with both the alphabet and the reduction function supplied up front —
-- only `forward`/`backward` remain:

theorem matmort_undecidable'' :
    Undecidable (fun Ws => HasSolution Ws) := by
  reduceToPCP over_type S23 with_red_function
    (fun K => {S, T} ∪
      K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ∪
      K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot)))
  case forward => exact (pcp_iff_matmort K).mp hPCP
  case backward => exact (pcp_iff_matmort K).mpr hC

-- Or, once both correctness directions already exist as their own named
-- lemmas (the `<target>_if_pcp`/`pcp_if_<target>` convention every reduction
-- file in this codebase follows), supply them too — nothing left to prove:

theorem matmort_undecidable''' :
    Undecidable (fun Ws => HasSolution Ws) := by
  reduceToPCP over_type S23 with_red_function mat_image
    using_lemmas pcp_if_matmort matmort_if_pcp
-/

/-
COMMENTED OUT — superseded by Variant A's `over_type $alpha (with_red_function
$f)?` extension above, which gets the same "supply α up front" benefit
(sidesteps the eager instance-search failure) while additionally keeping the
forward/backward decomposition and auto-resolving `instDecEq`/`instNontrivial`
with an actionable error message on failure. Nothing in the codebase actually
called `reduceToPCP over ...` (checked via grep across all reduction files),
so this is kept only for reference/rollback, not wired to a live tactic name.

-- ============================================================
-- VARIANT B: argument-based (matches your manual proof exactly)
-- ============================================================
-- BUG (confirmed against a live elaborator): a bare `tactic| tac1 \n tac2
-- \n tac3` quotation only parses ONE tactic — `apply` closed itself out and
-- the elaborator then expected the antiquotation to end, choking on `apply`
-- (the second one) as a stray token. Wrapping the whole sequence in
-- parentheses `(tac1 \n tac2 \n tac3)` is what actually makes Lean parse it
-- as a single compound tactic; that was the only bug here — supplying
-- `$alpha` up front (unlike Variant A) sidesteps the DecidableEq/Nontrivial
-- ordering problem entirely, so the three steps below now do work in order.

syntax "reduceToPCP" "over" term : tactic

macro_rules
  | `(tactic| reduceToPCP over $alpha) =>
    `(tactic|
        (apply DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (p := DiagonaLean.PCP.DecisionProblem)
         apply DiagonaLean.PCP.Reduction.PCP_undecidable_Gen (α := $alpha)))

Usage — this is your manual proof, unchanged, minus the boilerplate:

theorem matmort_undecidable :
    Undecidable (fun Ws => HasSolution Ws) := by
  reduceToPCP over S23
  unfold Synthetic.Definitions.ManyOneReduces
  exact ⟨fun K => {S, T} ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ∪
    K.toFinset.image (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot)),
    pcp_if_matmort⟩
-/

-- ============================================================
-- The teaching payoff, either variant: what a NEW reduction-to-PCP
-- proof always needs to supply, regardless of target.
-- ============================================================
/-
1. Which alphabet does your target's own PCP-style solvability predicate
   live over? (S23 for MatMort; a general α for EmpCFG.)
2. `f : Stack <your alphabet> → <your target's instance type>` — the
   actual encoding of a PCP instance into your target's domain.
3. `∀ K, PCP.DecisionProblem K ↔ <target> (f K)` — the correctness proof
   that makes `f` a genuine many-one reduction. This is the real
   mathematical content of the proof; everything else is boilerplate.

(`Encodable tm.State` for every `SingleTapeTM Bool` no longer needs to be
supplied here — it's discharged globally by the `noncomputable instance`
in `Halt_to_PCP.lean`, so instance search fills it wherever
`PCP_undecidable_Gen` needs it.)
-/
