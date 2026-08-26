import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.PCP.Basic
import DiagonaLean.PCP.Reductions.Halt_to_PCP


open DiagonaLean.Synthetic.Notation


/-
Tactic: `reduceFromPCP` (v2)

Changes from v1:
  1. `f` (the instance-encoding function) is no longer a required argument —
     it's left as a named goal `?f`, so its expected type is visible and it
     can be built incrementally/interactively like any other goal.
  2. The forward and backward correctness goals are no longer left as two
     opaque `Iff` halves. Since `PCP.HasSolution`'s own shape is fixed
     (∃ tiles, tiles ≠ [] ∧ (∀ t ∈ tiles, t ∈ K.toFinset) ∧ τ1 tiles = τ2 tiles
     — confirmed by the obtain/refine patterns in `pcp_if_matmort` /
     `exists_solution_from_prod`), the tactic pre-destructures it on the
     forward side and pre-splits it into its four fields on the backward
     side. Nothing about the *target* problem `q` is assumed anywhere —
     only PCP's own definition, which is the same in every such proof.

This intentionally does NOT try to generate a "canonical form" goal
(cf. `mortal_iff_exists_prod_of_Ws` in PCP_to_MatMort.lean): that lemma's
shape depends on the target problem having some notion of "combination"
(matrix products, in that case), which not every target problem has. That
piece stays bespoke per-target; the tactic only mechanizes what PCP itself
guarantees.
-/

/-- `reduceFromPCP` reduces a goal `undecidable q` to a many-one reduction from
    PCP, leaving PCP's fixed structure already unpacked. For an arbitrary
    instance `K`, leaves:

    1. `?f`     — construct the instance-encoding function `f : Stack Σ → Y`.
    2. Forward, pre-destructured — given `tiles : List (Tile Σ)`,
       `hne : tiles ≠ []`, `hmem : ∀ t ∈ tiles, t ∈ K`,
       `heq : τ1 tiles = τ2 tiles` in context, prove `q (f K)`.
    3. `?tiles` — construct the PCP witness tile list for the backward direction
       (you'll have `hq : q (f K)` in context).
    4. `?tiles ≠ []`
    5. `∀ t ∈ ?tiles, t ∈ K`
    6. `τ1 ?tiles = τ2 ?tiles`

    Goals 3–6 are exactly `PCP.DecisionProblem` unpacked, in order — the same
    four obligations every reduction-to-PCP backward direction has to
    produce, regardless of what `q` is.

    Uses `PCP_undecidable` as the base undecidability fact by default (with an
    arbitrary two-element type standing in for its unused distinctness
    hypothesis; its `Encodable tm.State` obligation is discharged globally by
    the `noncomputable instance` in `Halt_to_PCP.lean`, so no goal for it is
    produced); override with `from h` if you already have a proof of
    `Undecidable p` for some PCP-style `p` in scope
    (e.g. `PCP_undecidable_Gen (α := S23)`). -/

syntax "reduceFromPCP" ("from" term)? : tactic

macro_rules
  | `(tactic| reduceFromPCP) =>
    `(tactic|
        refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (DiagonaLean.PCP.Reduction.PCP_undecidable (b0 := true) (b1 := false) (by decide))
          ⟨?f, fun K =>
            ⟨fun ⟨tiles, hne, hmem, heq⟩ => ?_,
             fun hq => ⟨?tiles, ?_, ?_, ?_⟩⟩⟩)
  | `(tactic| reduceFromPCP from $h) =>
    `(tactic|
        (apply DiagonaLean.Synthetic.Notation.undecidability_from_reducibility $h
         refine ⟨?f, fun K =>
           ⟨fun ⟨tiles, hne, hmem, heq⟩ => ?_,
            fun hq => ⟨?tiles, ?_, ?_, ?_⟩⟩⟩))

/-
Usage against your MatMort example, once wired to the `undecidable` framework
(compare each numbered goal to the corresponding piece already proved in
PCP_to_MatMort.lean):

theorem matmort_undecidable :
    undecidable (fun Ws => HasSolution Ws) := by
  reduceFromPCP
  case f =>
    exact fun K => {S, T} ∪
      K.toFinset.image (fun tile => string_pair_to_W (liftS23 tile.top) (liftS23 tile.bot)) ∪
      K.toFinset.image
        (fun tile => string_pair_to_W (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot))
  -- forward: this is exactly the body of `pcp_if_matmort`, now with
  -- `tiles, hne, hmem, heq` already in context instead of a bundled `h`
  · ...
  -- backward's four goals are exactly what `matmort_if_pcp` (via
  -- `exists_solution_from_prod` / `bots_eq_of_word`) had to produce
  case tiles => ...
  · ...  -- nonempty
  · ...  -- membership
  · ...  -- τ1 = τ2, needs wordToInt_injective / liftS23_injective
-/
