/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Foundations.Normalize
import DiagonaLean.PCP.Reductions.AlphabetLift

/-! # Halt ⪯ₘ PCP

The composition `Halt ⪯ₘ MPCP ⪯ₘ PCP`, giving a direct equivalence between halting of a TM
`tm` on input `w` and solvability of the PCP instance `mpcpToPcp (startTile tm w) (haltTiles tm)`.

`MPCP_to_PCP` supplies the intermediate step; `Foundations.Normalize` removes the
`NoBlankWrites` and `NoLeftBoundary` side conditions by simulating an arbitrary TM by a
normalised one. This shifts the tape alphabet to `Bool × Bool`, landing the reduction in
`Stack (Ext (Alpha ℕ (Bool × Bool)))`. Finally, `AlphabetLift` transports the resulting
instance back to the target alphabet via distinct elements `Ext.hash ≠ Ext.rupee`. -/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
open DiagonaLean.PCP.AlphabetLift

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Equivalence between TM halting and PCP under normalization conditions. -/
theorem halt_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) [Encodable Symbol] [Encodable tm.State]:
    Halts tm w ↔
    PCP.DecisionProblem (mpcpToPcp (startTile tm w) (haltTiles tm)) :=
  (halt_iff_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)

/-- Apply `g : α → β` symbolwise to both sides of a PCP tile. -/
def Tile.map {α β : Type} (g : α → β) (t : Tile α) : Tile β :=
  ⟨t.top.map g, t.bot.map g⟩

variable {α β : Type} (s : Stack α) (f : Tile α → Tile β)

/-- `τ1` commutes with mapping a function symbolwise over tiles. -/
theorem τ1_map {α β : Type} (g : α → β) (l : List (Tile α)) :
    τ1 (l.map (Tile.map g)) = (τ1 l).map g := by
  induction l with
  | nil => simp
  | cons l ls ih =>
    simp_all [List.map, Tile.map]

/-- `τ2` commutes with mapping a function symbolwise over tiles. -/
theorem τ2_map {α β : Type} (g : α → β) (l : List (Tile α)) :
    τ2 (l.map (Tile.map g)) = (τ2 l).map g := by
  induction l with
  | nil => simp
  | cons l ls ih =>
    simp_all [List.map, Tile.map]

/-- Extract a source stack from a mapped stack given elementwise preimages. -/
theorem exists_stack_of_mem_mapped (l : Stack β) (g : α → β) (S : Stack α)
    (h : ∀ t ∈ l, ∃ a ∈ S, Tile.map g a = t) :
    ∃ ls : Stack α, ls.map (Tile.map g) = l ∧ (∀ t ∈ ls, t ∈ S) := by
  choose fn hfn using h
  exact ⟨ l.attach.map (fun ⟨t, ht⟩ => fn t ht), by
    rw [List.map_map]
    simp [hfn]
    refine fun t x x_1 h => ?_
    grind ⟩

/-- Injective map on tiles preserves and reflects PCP solvability. -/
theorem decisionProblem_map_iff {α β : Type} (g : α → β) (hg : Function.Injective g)
    (S : Stack α) :
    PCP.DecisionProblem S ↔ PCP.DecisionProblem (S.map (Tile.map g)) := by
      constructor
      · rintro ⟨l, hne, heq ⟩
        simp_all
        unfold DecisionProblem
        use (l.map (Tile.map g))
        simp_all
        constructor
        · have l_elem: ∃ x, x ∈ l := by
            exact List.exists_mem_of_ne_nil l hne
          rcases l_elem with ⟨x, hx⟩
          have S_elemen: x ∈ S := by
             obtain ⟨hl, hr⟩ := heq
             exact hl x hx
          grind
        · have hg: τ1 (List.map (Tile.map g) l) = τ1 (l.map (Tile.map g)) := by simp
          rw [hg]
          rw [τ1_map, τ2_map]
          simp_all
      · rintro ⟨l, hne, heq⟩
        simp_all
        unfold DecisionProblem
        have exists_l': ∃ ls : Stack α, ls.map (Tile.map g) = l ∧ (∀t ∈ ls, t ∈ S) := by apply exists_stack_of_mem_mapped l g S heq.left
        obtain ⟨ls, hls, hS⟩ := exists_l'
        use ls
        refine ⟨?_, ?_, ?_⟩
        grind
        exact hS
        simp [←hls] at heq
        simp [τ1_map, τ2_map] at heq
        obtain ⟨heql, heqr⟩ := heq
        exact (List.map_inj_right hg).mp heqr

open Synthetic.Notation

/-- Map state labels inside an extended TM configuration alphabet. -/
def Alpha.map {Q Q' S : Type} (g : Q → Q') : Alpha Q S → Alpha Q' S
  | .tape s  => .tape s
  | .state q => .state (g q)
  | .halt    => .halt
  | .sep     => .sep

/-- `Alpha.map` preserves injectivity of state mappings. -/
theorem Alpha.map_injective {Q Q' S : Type} {g : Q → Q'} (hg : Function.Injective g) :
    Function.Injective (Alpha.map g : Alpha Q S → Alpha Q' S) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [Alpha.map]
  exact hg hxy

/-- Map symbol types in the PCP boundary extension type `Ext`. -/
def Ext.map {α β : Type} (g : α → β) : Ext α → Ext β
  | .sym a  => .sym (g a)
  | .hash   => .hash
  | .rupee  => .rupee

/-- `Ext.map` preserves injectivity of the underlying map. -/
theorem Ext.map_injective {α β : Type} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (Ext.map g) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [Ext.map]
  exact hg hxy

/-- Map TM halting instance to a PCP stack via integer state encoding. -/
def pcpRed (tm : SingleTapeTM Symbol) (w : List Symbol)
    [Encodable Symbol] [Encodable tm.State] : Stack (Ext (Alpha ℕ Symbol)) :=
  (mpcpToPcp (startTile tm w) (haltTiles tm)).map
    (Tile.map (Ext.map (Alpha.map Encodable.encode)))

/-- State encoding preserves and reflects PCP solvability. -/
theorem pcpRed_iff (tm : SingleTapeTM Symbol) (w : List Symbol)
    [Encodable Symbol] [Encodable tm.State] :
    PCP.DecisionProblem (mpcpToPcp (startTile tm w) (haltTiles tm)) ↔
    PCP.DecisionProblem (pcpRed tm w) :=
  decisionProblem_map_iff (Ext.map (Alpha.map Encodable.encode))
    (Ext.map_injective (Alpha.map_injective Encodable.encode_injective))
    (mpcpToPcp (startTile tm w) (haltTiles tm))

variable (α : Type*) [Fintype α]

/-- The reduction function witnessing `HaltProblem ⪯ₘ PCP.DecisionProblem`: normalizes the
machine and input to satisfy `NoBlankWrites`/`NoLeftBoundary`, encodes states via `pcpRed`
(using `tm.stateEncodable`, composed with the hand-written `Encodable` instance for the
normalizer's `Ctrl` control states, to stay computable), and lifts the result to the fixed
alphabet `Ext (Alpha ℕ Bool)`. -/
def haltToPcp (p : EncodableTM Bool × List Bool) : Stack (Ext (Alpha ℕ Bool)) :=
  letI := p.1.stateEncodable
  letI : Encodable (Foundations.Normalize.normTM p.1.toSingleTapeTM).State :=
    (inferInstance : Encodable (p.1.State × Foundations.Normalize.Ctrl))
  AlphabetLift.liftInstance Ext.hash Ext.rupee
    (pcpRed (Foundations.Normalize.normTM p.1.toSingleTapeTM) (Foundations.Normalize.encInput p.2))

/-- `haltToPcp` witnesses that the halting problem many-one reduces to PCP over the fixed
alphabet `Ext (Alpha ℕ Bool)`. Combines TM normalization, MPCP reduction, and alphabet
lifting. -/
theorem halt_reducesto_pcp_spec :
    HaltProblem ⪯ₘ[haltToPcp] (@DecisionProblem (Ext (Alpha ℕ Bool))) := by
  rintro ⟨tm, w⟩
  show Halts tm.toSingleTapeTM w ↔ _
  let _ := tm.stateEncodable
  let _ : Encodable (Foundations.Normalize.normTM tm.toSingleTapeTM).State :=
    (inferInstance : Encodable (tm.State × Foundations.Normalize.Ctrl))
  rw [Foundations.Normalize.halts_normTM_iff tm.toSingleTapeTM w,
    halt_iff_pcp (Foundations.Normalize.normTM tm.toSingleTapeTM) (Foundations.Normalize.encInput w)
      (Foundations.Normalize.normTM_noBlankWrites tm.toSingleTapeTM)
      (Foundations.Normalize.normTM_noLeftBoundary tm.toSingleTapeTM w),
    pcpRed_iff (Foundations.Normalize.normTM tm.toSingleTapeTM) (Foundations.Normalize.encInput w)]
  exact AlphabetLift.decisionProblem_lifts Ext.hash Ext.rupee
    (pcpRed (Foundations.Normalize.normTM tm.toSingleTapeTM) (Foundations.Normalize.encInput w))
    (by decide)

/-- The halting problem many-one reduces to PCP over the fixed alphabet `Ext (Alpha ℕ Bool)`. -/
def halt_reducesto_pcp :
    HaltProblem ⪯ₘ (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  ⟨haltToPcp, halt_reducesto_pcp_spec⟩

/-- PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)`. -/
theorem pcp_undecidable' :
    Undecidable (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  ⟨halt_reducesto_pcp⟩

/-- PCP is undecidable over any `DecidableEq`, `Nontrivial` alphabet. Obtained by transporting
  `pcp_undecidable` along `AlphabetLift.PCP_alphabet_lift`. -/
@[nolint unusedArguments]
theorem pcp_undecidable {α : Type} [DecidableEq α] [Nontrivial α] :
    Undecidable (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact undecidability_from_reducibility
    pcp_undecidable'
    (AlphabetLift.pcp_alphabet_lift b0 b1 hne)

end DiagonaLean.PCP.Reduction
