/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
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
`NoBlankWrites`/`NoLeftBoundary` side conditions by simulating an arbitrary TM by a
normalised one; `AlphabetLift` transports the resulting instance from the alphabet the
normalisation produces (`Ext (Alpha ℕ (Bool × Bool))`) back to the target alphabet. -/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
open DiagonaLean.PCP.AlphabetLift

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Apply `g : α → β` symbolwise to both sides of a PCP tile. -/
def Tile.map {α β : Type} (g : α → β) (t : Tile α) : Tile β :=
  ⟨t.top.map g, t.bot.map g⟩

variable {α β : Type} (s : Stack α) (f : Tile α → Tile β)

theorem τ1_map {α β : Type} (g : α → β) (l : List (Tile α)) :
    τ1 (l.map (Tile.map g)) = (τ1 l).map g := by
  induction l with
  |nil => simp
  |cons l ls ih =>
    simp_all[List.map, Tile.map]

theorem τ2_map {α β : Type} (g : α → β) (l : List (Tile α)) :
    τ2 (l.map (Tile.map g)) = (τ2 l).map g := by
  induction l with
  |nil => simp
  |cons l ls ih =>
    simp_all[List.map, Tile.map]

theorem exists_ls (l : Stack β) (g: α → β) (S: Stack α) (h : ∀ t ∈ l, ∃ a ∈ S, Tile.map g a = t) :
    ∃ ls : Stack α, ls.map (Tile.map g) = l  ∧ (∀ t ∈ ls, t ∈ S):= by
  choose fn hfn using h
  exact ⟨l.attach.map (fun ⟨t, ht⟩ => fn t ht), by
    rw [List.map_map]
    simp [hfn]
    refine fun t x x_1 h => ?_
    grind
    ⟩

theorem DecisionProblem_map_iff {α β : Type} (g : α → β) (hg : Function.Injective g)
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
          rw[hg]
          rw[τ1_map, τ2_map]
          simp_all
      · rintro ⟨l, hne, heq⟩
        simp_all
        unfold DecisionProblem
        have exists_l':   ∃ ls : Stack α, ls.map (Tile.map g) = l ∧ (∀t ∈ ls, t ∈ S) := by apply exists_ls l g S heq.left
        obtain ⟨ls, hls, hS⟩ := exists_l'
        use ls
        refine ⟨?_, ?_, ?_⟩
        grind
        exact hS
        simp[←hls] at heq
        simp[τ1_map, τ2_map] at heq
        obtain ⟨heql, heqr⟩ := heq
        exact (List.map_inj_right hg).mp heqr


theorem halt_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) [Encodable Symbol] [Encodable tm.State]:
    Halts tm w ↔
    PCP.DecisionProblem (mpcpToPcp (startTile tm w) (haltTiles tm)) :=
  (halt_iff_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)


open Synthetic.Notation

def Alpha.map {Q Q' S : Type} (g : Q → Q') : Alpha Q S → Alpha Q' S
  | .tape s  => .tape s
  | .state q => .state (g q)
  | .halt    => .halt
  | .sep     => .sep


theorem Alpha.map_injective {Q Q' S : Type} {g : Q → Q'} (hg : Function.Injective g) :
    Function.Injective (Alpha.map g : Alpha Q S → Alpha Q' S) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [Alpha.map]
  exact hg hxy

def Ext.map {α β : Type} (g : α → β) : Ext α → Ext β
  | .sym a  => .sym (g a)
  | .hash   => .hash
  | .rupee  => .rupee

theorem Ext.map_injective {α β : Type} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (Ext.map g) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [Ext.map]
  exact hg hxy

def pcpRed (tm : SingleTapeTM Symbol) (w : List Symbol)
    [Encodable Symbol] [Encodable tm.State] : Stack (Ext (Alpha ℕ Symbol)) :=
  (mpcpToPcp (startTile tm w) (haltTiles tm)).map
    (Tile.map (Ext.map (Alpha.map Encodable.encode)))




theorem pcpRed_iff (tm : SingleTapeTM Symbol) (w : List Symbol)
    [Encodable Symbol] [Encodable tm.State] :
    PCP.DecisionProblem (mpcpToPcp (startTile tm w) (haltTiles tm)) ↔
    PCP.DecisionProblem (pcpRed tm w) :=
  DecisionProblem_map_iff (Ext.map (Alpha.map Encodable.encode))
    (Ext.map_injective (Alpha.map_injective Encodable.encode_injective))
    (mpcpToPcp (startTile tm w) (haltTiles tm))



variable (α : Type*) [Fintype α]

/-- Every `SingleTapeTM.State` is encodable via its bundled `Fintype` instance. Kept
generic in the tape alphabet `Symbol` so it covers the `SingleTapeTM (Bool × Bool)` produced
by `Foundations.Normalize.normalize_tm`, not just `SingleTapeTM Bool`. -/
noncomputable instance (tm : SingleTapeTM Symbol) : Encodable tm.State :=
  Encodable.ofEquiv (Fin (Fintype.card tm.State)) (Fintype.equivFin tm.State)

noncomputable def enumerate {α : Type} [Fintype α] : α ≃ Fin (Fintype.card α) :=
  Fintype.equivFin α

/-- The halting problem many-one reduces to PCP over the fixed alphabet
`Ext (Alpha ℕ Bool)`. `pcpRed tm w` only agrees with `Halts tm w` under the side conditions
`NoBlankWrites tm` and `NoLeftBoundary tm w`, which an arbitrary `tm : SingleTapeTM Bool`
need not satisfy. `Normalize.normalize_tm` supplies, for every `(tm, w)`, a normalized
`(tm', w') : SingleTapeTM (Bool × Bool) × List (Bool × Bool)` that does satisfy them and
halts iff `tm` does; this shifts the tape alphabet from `Bool` to `Bool × Bool`, so
`pcpRed tm' w'` lands in `Stack (Ext (Alpha ℕ (Bool × Bool)))`. `AlphabetLift.PCP_alphabet_lift`
closes that last gap, transporting `DecisionProblem` back to the `Bool`-alphabet target via
the distinct elements `Ext.hash ≠ Ext.rupee`. -/
theorem PCP_reduces :
    Synthetic.Notation.HALT ⪯ₘ (@DecisionProblem (Ext (Alpha ℕ Bool))) := by
  have hex : ∀ p : SingleTapeTM Bool × List Bool,
      ∃ (tm' : SingleTapeTM (Bool × Bool)) (w' : List (Bool × Bool)),
        NoBlankWrites tm' ∧ NoLeftBoundary tm' w' ∧ (Halts p.1 p.2 ↔ Halts tm' w') :=
    fun p => Foundations.Normalize.normalize_tm p.1 p.2
  choose tm' w' h_nbw h_nlb h_iff using hex
  refine ⟨fun p => AlphabetLift.liftInstance Ext.hash Ext.rupee (pcpRed (tm' p) (w' p)), ?_⟩
  rintro ⟨tm, w⟩
  show Halts tm w ↔ _
  rw [h_iff (tm, w), halt_iff_pcp (tm' (tm, w)) (w' (tm, w)) (h_nbw (tm, w)) (h_nlb (tm, w)),
    pcpRed_iff (tm' (tm, w)) (w' (tm, w))]
  exact AlphabetLift.decisionProblem_lifts Ext.hash Ext.rupee (pcpRed (tm' (tm, w)) (w' (tm, w)))
    (by decide)

theorem PCP_undecidable {α : Type} [DecidableEq α] {b0 b1 : α} (_hne : b0 ≠ b1) :
    Undecidable (@DecisionProblem (Ext (Alpha ℕ Bool))) := by
    unfold Undecidable HALT
    apply PCP_reduces

/-- PCP is undecidable over any `DecidableEq`, `Nontrivial` alphabet. Obtained by
transporting `PCP_undecidable` (fixed to `Ext (Alpha ℕ Bool)`) along `AlphabetLift.PCP_alphabet_lift`,
which reduces PCP over any alphabet to PCP over any target with two distinct elements. -/
theorem PCP_undecidable_Gen {α : Type} [DecidableEq α] [Nontrivial α] :
    Undecidable (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact undecidability_from_reducibility
    (PCP_undecidable (α := Bool) (b0 := true) (b1 := false) (by decide))
    (AlphabetLift.PCP_alphabet_lift b0 b1 hne)

end DiagonaLean.PCP.Reduction
