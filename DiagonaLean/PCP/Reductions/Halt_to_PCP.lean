/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Halt.Normalize
import DiagonaLean.PCP.Reductions.AlphabetLift

/-! # Halt ⪯ₘ PCP

The composition `Halt ⪯ₘ MPCP ⪯ₘ PCP`, giving a direct equivalence between
halting of a TM `tm` on input `w` and solvability of the PCP instance
`mpcpToPcp (startTile tm w) (haltTiles tm)`.

The reduction is subject to two side conditions (`NoBlankWrites` and
`NoLeftBoundary`) which can be removed by a normalisation construction;
this is left to a future `PCP.Normalize` module.
-/


namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP.Reduction
     DiagonaLean.MPCP.Reduction DiagonaLean.Halt

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- `tm` halts on `w` iff the PCP instance `mpcpToPcp (startTile tm w) (haltTiles tm)`
has a solution, subject to `NoBlankWrites tm` and `NoLeftBoundary tm w`. -/
def Tile.map {α β : Type} (g : α → β) (t : Tile α) : Tile β :=
  ⟨t.top.map g, t.bot.map g⟩

variable {α β : Type} (s : Stack α) (f : Tile α → Tile β)

-- 1. Using .map directly on a Stack:
#check s.map f
-- Output: List (Tile β) (or Stack β)
#check τ1
#print τ1_nil
#print τ1_map_copyTile
#print Tile
#check List.map
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

-- Best inside a tactic block

theorem exists_ls (l : Stack β) (g: α → β) (S: Stack α) (h : ∀ t ∈ l, ∃ a ∈ S, Tile.map g a = t) :
    ∃ ls : Stack α, ls.map (Tile.map g) = l  ∧ (∀ t ∈ ls, t ∈ S):= by
  choose fn hfn using h
  exact ⟨l.attach.map (fun ⟨t, ht⟩ => fn t ht), by
    rw [List.map_map]
    simp [hfn]
    refine fun t x x_1 h => ?_
    grind
    ⟩

#print SingleTapeTM
#print NoLeftBoundary

-- `normalize_tm` now lives in `DiagonaLean.Normalize` (see `PCP_reduces` below,
-- which imports and uses it from there) — this used to be a local duplicate.

#print Stack

-- DecisionProblem
--  (mpcpToPcp (Tile.map (Alpha.map Encodable.encode) (startTile tm w))
--    (List.map (Tile.map (Alpha.map Encodable.encode)) (haltTiles tm)))

--g =  (Alpha.map Encodable.encode) (startTile tm w)
--S = (List.map (Tile.map (Alpha.map Encodable.encode)) (haltTiles tm)))

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
#check SingleTapeTM
#check DecisionProblem
#check Synthetic.Definitions.ManyOneReduces
#eval (1,5).2

def Alpha.map {Q Q' S : Type} (g : Q → Q') : Alpha Q S → Alpha Q' S
  | .tape s  => .tape s
  | .state q => .state (g q)
  | .halt    => .halt
  | .sep     => .sep

#check Stmt
#check StackTape
#print Ext

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


#check pcpRed
#check enumerate
#print enumerate

variable (α : Type*) [Fintype α]



-- Generic in `Symbol` (via the ambient `variable {Symbol : Type} [Inhabited Symbol]
-- [Fintype Symbol]`), not hardcoded to `Bool`: every `SingleTapeTM` bundles
-- `stateFintype : Fintype State`, so this construction works for any tape alphabet,
-- e.g. `SingleTapeTM (Bool × Bool)` from `normalize_tm`.
noncomputable instance (tm : SingleTapeTM Symbol) : Encodable tm.State :=
  Encodable.ofEquiv (Fin (Fintype.card tm.State)) (Fintype.equivFin tm.State)

noncomputable def enumerate {α : Type} [Fintype α] : α ≃ Fin (Fintype.card α) :=
  Fintype.equivFin α


-- `pcpRed tm w` only agrees with `Halts tm w` when `NoBlankWrites tm`/`NoLeftBoundary tm w`
-- hold (`halt_iff_pcp`'s side conditions), which an arbitrary `tm : SingleTapeTM Bool` need
-- not satisfy. `Normalize.normalize_tm` supplies, for every `(tm, w)`, a normalized
-- `(tm', w') : SingleTapeTM (Bool × Bool) × List (Bool × Bool)` that DOES satisfy them and
-- halts iff `tm` does — but that shifts the tape alphabet from `Bool` to `Bool × Bool`, so
-- `pcpRed tm' w'` lands in `Stack (Ext (Alpha ℕ (Bool × Bool)))`, not the `Bool`-alphabet
-- target this theorem is stated over. `AlphabetLift.PCP_alphabet_lift` closes that last gap,
-- transporting `DecisionProblem` from any `DecidableEq` alphabet to any alphabet with two
-- distinct elements (here `Ext.hash ≠ Ext.rupee` in the `Bool`-alphabet target).
theorem PCP_reduces :
    Synthetic.Notation.HALT ⪯ₘ (@DecisionProblem (Ext (Alpha ℕ Bool))) := by
  have hex : ∀ p : SingleTapeTM Bool × List Bool,
      ∃ (tm' : SingleTapeTM (Bool × Bool)) (w' : List (Bool × Bool)),
        NoBlankWrites tm' ∧ NoLeftBoundary tm' w' ∧ (Halts p.1 p.2 ↔ Halts tm' w') :=
    fun p => Normalize.normalize_tm p.1 p.2
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

-- `PCP_undecidable` already gives undecidability fixed to the `Ext (Alpha ℕ Bool)`
-- alphabet; `AlphabetLift.PCP_alphabet_lift` transports that to any alphabet `α`
-- with two distinct elements, which `Nontrivial α` supplies.
theorem PCP_undecidable_Gen {α : Type} [DecidableEq α] [Nontrivial α] :
    Undecidable (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact undecidability_from_reducibility
    (PCP_undecidable (α := Bool) (b0 := true) (b1 := false) (by decide))
    (AlphabetLift.PCP_alphabet_lift b0 b1 hne)

end DiagonaLean.PCP.Reduction
