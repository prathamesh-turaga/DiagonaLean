/-
Copyright (c) 2026 Aalok Thakkar and Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar and Akhilesh Balaji
-/

import DiagonaLean.Halt.Compositions


variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding DiagonaLean.Halt.Compositions DiagonaLean.Halt.Helpers

@[expose] public section

namespace DiagonaLean.Halt.Undecidable

/-- `SingleTapeTM.TransitionRelation` is deterministic. -/
private lemma transitionRelation_det {tm : SingleTapeTM Bool}
    {a b c : tm.Cfg}
    (hab : tm.TransitionRelation a b) (hac : tm.TransitionRelation a c) :
    b = c := by grind

/-- Specialisation of the diamond to `SingleTapeTM` traces. -/
private lemma trace_diamond {tm : SingleTapeTM Bool}
    {a b c : tm.Cfg}
    (hab : Relation.ReflTransGen tm.TransitionRelation a b)
    (hac : Relation.ReflTransGen tm.TransitionRelation a c) :
    Relation.ReflTransGen tm.TransitionRelation b c ∨
    Relation.ReflTransGen tm.TransitionRelation c b :=
  reflTransGen_diamond (@transitionRelation_det _) hab hac

/-- The state space of `diagTM D`: either a state of `D` (in the
"simulating `D`" phase), or one of two post-`D` states. -/
private inductive DiagPost : Type
  | reading -- about to inspect the head symbol of `D`'s output
  | loop    -- looping forever
  deriving DecidableEq, Inhabited

private instance : Fintype DiagPost where
  elems := {DiagPost.reading, DiagPost.loop}
  complete := fun x => by cases x <;> decide

/-- The diagonal TM for a hypothetical decider `D`. Simulates `D`;
when `D` would halt, transitions to `reading`. From `reading`, halts
if head is anything other than `some true`, loops if head is `some true`. -/
private def diagTM (D : SingleTapeTM Bool) : SingleTapeTM Bool where
  State := D.State ⊕ DiagPost
  q₀ := .inl D.q₀
  tr q sym :=
    match q with
    | .inl q' =>
      let (stmt, next) := D.tr q' sym
      match next with
      | some q'' => (stmt, some (.inl q''))
      | none => (stmt, some (.inr .reading))  -- D would halt → reading
    | .inr .reading =>
      match sym with
      | some true => (⟨none, none⟩, some (.inr .loop))
      | _ => (⟨none, none⟩, none)  -- halt (some false or blank)
    | .inr .loop => (⟨none, none⟩, some (.inr .loop))

variable (D : SingleTapeTM Bool)

/-- Lift a `D`-cfg into a `diagTM`-cfg. The `D`-halt cfg `⟨none, t⟩`
maps to `⟨some (.inr .reading), t⟩`. -/
private def liftCfg : D.Cfg → (diagTM D).Cfg
  | ⟨some q, t⟩ => ⟨some (.inl q), t⟩
  | ⟨none, t⟩   => ⟨some (.inr .reading), t⟩

@[simp]
private lemma liftCfg_initCfg (w : List Bool) :
    liftCfg D (SingleTapeTM.initCfg D w) =
      SingleTapeTM.initCfg (diagTM D) w := rfl

@[simp]
private lemma liftCfg_haltCfg (out : List Bool) :
    liftCfg D (SingleTapeTM.haltCfg D out) =
      ⟨some (.inr .reading), BiTape.mk₁ out⟩ := rfl

/-- One `D`-step lifts to one `diagTM`-step. -/
private lemma step_liftCfg
    {a b : D.Cfg} (h_ab : D.TransitionRelation a b) :
    (diagTM D).TransitionRelation (liftCfg D a) (liftCfg D b) := by
  obtain ⟨st_a, t_a⟩ := a
  cases st_a with
  | none => simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h_ab
  | some q =>
    generalize h_tr : D.tr q t_a.head = res
    obtain ⟨⟨wr, dir⟩, next⟩ := res
    have h_step_D : D.step ⟨some q, t_a⟩ =
        some ⟨next, (t_a.write wr).optionMove dir⟩ := by
      simp only [SingleTapeTM.step, h_tr]
    simp only [SingleTapeTM.TransitionRelation] at h_ab
    rw [h_step_D, Option.some_inj] at h_ab
    subst h_ab
    show (diagTM D).step ⟨some (.inl q), t_a⟩ =
      some (liftCfg D ⟨next, (t_a.write wr).optionMove dir⟩)
    cases next with
    | none =>
      show (diagTM D).step ⟨some (.inl q), t_a⟩ =
        some ⟨some (.inr DiagPost.reading), (t_a.write wr).optionMove dir⟩
      simp only [SingleTapeTM.step, diagTM, h_tr]
    | some q' =>
      show (diagTM D).step ⟨some (.inl q), t_a⟩ =
        some ⟨some (.inl q'), (t_a.write wr).optionMove dir⟩
      simp only [SingleTapeTM.step, diagTM, h_tr]

/-- `D`-traces lift to `diagTM`-traces. -/
private lemma trace_liftCfg {a b : D.Cfg}
    (h : Relation.ReflTransGen D.TransitionRelation a b) :
    Relation.ReflTransGen (diagTM D).TransitionRelation
      (liftCfg D a) (liftCfg D b) :=
  Relation.ReflTransGen.lift (liftCfg D) (fun _ _ => step_liftCfg D) _ _ h

/-! ## Behaviour of `diagTM` in the post-`D` phase -/

/-- One step from `reading` with head `some true` enters `loop`. -/
private lemma diagTM_reading_true (t : BiTape Bool)
    (h_head : t.head = some true) :
    (diagTM D).step ⟨some (.inr .reading), t⟩ =
      some ⟨some (.inr .loop), t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  cases h_head
  rfl

/-- One step from `reading` with head `some false` halts. -/
private lemma diagTM_reading_false (t : BiTape Bool)
    (h_head : t.head = some false) :
    (diagTM D).step ⟨some (.inr .reading), t⟩ =
      some ⟨none, t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  cases h_head
  rfl

/-- One step from `loop` stays in `loop`. -/
private lemma diagTM_loop_step (t : BiTape Bool) :
    (diagTM D).step ⟨some (.inr .loop), t⟩ =
      some ⟨some (.inr .loop), t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  rfl

/-- The `loop` state is closed under stepping. -/
private lemma loop_closed
    {a b : (diagTM D).Cfg}
    (h_loop : a.state = some (.inr .loop))
    (h_step : (diagTM D).TransitionRelation a b) :
    b.state = some (.inr .loop) := by
  obtain ⟨st_a, t_a⟩ := a
  have h := diagTM_loop_step D t_a
  grind

/-- From `loop`, every reachable cfg is in `loop`. -/
private lemma loop_persistent
    {a b : (diagTM D).Cfg}
    (h_loop : a.state = some (.inr .loop))
    (h_reach : Relation.ReflTransGen (diagTM D).TransitionRelation a b) :
    b.state = some (.inr .loop) := by
  induction h_reach with
  | refl => exact h_loop
  | tail _ h_step ih => exact loop_closed D ih h_step

/-! ## Behavior on `Outputs D w [false]` and `Outputs D w [true]` -/

/-- If `D` outputs `[false]` on `w`, then `diagTM D` halts on `w`. -/
private lemma diagTM_halts_of_outputs_false
    {w : List Bool}
    (h : SingleTapeTM.Outputs D w [false]) :
    Halts (diagTM D) w := by
  -- Lift D's trace to diagTM.
  have h_lift := trace_liftCfg D h
  rw [liftCfg_initCfg, liftCfg_haltCfg] at h_lift
  -- One more step: ⟨some (.inr .reading), mk₁ [false]⟩ → ⟨none, _⟩
  have h_step : (diagTM D).TransitionRelation
      ⟨some (.inr .reading), BiTape.mk₁ [false]⟩
      ⟨none, (BiTape.mk₁ [false]).write none⟩ := by
    show (diagTM D).step _ = some _
    apply diagTM_reading_false
    rfl
  exact ⟨_, h_lift.tail h_step⟩

/-- If `D` outputs `[true]` on `w`, then `diagTM D` does *not* halt
on `w`. -/
private lemma diagTM_loops_of_outputs_true
    {w : List Bool}
    (h : SingleTapeTM.Outputs D w [true]) :
    ¬ Halts (diagTM D) w := by
  rintro ⟨tape_halt, h_halt⟩
  -- Lift D's trace to diagTM, ending at ⟨some (.inr .reading), mk₁ [true]⟩.
  have h_lift := trace_liftCfg D h
  rw [liftCfg_initCfg, liftCfg_haltCfg] at h_lift
  -- One more step lands in `.loop`.
  have h_step : (diagTM D).TransitionRelation
      ⟨some (.inr .reading), BiTape.mk₁ [true]⟩
      ⟨some (.inr .loop), (BiTape.mk₁ [true]).write none⟩ := by
    show (diagTM D).step _ = some _
    apply diagTM_reading_true
    rfl
  have h_loop_reach : Relation.ReflTransGen (diagTM D).TransitionRelation
      (SingleTapeTM.initCfg (diagTM D) w)
      ⟨some (.inr .loop), (BiTape.mk₁ [true]).write none⟩ :=
    h_lift.tail h_step
  -- By deterministic diamond: ⟨some (.inr .loop), _⟩ →* ⟨none, tape_halt⟩
  -- (since the reverse is impossible from a halt cfg).
  rcases trace_diamond h_loop_reach h_halt with h_loop_to_halt | h_halt_to_loop
  · -- From `.loop`, every reachable cfg is in `.loop`. But the destination
    -- has state `none`. Contradiction.
    have := loop_persistent D rfl h_loop_to_halt
    simp at this
  · -- ⟨none, tape_halt⟩ →* ⟨some (.inr .loop), _⟩. Impossible.
    rcases h_halt_to_loop.cases_head with h_eq | ⟨c, h_step', _⟩
    · -- ⟨none, tape_halt⟩ = ⟨some (.inr .loop), _⟩. Contradicts state mismatch.
      simp at h_eq
    · simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h_step'

/-- **The Self-Halting Problem is undecidable**: no `SingleTapeTM Bool` can
decide the self-halt problem `K`. -/
theorem self_halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D := by
  rintro ⟨D, h_dec⟩
  haveI : DecidableEq D.State := Classical.decEq _
  let c_diag := diagTM D
  haveI : DecidableEq c_diag.State := by show DecidableEq (D.State ⊕ DiagPost); exact inferInstance
  obtain ⟨h_pos, h_neg⟩ := h_dec c_diag
  by_cases h_halts : Halts c_diag (encodeBoolTM c_diag)
  · -- D outputs [true] on `encodeBoolTM c_diag`.
    have h_out_true := h_pos h_halts
    have h_diag_halts : Halts (diagTM D) (encodeBoolTM c_diag) := by grind
    exact diagTM_loops_of_outputs_true D h_out_true h_diag_halts
  · -- D outputs [false] on `encodeBoolTM c_diag`.
    have h_out_false := h_neg h_halts
    have h_diag_halts := diagTM_halts_of_outputs_false D h_out_false
    exact h_halts h_diag_halts

lemma self_halt_decider_if_halt_decider {D} (h : IsHaltDecider D) : ∃ D' :
    SingleTapeTM Bool, IsSelfHaltDecider D' := -- sorry
  ⟨compComputer pairSelfTM D, fun M => by
    haveI : DecidableEq M.State := Classical.decEq _
    intro _
    obtain ⟨h_pos, h_neg⟩ := h M (encodeBoolTM M)
    constructor
    · intro hM
      exact compComputer_seq_outputs (pairSelfTM_outputs _) (h_pos hM)
    · intro hM
      exact compComputer_seq_outputs (pairSelfTM_outputs _) (h_neg hM)⟩

/-- **The Halting Problem is undecidable**: no `SingleTapeTM Bool` can
decide the self-halt problem `K`. -/
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsHaltDecider D := by
  rintro ⟨D, h_dec⟩
  exact self_halt_undecidable (self_halt_decider_if_halt_decider h_dec)

end DiagonaLean.Halt.Undecidable
