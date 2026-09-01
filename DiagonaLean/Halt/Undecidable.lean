/-
Copyright (c) 2026 Aalok Thakkar and Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Akhilesh Balaji
-/

import DiagonaLean.Halt.Compositions
import DiagonaLean.Synthetic.Definitions

/-! # Undecidability of the Halting Problem

The main results are `self_halt_undecidable` and `halt_undecidable`, proved by diagonalization.
`diagTM D` simulates `D` and inverts its output: if `D` says the input halts, `diagTM D` loops;
if `D` says it does not halt, `diagTM D` halts. Running `diagTM D` on its own encoding yields
a contradiction in either case.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding
     DiagonaLean.Halt.Compositions DiagonaLean.Halt.Helpers

@[expose] public section

namespace DiagonaLean.Halt.Undecidable

/-- The transition relation of any `SingleTapeTM Bool` is deterministic. -/
private lemma transitionRelation_det {tm : SingleTapeTM Bool}
    {a b c : tm.Cfg}
    (hab : tm.TransitionRelation a b) (hac : tm.TransitionRelation a c) :
    b = c := by grind

/-- Any two traces from a common source in a `SingleTapeTM Bool` are comparable. -/
private lemma trace_diamond {tm : SingleTapeTM Bool}
    {a b c : tm.Cfg}
    (hab : Relation.ReflTransGen tm.TransitionRelation a b)
    (hac : Relation.ReflTransGen tm.TransitionRelation a c) :
    Relation.ReflTransGen tm.TransitionRelation b c ∨
    Relation.ReflTransGen tm.TransitionRelation c b :=
  reflTransGen_diamond (@transitionRelation_det _) hab hac

/-- Post-`D` states of `diagTM D`: `reading` inspects the head of `D`'s output tape;
`loop` runs forever. -/
private inductive DiagPost : Type
  | reading
  | loop
  deriving DecidableEq, Inhabited

private instance : Fintype DiagPost where
  elems := {DiagPost.reading, DiagPost.loop}
  complete := fun x => by cases x <;> decide

/-- The diagonal TM for a hypothetical decider `D`. Simulates `D` in `.inl` states;
when `D` halts, enters `reading`. From `reading`, halts on any head symbol other than
`some true`, and loops forever on `some true`. -/
private def diagTM (D : SingleTapeTM Bool) : SingleTapeTM Bool where
  State := D.State ⊕ DiagPost
  q₀ := .inl D.q₀
  tr q sym :=
    match q with
    | .inl q' =>
      let (stmt, next) := D.tr q' sym
      match next with
      | some q'' => (stmt, some (.inl q''))
      | none => (stmt, some (.inr .reading))
    | .inr .reading =>
      match sym with
      | some true => (⟨none, none⟩, some (.inr .loop))
      | _ => (⟨none, none⟩, none)
    | .inr .loop => (⟨none, none⟩, some (.inr .loop))

variable (D : SingleTapeTM Bool)

/-- Projects a `D`-configuration into a `diagTM D`-configuration, mapping a halted
`D`-configuration to `⟨some (.inr .reading), t⟩`. -/
private def liftCfg : D.Cfg → (diagTM D).Cfg
  | ⟨some q, t⟩ => ⟨some (.inl q), t⟩
  | ⟨none, t⟩   => ⟨some (.inr .reading), t⟩

/-- `liftCfg` maps the initial configuration of `D` on `w` to the initial configuration
of `diagTM D` on `w`. -/
@[simp]
private lemma liftCfg_initCfg (w : List Bool) :
    liftCfg D (SingleTapeTM.initCfg D w) =
      SingleTapeTM.initCfg (diagTM D) w := rfl

/-- `liftCfg` maps the halting configuration of `D` with output `out` to the `reading`
state of `diagTM D` with tape `mk₁ out`. -/
@[simp]
private lemma liftCfg_haltCfg (out : List Bool) :
    liftCfg D (SingleTapeTM.haltCfg D out) =
      ⟨some (.inr .reading), BiTape.mk₁ out⟩ := rfl

/-- A single `D`-step lifts to a single `diagTM D`-step. -/
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

/-- A `D`-trace lifts to a `diagTM D`-trace via `liftCfg`. -/
private lemma trace_liftCfg {a b : D.Cfg}
    (h : Relation.ReflTransGen D.TransitionRelation a b) :
    Relation.ReflTransGen (diagTM D).TransitionRelation
      (liftCfg D a) (liftCfg D b) :=
  Relation.ReflTransGen.lift (liftCfg D) (fun _ _ => step_liftCfg D) _ _ h

/-- From `reading` with head `some true`, the next state is `loop`. -/
private lemma diagTM_reading_true (t : BiTape Bool)
    (h_head : t.head = some true) :
    (diagTM D).step ⟨some (.inr .reading), t⟩ =
      some ⟨some (.inr .loop), t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  cases h_head; rfl

/-- From `reading` with head `some false`, the machine halts. -/
private lemma diagTM_reading_false (t : BiTape Bool)
    (h_head : t.head = some false) :
    (diagTM D).step ⟨some (.inr .reading), t⟩ =
      some ⟨none, t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t
  cases h_head; rfl

/-- From `loop`, the machine steps back to `loop`. -/
private lemma diagTM_loop_step (t : BiTape Bool) :
    (diagTM D).step ⟨some (.inr .loop), t⟩ =
      some ⟨some (.inr .loop), t.write none⟩ := by
  obtain ⟨h, l, r⟩ := t; rfl

/-- A single step from a `loop` configuration produces another `loop` configuration. -/
private lemma loop_closed
    {a b : (diagTM D).Cfg}
    (h_loop : a.state = some (.inr .loop))
    (h_step : (diagTM D).TransitionRelation a b) :
    b.state = some (.inr .loop) := by
  obtain ⟨st_a, t_a⟩ := a
  have h := diagTM_loop_step D t_a
  grind

/-- Every configuration reachable from a `loop` configuration is also in `loop`. -/
private lemma loop_persistent
    {a b : (diagTM D).Cfg}
    (h_loop : a.state = some (.inr .loop))
    (h_reach : Relation.ReflTransGen (diagTM D).TransitionRelation a b) :
    b.state = some (.inr .loop) := by
  induction h_reach with
  | refl => exact h_loop
  | tail _ h_step ih => exact loop_closed D ih h_step

/-- If `D` outputs `[false]` on `w`, then `diagTM D` halts on `w`. -/
private lemma diagTM_halts_of_outputs_false
    {w : List Bool}
    (h : SingleTapeTM.Outputs D w [false]) :
    Halts (diagTM D) w := by
  have h_lift := trace_liftCfg D h
  rw [liftCfg_initCfg, liftCfg_haltCfg] at h_lift
  have h_step : (diagTM D).TransitionRelation
      ⟨some (.inr .reading), BiTape.mk₁ [false]⟩
      ⟨none, (BiTape.mk₁ [false]).write none⟩ := by
    show (diagTM D).step _ = some _
    apply diagTM_reading_false; rfl
  exact ⟨_, h_lift.tail h_step⟩

/-- If `D` outputs `[true]` on `w`, then `diagTM D` does not halt on `w`. -/
private lemma diagTM_loops_of_outputs_true
    {w : List Bool}
    (h : SingleTapeTM.Outputs D w [true]) :
    ¬ Halts (diagTM D) w := by
  rintro ⟨tape_halt, h_halt⟩
  have h_lift := trace_liftCfg D h
  rw [liftCfg_initCfg, liftCfg_haltCfg] at h_lift
  have h_step : (diagTM D).TransitionRelation
      ⟨some (.inr .reading), BiTape.mk₁ [true]⟩
      ⟨some (.inr .loop), (BiTape.mk₁ [true]).write none⟩ := by
    show (diagTM D).step _ = some _
    apply diagTM_reading_true; rfl
  have h_loop_reach : Relation.ReflTransGen (diagTM D).TransitionRelation
      (SingleTapeTM.initCfg (diagTM D) w)
      ⟨some (.inr .loop), (BiTape.mk₁ [true]).write none⟩ :=
    h_lift.tail h_step
  rcases trace_diamond h_loop_reach h_halt with h_loop_to_halt | h_halt_to_loop
  · have := loop_persistent D rfl h_loop_to_halt
    simp at this
  · rcases h_halt_to_loop.cases_head with h_eq | ⟨c, h_step', _⟩
    · simp at h_eq
    · simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h_step'

/-- No `SingleTapeTM Bool` decides the self-halting problem. -/
theorem self_halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D := by
  rintro ⟨D, h_dec⟩
  have : Encodable D.State := Fintype.toEncodable D.State
  have : Encodable DiagPost := Fintype.toEncodable DiagPost
  let c_diag := diagTM D
  have : Encodable c_diag.State := by
    show Encodable (D.State ⊕ DiagPost); exact inferInstance
  obtain ⟨h_pos, h_neg⟩ := h_dec c_diag
  by_cases h_halts : Halts c_diag (encodeBoolTM c_diag)
  · exact diagTM_loops_of_outputs_true D (h_pos h_halts) (by grind)
  · exact h_halts (diagTM_halts_of_outputs_false D (h_neg h_halts))

/-- A general halt decider for all `(M, w)` yields a self-halt decider by composing with
`pairSelfTM`, which maps `encodeBoolTM M` to `encodePair (encodeBoolTM M) (encodeBoolTM M)`. -/
lemma self_halt_decider_if_halt_decider {D} (h : IsHaltDecider D) :
    ∃ D' : SingleTapeTM Bool, IsSelfHaltDecider D' :=
  ⟨compComputer pairSelfTM D, fun M => by
    have : Encodable M.State := Fintype.toEncodable M.State
    intro _
    obtain ⟨h_pos, h_neg⟩ := h M (encodeBoolTM M)
    constructor
    · intro hM
      exact compComputer_seq_outputs (pairSelfTM_outputs _) (h_pos hM)
    · intro hM
      exact compComputer_seq_outputs (pairSelfTM_outputs _) (h_neg hM)⟩

/-- No `SingleTapeTM Bool` decides the halting problem. -/
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsHaltDecider D := by
  rintro ⟨D, h_dec⟩
  exact self_halt_undecidable (self_halt_decider_if_halt_decider h_dec)

/-- `DTrue` is a single-tape Turing machine over `Bool` that scans right across
non-blank tape symbols until it reaches the first blank (`none`), writes `true`,
and halts. -/
def DTrue : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ a :=
    match a with
    | some _ => (⟨none, some Turing.Dir.right⟩, some ())
    | none   => (⟨some true, none⟩, none)

/-- One step of `DTrue` on `h :: t` lands exactly on the initial configuration for `t`. -/
private lemma DTrue_step_tail (h : Bool) (t : List Bool) :
    DTrue.TransitionRelation (SingleTapeTM.initCfg DTrue (h :: t))
      (SingleTapeTM.initCfg DTrue t) :=
  by
  show DTrue.step _ = some _
  simp only [SingleTapeTM.step, SingleTapeTM.initCfg, DTrue, BiTape.mk₁,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight,
    StackTape.cons, StackTape.mapSome, StackTape.head, StackTape.tail]
  cases t with
  | nil => exact Option.some_inj.mpr rfl
  | cons h' t' => exact Option.some_inj.mpr rfl

/-- `DTrue` halts on every input, erasing the tape and writing `[true]`. -/
theorem DTrue_outputs (l : List Bool) : SingleTapeTM.Outputs DTrue l [true] := by
  induction l with
  | nil =>
    exact Relation.ReflTransGen.single rfl
  | cons h t ih =>
    exact Relation.ReflTransGen.head (DTrue_step_tail h t) ih

--Final step of halting problem which asserts existence of a turning Machine which does not satisfy Halting
theorem exists_not_halts : ∃ (tm : SingleTapeTM Bool) (w : List Bool), ¬ Halts tm w := by
  by_contra h
  apply halt_undecidable
  simp at h
  refine ⟨DTrue, fun tm _ w => ⟨fun _ => DTrue_outputs _, fun hc => absurd (h tm w) hc⟩⟩

open DiagonaLean.Synthetic.Definitions

/-- The pair-encoding used by `IsHaltDecider`, packaged as a plain function of the encoding's
domain so `HaltProblem` can be phrased as an instance of `MachineDecidable`. Uses the `Encodable`
instance bundled with `p.1 : EncodableTM Bool` (its `stateEncodable` field) rather than a
classically chosen one, since `Encodable` witnesses are data -- unlike `DecidableEq`, they are
not subsingletons, so which instance is used matters and must be threaded explicitly. -/
noncomputable def haltInputEncoding (p : EncodableTM Bool × List Bool) : List Bool :=
  letI := p.1.stateEncodable
  encodePair (encodeBoolTM p.1.toSingleTapeTM) p.2

/-- `IsHaltDecider D` is exactly `D` deciding `HaltProblem` under `haltInputEncoding`. Since
`IsHaltDecider` quantifies over an arbitrary `[Encodable tm.State]` instance for each `tm`, both
directions can simply instantiate that instance argument with whichever `Encodable` witness the
other side already uses (`p.1.stateEncodable` / `tm.stateEncodable`), with no need to reconcile
mismatched instances as the old `DecidableEq`-based proof did via `Subsingleton.elim`. -/
theorem tmdeciderfor_halt_iff (D : SingleTapeTM Bool) :
    TMDeciderFor D haltInputEncoding HaltProblem ↔ IsHaltDecider D := by
  constructor
  · intro h tm inst w
    have h' := h (⟨⟨tm, inst⟩, w⟩)
    unfold haltInputEncoding at h'
    exact h'
  · rintro h ⟨tm, w⟩
    have h' := @h tm.toSingleTapeTM tm.stateEncodable w
    unfold haltInputEncoding
    exact h'

/-- The halting problem is not machine-decidable: no `SingleTapeTM Bool` decides `HaltProblem`
under `haltInputEncoding`. This connects `halt_undecidable`'s diagonalization argument to the
general, non-vacuous `MachineDecidable` notion (unlike `SDecidable`, which holds classically for
every predicate regardless of computability). -/
theorem halt_not_machinedecidable : ¬ MachineDecidable haltInputEncoding HaltProblem := by
  rintro ⟨D, hD⟩
  exact halt_undecidable ⟨D, (tmdeciderfor_halt_iff D).mp hD⟩

variable {X Y : Type*}

/-- `R` computes the reduction `f` at the level of encodings: on `enc1 x`, `R` halts with
output `enc2 (f x)`. -/
def ComputesReduction (R : SingleTapeTM Bool)
    (enc1 : X → List Bool) (enc2 : Y → List Bool) (f : X → Y) : Prop :=
  ∀ x, SingleTapeTM.Outputs R (enc1 x) (enc2 (f x))

/-- If a TM `R` computes a many-one reduction `f : P ⪯ₘ[f] Q` at the level of encodings, then
a machine decider for `Q` yields one for `P`: preprocess the input with `R`, then run the
`Q`-decider. This is the general shape of `self_halt_decider_if_halt_decider` (there,
`R = pairSelfTM`), stated for an arbitrary computable reduction rather than that one instance. -/
theorem machineDecidable_of_computes_reduction
    {enc1 : X → List Bool} {enc2 : Y → List Bool} {P : X → Prop} {Q : Y → Prop}
    {R : SingleTapeTM Bool} {f : X → Y}
    (hR : ComputesReduction R enc1 enc2 f) (hf : P ⪯ₘ[f] Q)
    (hQ : MachineDecidable enc2 Q) :
    MachineDecidable enc1 P := by
  obtain ⟨D, hD⟩ := hQ
  refine ⟨compComputer R D, fun x => ?_⟩
  obtain ⟨hpos, hneg⟩ := hD (f x)
  exact ⟨fun hPx => compComputer_seq_outputs (hR x) (hpos ((hf x).mp hPx)),
         fun hnPx => compComputer_seq_outputs (hR x)
           (hneg (fun hQfx => hnPx ((hf x).mpr hQfx)))⟩

/-- Contrapositive of `machineDecidable_of_computes_reduction`: undecidability transports
*forward* along a computable reduction. If `P` has no machine decider and `R` computes
`f : P ⪯ₘ[f] Q`, then `Q` has none either -- a decider for `Q` would, via `R`, yield one for
`P`. -/
theorem not_machineDecidable_of_computes_reduction
    {enc1 : X → List Bool} {enc2 : Y → List Bool} {P : X → Prop} {Q : Y → Prop}
    {R : SingleTapeTM Bool} {f : X → Y}
    (hR : ComputesReduction R enc1 enc2 f) (hf : P ⪯ₘ[f] Q)
    (hP : ¬ MachineDecidable enc1 P) :
    ¬ MachineDecidable enc2 Q :=
  fun hQ => hP (machineDecidable_of_computes_reduction hR hf hQ)

end DiagonaLean.Halt.Undecidable
