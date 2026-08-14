import Mathlib.Logic.Relation
import DiagonaLean.Halt.Basic

/-! # Helpers for Deterministic Transition Relations

Auxiliary lemmas about `Relation.ReflTransGen` used in the halting problem proof.
-/
open Cslib.Turing SingleTapeTM

namespace DiagonaLean.Halt.Helpers

/-- For a deterministic relation, any two paths from a common source are comparable:
one is a prefix of the other. -/
lemma reflTransGen_diamond {α : Type*} {r : α → α → Prop}
    (h_det : ∀ {a b c : α}, r a b → r a c → b = c) {a b c : α}
    (hab : Relation.ReflTransGen r a b)
    (hac : Relation.ReflTransGen r a c) :
    Relation.ReflTransGen r b c ∨ Relation.ReflTransGen r c b := by
  induction hab with
  | refl => grind
  | @tail b_int b_end h_rest h_step ih =>
    cases ih with
    | inr h_c_b_int => grind
    | inl h_b_int_c =>
      rcases h_b_int_c.cases_head with h_eq | ⟨x, h_b_int_x, h_x_c⟩ <;> grind

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A halted configuration has no successor configuration. -/
lemma not_transitionRelation_of_halted {tm : SingleTapeTM Symbol}
    {t : BiTape Symbol} {c : tm.Cfg} :
    ¬ tm.TransitionRelation (⟨none, t⟩ : tm.Cfg) c := by
  simp [SingleTapeTM.TransitionRelation]

/-- Nothing but a halted configuration itself is reachable from a halted configuration. -/
lemma eq_of_reflTransGen_halted {tm : SingleTapeTM Symbol}
    {t : BiTape Symbol} {c : tm.Cfg}
    (h : Relation.ReflTransGen tm.TransitionRelation ⟨none, t⟩ c) :
    c = ⟨none, t⟩ := by
  rcases h.cases_head with h | ⟨d, hstep, -⟩
  · exact h.symm
  · exact absurd hstep not_transitionRelation_of_halted

/-- The transition relation of a single-tape TM is deterministic. -/
lemma transitionRelation_deterministic {tm : SingleTapeTM Symbol} {a b c : tm.Cfg}
    (hab : tm.TransitionRelation a b) (hac : tm.TransitionRelation a c) : b = c := by
  grind
omit [Inhabited Symbol] [Fintype Symbol] in

/-- `BiTape.mk₁` is injective: distinct lists give distinct initial tapes. -/
lemma mk₁_injective : Function.Injective (BiTape.mk₁ : List Symbol → BiTape Symbol) := by
  intro l₁ l₂ h
  cases l₁ with
  | nil => cases l₂ with
    | nil => rfl
    | cons b t => simp [BiTape.mk₁, BiTape.nil] at h
  | cons a s => cases l₂ with
    | nil => simp [BiTape.mk₁, BiTape.nil] at h
    | cons b t =>
      simp only [BiTape.mk₁, BiTape.mk.injEq, Option.some.injEq] at h
      obtain ⟨hab, -, hst⟩ := h
      have hmap : (s.map some) = (t.map some) := congrArg StackTape.toList hst
      exact congrArg₂ List.cons hab
        (List.map_injective_iff.mpr (Option.some_injective Symbol) hmap)

/-- A single-tape TM produces at most one output on a given input. -/
theorem outputs_unique {tm : SingleTapeTM Symbol} {w v₁ v₂ : List Symbol}
    (h₁ : tm.Outputs w v₁) (h₂ : tm.Outputs w v₂) : v₁ = v₂ := by
  have hcfg : (tm.haltCfg v₁) = tm.haltCfg v₂ := by
    rcases reflTransGen_diamond (fun {_ _ _} => transitionRelation_deterministic) h₁ h₂ with h | h
    · exact (eq_of_reflTransGen_halted h).symm
    · exact eq_of_reflTransGen_halted h
  exact mk₁_injective (congrArg SingleTapeTM.Cfg.BiTape hcfg)

/-- A halting single-tape TM halts with a unique final tape. -/
theorem halt_tape_unique {tm : SingleTapeTM Symbol} {w : List Symbol}
    {t₁ t₂ : BiTape Symbol}
    (h₁ : Relation.ReflTransGen tm.TransitionRelation (tm.initCfg w) ⟨none, t₁⟩)
    (h₂ : Relation.ReflTransGen tm.TransitionRelation (tm.initCfg w) ⟨none, t₂⟩) :
    t₁ = t₂ := by
  rcases reflTransGen_diamond (fun {_ _ _} => transitionRelation_deterministic) h₁ h₂ with h | h
  · exact (congrArg SingleTapeTM.Cfg.BiTape (eq_of_reflTransGen_halted h)).symm
  · exact congrArg SingleTapeTM.Cfg.BiTape (eq_of_reflTransGen_halted h)

/-- If a machine outputs something on `w`, then it halts on `w`. -/
lemma halts_of_outputs {tm : SingleTapeTM Symbol} {w v : List Symbol}
    (h : tm.Outputs w v) : Halts tm w :=
  ⟨BiTape.mk₁ v, h⟩

/-- A machine that never halts: whatever it reads, it blanks the cell and stays in its single
  state. -/
def loopTM : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨none, none⟩, some ())
instance : DecidableEq loopTM.State := fun _ _ => isTrue rfl

/-- Every configuration reachable in `loopTM` is still in its (unique) state. -/
private lemma loopTM_state_persists {c d : loopTM.Cfg}
    (hc : c.state = some ())
    (h : Relation.ReflTransGen loopTM.TransitionRelation c d) :
    d.state = some () := by
  induction h with
  | refl => exact hc
  | @tail b e _ hstep ih =>
    obtain ⟨_ | q, t⟩ := b
    · simp [SingleTapeTM.TransitionRelation] at hstep
    · simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at hstep
      grind [loopTM]

/-- `loopTM` halts on no input. -/
theorem not_halts_loopTM (w : List Bool) : ¬ Halts loopTM w := by
  rintro ⟨t, h⟩
  have := loopTM_state_persists (c := loopTM.initCfg w) rfl h
  simp at this

/-- A machine that halts immediately, on every input. -/
def haltTM : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ x := (⟨x, none⟩, none)
instance : DecidableEq haltTM.State := fun _ _ => isTrue rfl

/-- `haltTM` halts on every input. -/
theorem halts_haltTM (w : List Bool) : Halts haltTM w :=
  ⟨BiTape.mk₁ w, Relation.ReflTransGen.single (by
    cases w <;> rfl)⟩

end DiagonaLean.Halt.Helpers
