/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Foundations.UniversalTuringMachine.Basic
import DiagonaLean.Halt.Helpers

/-! # Invariance of Universality Under Machine-Computable Re-Encodings

Universality (`DiagonaLean.Foundations.UniversalTuringMachine.IsUniversalWrt`) is stated relative to
a way `pair` of packaging the encoding of a machine and an input into a single string. This file
shows that the choice of packaging does not matter, as long as one packaging can be translated into
the other by a Turing machine: prefixing a universal machine with such a translator again yields a
universal machine.

This is a full analysis of the halting behaviour of the sequential composition
`compComputer tm1 tm2` of two machines: while `compComputer_seq_outputs` of
`DiagonaLean.Halt.Compositions` gives one direction, here we also *reflect* runs of the composed
machine back into runs of its second component, which yields the equivalences
`compComputer_halts_iff` and `compComputer_outputs_iff`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

@[expose] public section

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
     DiagonaLean.Halt.Helpers DiagonaLean.Halt.Compositions

namespace DiagonaLean.Foundations.UniversalTuringMachine
section Reflection

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm1 tm2 : SingleTapeTM Symbol}

/-- A configuration of the composed machine that is a halted image under `compCfgR`
comes from a halted configuration of the second component. -/
lemma eq_of_compCfgR_halted {c : tm2.Cfg} {t : BiTape Symbol}
    (h : compCfgR tm1 tm2 c = ⟨none, t⟩) : c = ⟨none, t⟩ := by
  obtain ⟨st, t'⟩ := c
  cases st with
  | none =>
    have ht : t' = t := congrArg SingleTapeTM.Cfg.BiTape h
    subst ht; rfl
  | some q =>
    have hst : (Option.map Sum.inr (some q) : Option (tm1.State ⊕ tm2.State)) = none :=
      congrArg SingleTapeTM.Cfg.state h
    simp at hst

/-- A step of the composed machine out of the second component's phase is the image of a
step of the second component. -/
lemma compCfgR_step_reflect {c : tm2.Cfg} {b : (compComputer tm1 tm2).Cfg}
    (h : (compComputer tm1 tm2).TransitionRelation (compCfgR tm1 tm2 c) b) :
    ∃ c' : tm2.Cfg, b = compCfgR tm1 tm2 c' ∧ tm2.TransitionRelation c c' := by
  obtain ⟨st, t⟩ := c
  cases st with
  | none =>
    have h' : (compComputer tm1 tm2).step ⟨none, t⟩ = some b := h
    simp at h'
  | some q =>
    generalize htr : tm2.tr q t.head = res
    obtain ⟨⟨wr, dir⟩, next⟩ := res
    have hstep : (compComputer tm1 tm2).step (compCfgR tm1 tm2 ⟨some q, t⟩) =
        some (compCfgR tm1 tm2 ⟨next, (t.write wr).optionMove dir⟩) := by
      cases next <;> simp [compCfgR, SingleTapeTM.step, compComputer, htr]
    refine ⟨⟨next, (t.write wr).optionMove dir⟩, ?_, ?_⟩
    · rw [SingleTapeTM.TransitionRelation, hstep] at h
      exact (Option.some_inj.mp h).symm
    · simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step, htr]

/-- A run of the composed machine started inside the second component's phase is the
image of a run of the second component. -/
lemma compCfgR_trace_reflect {c : tm2.Cfg} {b : (compComputer tm1 tm2).Cfg}
    (h : Relation.ReflTransGen (compComputer tm1 tm2).TransitionRelation
      (compCfgR tm1 tm2 c) b) :
    ∃ c' : tm2.Cfg, b = compCfgR tm1 tm2 c' ∧
      Relation.ReflTransGen tm2.TransitionRelation c c' := by
  induction h with
  | refl => exact ⟨c, rfl, .refl⟩
  | @tail _ _ _ hxy ih =>
    obtain ⟨cx, rfl, hcx⟩ := ih
    obtain ⟨cy, rfl, hcy⟩ := compCfgR_step_reflect hxy
    exact ⟨cy, rfl, hcx.tail hcy⟩

variable {w mid : List Symbol}

/-- Every halted configuration reachable in the composed machine is reachable from the
point at which the second component takes over. -/
private lemma reflTransGen_of_halts (h1 : tm1.Outputs w mid) {t : BiTape Symbol}
    (h : Relation.ReflTransGen (compComputer tm1 tm2).TransitionRelation
      (SingleTapeTM.initCfg (compComputer tm1 tm2) w) ⟨none, t⟩) :
    Relation.ReflTransGen (compComputer tm1 tm2).TransitionRelation
      (compCfgR tm1 tm2 (tm2.initCfg mid)) ⟨none, t⟩ := by
  have hleft : Relation.ReflTransGen (compComputer tm1 tm2).TransitionRelation
      (SingleTapeTM.initCfg (compComputer tm1 tm2) w)
      (compCfgR tm1 tm2 (tm2.initCfg mid)) := comp_left_trace h1
  rcases reflTransGen_diamond (fun {_ _ _} => transitionRelation_deterministic) hleft h with
    hcase | hcase
  · exact hcase
  · refine absurd (eq_of_compCfgR_halted (eq_of_reflTransGen_halted hcase)) (fun heq => ?_)
    exact absurd (congrArg SingleTapeTM.Cfg.state heq) (by simp [SingleTapeTM.initCfg])

/-- If `tm1` outputs `mid` on `w`, then the sequential composition halts on `w` exactly
when `tm2` halts on `mid`. -/
theorem compComputer_halts_iff (h1 : tm1.Outputs w mid) :
    Halts (compComputer tm1 tm2) w ↔ Halts tm2 mid := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨c', hc', htrace⟩ := compCfgR_trace_reflect (reflTransGen_of_halts h1 h)
    exact ⟨t, eq_of_compCfgR_halted hc'.symm ▸ htrace⟩
  · rintro ⟨t, h⟩
    exact ⟨t, (comp_left_trace h1).trans
      (Relation.ReflTransGen.lift (r := tm2.TransitionRelation) (compCfgR tm1 tm2)
        (fun _ _ hab => compCfgR_step hab) _ _ h)⟩

/-- If `tm1` outputs `mid` on `w`, then the sequential composition outputs `out` on `w`
exactly when `tm2` outputs `out` on `mid`. -/
theorem compComputer_outputs_iff (h1 : tm1.Outputs w mid) {out : List Symbol} :
    (compComputer tm1 tm2).Outputs w out ↔ tm2.Outputs mid out := by
  constructor
  · intro h
    obtain ⟨c', hc', htrace⟩ :=
      compCfgR_trace_reflect (reflTransGen_of_halts (tm2 := tm2) h1 h)
    have hc : c' = tm2.haltCfg out := eq_of_compCfgR_halted hc'.symm
    subst hc
    exact htrace
  · exact fun h => compComputer_seq_outputs h1 h
end Reflection

variable {pair1 pair2 : InstanceEncoding} {T U : SingleTapeTM Bool}

/-- `T` translates the encoding `pair₁` into the encoding `pair₂` if, on every instance
`pair₁ ⟪tm⟫ w`, it outputs `pair₂ ⟪tm⟫ w`. -/
def IsTranslator (T : SingleTapeTM Bool) (pair1 pair2 : InstanceEncoding) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [Encodable tm.State] (w : List Bool),
    T.Outputs (pair1 (encodeBoolTM tm) w) (pair2 (encodeBoolTM tm) w)

/-- Prefixing a weakly universal machine with a translator yields a machine that is
weakly universal for the translated encoding. -/
theorem IsWeaklyUniversalWrt.comp_translator (hU : IsWeaklyUniversalWrt pair2 U)
    (hT : IsTranslator T pair1 pair2) :
    IsWeaklyUniversalWrt pair1 (compComputer T U) := by
  intro tm _ w
  exact (compComputer_halts_iff (hT tm w)).trans (hU tm w)

/-- Prefixing a universal machine with a translator yields a machine that is universal
for the translated encoding. -/
theorem IsUniversalWrt.comp_translator (hU : IsUniversalWrt pair2 U)
    (hT : IsTranslator T pair1 pair2) :
    IsUniversalWrt pair1 (compComputer T U) := by
  intro tm _ w
  exact ⟨(compComputer_halts_iff (hT tm w)).trans (hU tm w).1,
    fun v => (compComputer_outputs_iff (hT tm w)).trans ((hU tm w).2 v)⟩

end DiagonaLean.Foundations.UniversalTuringMachine
