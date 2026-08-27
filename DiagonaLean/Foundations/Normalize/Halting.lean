/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Foundations.Normalize.Sim
import DiagonaLean.Foundations.Normalize.Input
import DiagonaLean.Halt.Basic
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP

/-! # Reachable configurations of the normalised machine

`PhaseInv` describes the configurations of `normTM tm` that arise during the simulation:
each of them encodes a configuration of `tm`, the control state recording how far the
current step of `tm` has been simulated.  It is closed under the transition relation, which
gives both the halting equivalence and the `NoLeftBoundary` property.
-/

@[expose] public section
namespace DiagonaLean.Foundations.Normalize

open Cslib.Turing SingleTapeTM

variable (tm : SingleTapeTM Bool)

/-- The configurations of `normTM tm` occurring during the simulation of `tm`, described in
terms of the configuration `⟨some q, t⟩` of `tm` being simulated and the absolute index `i`
of its head. -/
def PhaseInv (q : tm.State) (t : BiTape Bool) (i : ℤ)
    (s : Option (tm.State × Ctrl)) (tp : BiTape Sym2) : Prop :=
  (s = some (q, Ctrl.start) ∧ i = 0 ∧ InvAt t i tp 0)
  ∨ (s = some (q, Ctrl.sim (decide (0 ≤ i))) ∧ InvAt t i tp (fold i))
  ∨ (s = some (q, Ctrl.mvRR) ∧ 0 ≤ i ∧ InvAt t i tp (fold i - 1))
  ∨ (s = some (q, Ctrl.mvRL) ∧ i < 0 ∧ InvAt t i tp (fold i - 1))
  ∨ (s = some (q, Ctrl.chkR) ∧ -1 ≤ i ∧ InvAt t i tp (fold (i + 1) - 1))
  ∨ (s = some (q, Ctrl.chkL1) ∧ i ≤ 0 ∧ InvAt t i tp (fold (i - 1) - 1))
  ∨ (s = some (q, Ctrl.chkL2) ∧ i ≤ 0 ∧ InvAt t i tp (fold (i - 1) - 2))

variable {tm}

lemma PhaseInv.state_ne_none {q : tm.State} {t i s tp} (h : PhaseInv tm q t i s tp) :
    s ≠ none := by
  rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ <;>
    simp [hs]

/-- One step of the normalised machine from a simulation configuration. -/
theorem phase_step {q : tm.State} {t : BiTape Bool} {i : ℤ}
    {s : Option (tm.State × Ctrl)} {tp : BiTape Sym2} (hp : PhaseInv tm q t i s tp) :
    ∃ c'' : (normTM tm).Cfg, (normTM tm).step ⟨s, tp⟩ = some c'' ∧
      ((∃ (q₂ : tm.State) (t₂ : BiTape Bool) (i₂ : ℤ),
          PhaseInv tm q₂ t₂ i₂ c''.state c''.BiTape ∧
            Relation.ReflTransGen tm.TransitionRelation ⟨some q, t⟩ ⟨some q₂, t₂⟩)
        ∨ (c''.state = none ∧
            ∃ tpx, Relation.ReflTransGen tm.TransitionRelation ⟨some q, t⟩ ⟨none, tpx⟩)) := by
  rcases hp with ⟨hs, hi, hinv⟩ | ⟨hs, hinv⟩ | ⟨hs, hi, hinv⟩ | ⟨hs, hi, hinv⟩ |
      ⟨hs, hi, hinv⟩ | ⟨hs, hi, hinv⟩ | ⟨hs, hi, hinv⟩
  -- start
  · subst hs; subst hi
    obtain ⟨t'', hstep, hinv'⟩ := step_start tm hinv
    refine ⟨_, hstep, Or.inl ⟨q, t, 0, ?_, Relation.ReflTransGen.refl⟩⟩
    exact Or.inr (Or.inl ⟨by simp [Ctrl.sim], hinv'⟩)
  -- sim
  · subst hs
    rcases htr : tm.tr q t.head with ⟨⟨wr, mv⟩, q''⟩
    have hstepTm : tm.step ⟨some q, t⟩
        = some ⟨q'', (t.write wr).optionMove mv⟩ := by
      rw [tm_step_eq, htr]
    match q'' with
    | none =>
      obtain ⟨t'', hstep⟩ := step_sim_halt tm (decide (0 ≤ i)) hinv htr
      exact ⟨_, hstep, Or.inr ⟨rfl, _, Relation.ReflTransGen.single hstepTm⟩⟩
    | some q₂ =>
      have hreach : Relation.ReflTransGen tm.TransitionRelation ⟨some q, t⟩
          ⟨some q₂, (t.write wr).optionMove mv⟩ := Relation.ReflTransGen.single hstepTm
      match mv with
      | none =>
        obtain ⟨t'', hstep, hinv'⟩ := step_sim_stay tm (decide (0 ≤ i)) hinv htr
        exact ⟨_, hstep, Or.inl ⟨q₂, t.write wr, i, Or.inr (Or.inl ⟨rfl, hinv'⟩), hreach⟩⟩
      | some Turing.Dir.right =>
        by_cases hi : 0 ≤ i
        · rw [sim_of_nonneg hi]
          obtain ⟨t'', hstep, hinv'⟩ := step_sim_right_R tm hi hinv htr
          refine ⟨_, hstep, Or.inl ⟨q₂, (t.write wr).moveRight, i + 1, ?_, hreach⟩⟩
          exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega, hinv'⟩))
        · rw [not_le] at hi
          rw [sim_of_neg hi]
          obtain ⟨t'', hstep, hinv'⟩ := step_sim_right_L tm hinv htr
          refine ⟨_, hstep, Or.inl ⟨q₂, (t.write wr).moveRight, i + 1, ?_, hreach⟩⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, hinv'⟩)))))
      | some Turing.Dir.left =>
        by_cases hi : 0 ≤ i
        · rw [sim_of_nonneg hi]
          obtain ⟨t'', hstep, hinv'⟩ := step_sim_left_R tm hinv htr
          refine ⟨_, hstep, Or.inl ⟨q₂, (t.write wr).moveLeft, i - 1, ?_, hreach⟩⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, hinv'⟩))))
        · rw [not_le] at hi
          rw [sim_of_neg hi]
          obtain ⟨t'', hstep, hinv'⟩ := step_sim_left_L tm hi hinv htr
          refine ⟨_, hstep, Or.inl ⟨q₂, (t.write wr).moveLeft, i - 1, ?_, hreach⟩⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, hinv'⟩)))
  -- mvRR
  · subst hs
    obtain ⟨t'', hstep, hinv'⟩ := step_mvRR tm hinv
    refine ⟨_, hstep, Or.inl ⟨q, t, i, ?_, Relation.ReflTransGen.refl⟩⟩
    exact Or.inr (Or.inl ⟨by rw [sim_of_nonneg hi]; rfl, hinv'⟩)
  -- mvRL
  · subst hs
    obtain ⟨t'', hstep, hinv'⟩ := step_mvRL tm hinv
    refine ⟨_, hstep, Or.inl ⟨q, t, i, ?_, Relation.ReflTransGen.refl⟩⟩
    exact Or.inr (Or.inl ⟨by rw [sim_of_neg hi]; rfl, hinv'⟩)
  -- chkR
  · subst hs
    by_cases hi0 : i = -1
    · subst hi0
      have hz : fold (-1 + 1) - 1 = 0 := by norm_num [fold_zero]
      rw [hz] at hinv
      obtain ⟨t'', hstep, hinv'⟩ := step_chkR_marker tm hinv
      refine ⟨_, hstep, Or.inl ⟨q, t, -1, ?_, Relation.ReflTransGen.refl⟩⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, hinv'⟩)))
    · have hi1 : 0 ≤ i := by omega
      have hz : fold (i + 1) - 1 = fold i + 1 := by
        have := fold_succ_of_nonneg hi1; omega
      rw [hz] at hinv
      obtain ⟨t'', hstep, hinv'⟩ := step_chkR_data tm hinv
      refine ⟨_, hstep, Or.inl ⟨q, t, i, ?_, Relation.ReflTransGen.refl⟩⟩
      exact Or.inr (Or.inl ⟨by rw [sim_of_nonneg hi1]; rfl, hinv'⟩)
  -- chkL1
  · subst hs
    obtain ⟨t'', hstep, hinv'⟩ := step_chkL1 tm hinv
    refine ⟨_, hstep, Or.inl ⟨q, t, i, ?_, Relation.ReflTransGen.refl⟩⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hi, hinv'⟩)))))
  -- chkL2
  · subst hs
    by_cases hi0 : i = 0
    · subst hi0
      have hz : fold (0 - 1) - 2 = 0 := by norm_num [fold_neg_one]
      rw [hz] at hinv
      obtain ⟨t'', hstep, hinv'⟩ := step_chkL2_marker tm hinv
      refine ⟨_, hstep, Or.inl ⟨q, t, 0, ?_, Relation.ReflTransGen.refl⟩⟩
      exact Or.inr (Or.inl ⟨by simp [Ctrl.sim], hinv'⟩)
    · have hineg : i < 0 := by omega
      have hz : fold (i - 1) - 2 = fold i := by
        have := fold_pred_of_neg hineg; omega
      rw [hz] at hinv
      obtain ⟨t'', hstep, hinv'⟩ := step_chkL2_data tm hinv
      refine ⟨_, hstep, Or.inl ⟨q, t, i, ?_, Relation.ReflTransGen.refl⟩⟩
      exact Or.inr (Or.inl ⟨by rw [sim_of_neg hineg]; rfl, hinv'⟩)

variable (tm)

/-- The initial configuration of the normalised machine is a simulation configuration. -/
lemma phaseInv_init (w : List Bool) :
    PhaseInv tm tm.q₀ (BiTape.mk₁ w) 0
      ((normTM tm).initCfg (encInput w)).state ((normTM tm).initCfg (encInput w)).BiTape :=
  Or.inl ⟨rfl, rfl, invAt_init w⟩

/-- Every configuration reachable by the normalised machine is either halted or a
simulation configuration. -/
theorem reach_phase (w : List Bool) {c : (normTM tm).Cfg}
    (h : NSteps tm ((normTM tm).initCfg (encInput w)) c) :
    c.state = none ∨
      ∃ (q : tm.State) (t : BiTape Bool) (i : ℤ), PhaseInv tm q t i c.state c.BiTape := by
  induction h with
  | refl => exact Or.inr ⟨tm.q₀, BiTape.mk₁ w, 0, phaseInv_init tm w⟩
  | @tail b c _ hbc ih =>
    have hstepb : (normTM tm).step b = some c := hbc
    rcases ih with hb | ⟨q, t, i, hp⟩
    · exfalso
      obtain ⟨s, tpb⟩ := b
      simp only at hb
      subst hb
      simp [SingleTapeTM.step] at hstepb
    · obtain ⟨c'', hstep, hc⟩ := phase_step hp
      have hbb : ((⟨b.state, b.BiTape⟩ : (normTM tm).Cfg)) = b := rfl
      rw [hbb] at hstep
      have hcc : c = c'' := by
        rw [hstepb] at hstep; exact Option.some.inj hstep
      subst hcc
      rcases hc with ⟨q₂, t₂, i₂, hp₂, _⟩ | ⟨hnone, _⟩
      · exact Or.inr ⟨q₂, t₂, i₂, hp₂⟩
      · exact Or.inl hnone

/-- No halting configuration of `tm` is reachable from `c`. -/
def NoHaltFrom (c : tm.Cfg) : Prop :=
  ∀ tape : BiTape Bool, ¬ Relation.ReflTransGen tm.TransitionRelation c ((⟨none, tape⟩ : tm.Cfg))

variable {tm}

lemma NoHaltFrom.mono {c c' : tm.Cfg} (h : NoHaltFrom tm c)
    (hr : Relation.ReflTransGen tm.TransitionRelation c c') : NoHaltFrom tm c' :=
  fun tape hc => h tape (hr.trans hc)

variable (tm)

/-- If `tm` does not halt on `w`, every reachable configuration of the normalised machine is
a simulation configuration of a non-halting configuration of `tm`. -/
theorem reach_phase_noHalt (w : List Bool) (hnh : ¬ DiagonaLean.Halt.Halts tm w)
    {c : (normTM tm).Cfg} (h : NSteps tm ((normTM tm).initCfg (encInput w)) c) :
    ∃ (q : tm.State) (t : BiTape Bool) (i : ℤ),
      PhaseInv tm q t i c.state c.BiTape ∧ NoHaltFrom tm ⟨some q, t⟩ := by
  have hinit : NoHaltFrom tm (⟨some tm.q₀, BiTape.mk₁ w⟩ : tm.Cfg) := by
    intro tape hc
    exact hnh ⟨tape, hc⟩
  induction h with
  | refl => exact ⟨tm.q₀, BiTape.mk₁ w, 0, phaseInv_init tm w, hinit⟩
  | @tail b c _ hbc ih =>
    have hstepb : (normTM tm).step b = some c := hbc
    obtain ⟨q, t, i, hp, hnhc⟩ := ih
    obtain ⟨c'', hstep, hc⟩ := phase_step hp
    have hbb : ((⟨b.state, b.BiTape⟩ : (normTM tm).Cfg)) = b := rfl
    rw [hbb] at hstep
    have hcc : c = c'' := by
      rw [hstepb] at hstep; exact Option.some.inj hstep
    subst hcc
    rcases hc with ⟨q₂, t₂, i₂, hp₂, hreach⟩ | ⟨_, tpx, hhalt⟩
    · exact ⟨q₂, t₂, i₂, hp₂, hnhc.mono hreach⟩
    · exact absurd hhalt (hnhc tpx)

/-- Forward simulation: every configuration reachable by `tm` is mirrored by the normalised
machine. -/
theorem reach_forward (w : List Bool) {c : tm.Cfg}
    (h : Relation.ReflTransGen tm.TransitionRelation (tm.initCfg w) c) :
    (∃ (q : tm.State) (t : BiTape Bool) (i : ℤ) (t' : BiTape Sym2), c = ⟨some q, t⟩ ∧
        NSteps tm ((normTM tm).initCfg (encInput w))
          ⟨some (q, Ctrl.sim (decide (0 ≤ i))), t'⟩ ∧ InvAt t i t' (fold i))
      ∨ (∃ tp' : BiTape Sym2, NSteps tm ((normTM tm).initCfg (encInput w)) ⟨none, tp'⟩) := by
  induction h with
  | refl =>
    obtain ⟨t'', hstep, hinv⟩ := step_start (q := tm.q₀) tm (invAt_init w)
    refine Or.inl ?_
    refine ⟨tm.q₀, BiTape.mk₁ w, 0, t'', rfl, ?_, by simpa [fold_zero] using hinv⟩
    have : Ctrl.sim (decide (0 ≤ (0 : ℤ))) = Ctrl.simR := by simp [Ctrl.sim]
    rw [this]
    exact nsteps_single tm hstep
  | @tail b c _ hbc ih =>
    have hstepb : tm.step b = some c := hbc
    rcases ih with ⟨q, t, i, t', hb, hreach, hinv⟩ | hhalt
    · subst hb
      obtain ⟨s, tc⟩ := c
      match s with
      | none =>
        obtain ⟨t₂', hs⟩ := sim_tm_step_halt tm hinv hstepb
        exact Or.inr ⟨t₂', hreach.trans hs⟩
      | some q₂ =>
        obtain ⟨i₂, t₂', hs, hinv₂⟩ := sim_tm_step_running tm hinv hstepb
        exact Or.inl ⟨q₂, tc, i₂, t₂', rfl, hreach.trans hs, hinv₂⟩
    · exact Or.inr hhalt

/-- The normalised machine halts on the encoded input exactly when the original machine
halts on the original input. -/
theorem halts_normTM_iff (w : List Bool) :
    DiagonaLean.Halt.Halts tm w ↔ DiagonaLean.Halt.Halts (normTM tm) (encInput w) := by
  constructor
  · rintro ⟨tape, hreach⟩
    rcases reach_forward tm w hreach with ⟨q, t, i, t', hc, _, _⟩ | ⟨tp', hs⟩
    · exact absurd hc (by simp)
    · exact ⟨tp', hs⟩
  · intro hh
    by_contra hnh
    obtain ⟨tape', hreach⟩ := hh
    obtain ⟨q, t, i, hp, _⟩ := reach_phase_noHalt tm w hnh hreach
    exact hp.state_ne_none rfl

end DiagonaLean.Foundations.Normalize
