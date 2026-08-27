/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Foundations.Normalize.Steps

/-! # Simulating one step of the original machine

One step of `tm` is simulated by one to three steps of `normTM tm`.
-/

@[expose] public section
namespace DiagonaLean.Foundations.Normalize

open Cslib.Turing SingleTapeTM

variable (tm : SingleTapeTM Bool)
variable {t : BiTape Bool} {i : ℤ} {t' : BiTape Sym2} {q : tm.State}

lemma tm_step_eq (q : tm.State) (t : BiTape Bool) :
    tm.step ⟨some q, t⟩ =
      some ⟨(tm.tr q t.head).2,
        (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement⟩ := by
  rcases h : tm.tr q t.head with ⟨⟨wr, dir⟩, q''⟩
  simp [SingleTapeTM.step, h]

/-- Reachability in the normalised machine. -/
abbrev NSteps (c c' : (normTM tm).Cfg) : Prop :=
  Relation.ReflTransGen (normTM tm).TransitionRelation c c'

lemma nsteps_single {c c' : (normTM tm).Cfg} (h : (normTM tm).step c = some c') :
    NSteps tm c c' :=
  Relation.ReflTransGen.single h

lemma sim_of_nonneg {i : ℤ} (hi : 0 ≤ i) : Ctrl.sim (decide (0 ≤ i)) = Ctrl.simR := by
  simp [Ctrl.sim, hi]

lemma sim_of_neg {i : ℤ} (hi : i < 0) : Ctrl.sim (decide (0 ≤ i)) = Ctrl.simL := by
  rw [decide_eq_false (by omega : ¬ (0 ≤ i))]
  rfl

/-- One step of `tm` ending in a running state is simulated by several steps of
`normTM tm`. -/
theorem sim_tm_step_running {q₂ : tm.State} {t₂ : BiTape Bool}
    (h : InvAt t i t' (fold i))
    (hstep : tm.step ⟨some q, t⟩ = some ⟨some q₂, t₂⟩) :
    ∃ (i₂ : ℤ) (t₂' : BiTape Sym2),
      NSteps tm ⟨some (q, Ctrl.sim (decide (0 ≤ i))), t'⟩
        ⟨some (q₂, Ctrl.sim (decide (0 ≤ i₂))), t₂'⟩ ∧ InvAt t₂ i₂ t₂' (fold i₂) := by
  rcases htr : tm.tr q t.head with ⟨⟨wr, mv⟩, q''⟩
  rw [tm_step_eq, htr] at hstep
  simp only [Option.some.injEq, SingleTapeTM.Cfg.mk.injEq] at hstep
  obtain ⟨hq, ht⟩ := hstep
  subst ht
  subst hq
  match mv with
  | none =>
    obtain ⟨t'', hs, hinv⟩ := step_sim_stay tm (decide (0 ≤ i)) h htr
    exact ⟨i, t'', nsteps_single tm hs, hinv⟩
  | some Turing.Dir.right =>
    by_cases hi : 0 ≤ i
    · rw [sim_of_nonneg hi]
      obtain ⟨t₁, hs1, hinv1⟩ := step_sim_right_R tm hi h htr
      obtain ⟨t₂', hs2, hinv2⟩ := step_mvRR tm hinv1
      refine ⟨i + 1, t₂', ?_, hinv2⟩
      rw [sim_of_nonneg (by omega)]
      exact (nsteps_single tm hs1).trans (nsteps_single tm hs2)
    · rw [not_le] at hi
      rw [sim_of_neg hi]
      obtain ⟨t₁, hs1, hinv1⟩ := step_sim_right_L tm h htr
      obtain ⟨t₂, hs2, hinv2⟩ := step_chkL1 tm hinv1
      by_cases hi2 : i + 1 = 0
      · rw [hi2] at hinv2
        have hz : fold (0 - 1) - 2 = 0 := by norm_num [fold_neg_one]
        rw [hz] at hinv2
        obtain ⟨t₃, hs3, hinv3⟩ := step_chkL2_marker tm hinv2
        refine ⟨0, t₃, ?_, hinv3⟩
        rw [sim_of_nonneg (le_refl 0)]
        exact ((nsteps_single tm hs1).trans (nsteps_single tm hs2)).trans (nsteps_single tm hs3)
      · have hneg : i + 1 < 0 := by omega
        have hpos : fold (i + 1 - 1) - 2 = fold (i + 1) := by
          have h2 : fold (i + 1 - 1) = fold (i + 1) + 2 := fold_pred_of_neg hneg
          omega
        rw [hpos] at hinv2
        obtain ⟨t₃, hs3, hinv3⟩ := step_chkL2_data tm hinv2
        refine ⟨i + 1, t₃, ?_, hinv3⟩
        rw [sim_of_neg hneg]
        exact ((nsteps_single tm hs1).trans (nsteps_single tm hs2)).trans (nsteps_single tm hs3)
  | some Turing.Dir.left =>
    by_cases hi : 0 ≤ i
    · rw [sim_of_nonneg hi]
      obtain ⟨t₁, hs1, hinv1⟩ := step_sim_left_R tm h htr
      by_cases hi0 : i = 0
      · subst hi0
        have hz : fold (0 - 1 + 1) - 1 = 0 := by norm_num [fold_zero]
        rw [hz] at hinv1
        obtain ⟨t₂, hs2, hinv2⟩ := step_chkR_marker tm hinv1
        obtain ⟨t₃, hs3, hinv3⟩ := step_mvRL tm hinv2
        refine ⟨-1, t₃, ?_, hinv3⟩
        rw [sim_of_neg (by omega)]
        exact ((nsteps_single tm hs1).trans (nsteps_single tm hs2)).trans (nsteps_single tm hs3)
      · have hi1 : 0 ≤ i - 1 := by omega
        have hpos : fold (i - 1 + 1) - 1 = fold (i - 1) + 1 := by
          have h2 : fold (i - 1 + 1) = fold (i - 1) + 2 := fold_succ_of_nonneg hi1
          omega
        rw [hpos] at hinv1
        obtain ⟨t₂, hs2, hinv2⟩ := step_chkR_data tm hinv1
        refine ⟨i - 1, t₂, ?_, hinv2⟩
        rw [sim_of_nonneg hi1]
        exact (nsteps_single tm hs1).trans (nsteps_single tm hs2)
    · rw [not_le] at hi
      rw [sim_of_neg hi]
      obtain ⟨t₁, hs1, hinv1⟩ := step_sim_left_L tm hi h htr
      obtain ⟨t₂, hs2, hinv2⟩ := step_mvRL tm hinv1
      refine ⟨i - 1, t₂, ?_, hinv2⟩
      rw [sim_of_neg (by omega)]
      exact (nsteps_single tm hs1).trans (nsteps_single tm hs2)

/-- A halting step of `tm` is simulated by a halting step of `normTM tm`. -/
theorem sim_tm_step_halt {t₂ : BiTape Bool} (h : InvAt t i t' (fold i))
    (hstep : tm.step ⟨some q, t⟩ = some ⟨none, t₂⟩) :
    ∃ t₂' : BiTape Sym2, NSteps tm ⟨some (q, Ctrl.sim (decide (0 ≤ i))), t'⟩ ⟨none, t₂'⟩ := by
  rcases htr : tm.tr q t.head with ⟨⟨wr, mv⟩, q''⟩
  rw [tm_step_eq, htr] at hstep
  simp only [Option.some.injEq, SingleTapeTM.Cfg.mk.injEq] at hstep
  obtain ⟨hq, _⟩ := hstep
  subst hq
  obtain ⟨t₂', hs⟩ := step_sim_halt tm (decide (0 ≤ i)) h htr
  exact ⟨t₂', nsteps_single tm hs⟩

end DiagonaLean.Foundations.Normalize
