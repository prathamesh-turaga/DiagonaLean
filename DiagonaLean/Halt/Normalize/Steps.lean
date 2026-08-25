import DiagonaLean.Halt.Normalize.Invariant

/-! # Single steps of the normalised machine

For each control state we describe the effect of one step of `normTM tm` on a configuration
satisfying the appropriate instance of the simulation invariant.
-/

namespace DiagonaLean.Normalize

open Cslib.Turing SingleTapeTM

variable (tm : SingleTapeTM Bool)
variable {t : BiTape Bool} {i : ℤ} {t' : BiTape Sym2} {q : tm.State}

lemma normTM_step (q : tm.State) (ctrl : Ctrl) (t' : BiTape Sym2) :
    (normTM tm).step ⟨some (q, ctrl), t'⟩ =
      some ⟨(normTr tm q ctrl t'.head).2,
        (t'.write (normTr tm q ctrl t'.head).1.symbol).optionMove
          (normTr tm q ctrl t'.head).1.movement⟩ := by
  rcases h : normTr tm q ctrl t'.head with ⟨⟨wr, dir⟩, q''⟩
  simp [SingleTapeTM.step, normTM, h]

@[simp] lemma optionMove_none' (x : BiTape Sym2) : x.optionMove none = x := rfl

@[simp] lemma write_head_eq (x : BiTape Sym2) : x.write x.head = x := rfl

@[simp] lemma optionMove_some_right (x : BiTape Sym2) :
    x.optionMove (some Turing.Dir.right) = x.moveRight := rfl

@[simp] lemma optionMove_some_left (x : BiTape Sym2) :
    x.optionMove (some Turing.Dir.left) = x.moveLeft := rfl

/-! ### The initial step -/

lemma step_start (h : InvAt t 0 t' 0) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.start), t'⟩
        = some ⟨some (q, Ctrl.simR), t''⟩ ∧ InvAt t 0 t'' (fold 0) := by
  have hhd : t'.head = some Mk := by simpa using h.head_eq_Mk
  have hw : t'.write (some Mk) = t' := by rw [← hhd]; rfl
  refine ⟨t'.moveRight, ?_, ?_⟩
  · rw [normTM_step]
    simp [normTr, hw]
  · simpa [fold_zero] using h.moveRight

/-! ### Finishing a two-cell move to the right -/

lemma step_mvRR (h : InvAt t i t' (fold i - 1)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.mvRR), t'⟩
        = some ⟨some (q, Ctrl.simR), t''⟩ ∧ InvAt t i t'' (fold i) := by
  refine ⟨(t'.write (preserve t'.head)).moveRight, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr]
  · have := (h.write_preserve (by have := one_le_fold i; omega)).moveRight
    simpa using this

lemma step_mvRL (h : InvAt t i t' (fold i - 1)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.mvRL), t'⟩
        = some ⟨some (q, Ctrl.simL), t''⟩ ∧ InvAt t i t'' (fold i) := by
  refine ⟨(t'.write (preserve t'.head)).moveRight, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr]
  · have := (h.write_preserve (by have := one_le_fold i; omega)).moveRight
    simpa using this

/-! ### Checking for the marker after a left move -/

lemma step_chkR_marker (h : InvAt t (-1) t' 0) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.chkR), t'⟩
        = some ⟨some (q, Ctrl.mvRL), t''⟩ ∧ InvAt t (-1) t'' (fold (-1) - 1) := by
  have hhd : t'.head = some Mk := by simpa using h.head_eq_Mk
  have hw : t'.write (some Mk) = t' := by rw [← hhd]; rfl
  refine ⟨t'.moveRight, ?_, ?_⟩
  · rw [normTM_step]
    simp [normTr, hhd, hw]
  · simpa [fold_neg_one] using h.moveRight

lemma step_chkR_data (h : InvAt t i t' (fold i + 1)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.chkR), t'⟩
        = some ⟨some (q, Ctrl.simR), t''⟩ ∧ InvAt t i t'' (fold i) := by
  have hhd : t'.head ≠ some Mk := by
    have := h.head_ne_Mk (by have := one_le_fold i; omega)
    simpa using this
  refine ⟨(t'.write (preserve t'.head)).moveLeft, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr, hhd]
  · have := (h.write_preserve (by have := one_le_fold i; omega)).moveLeft
    simpa using this

lemma step_chkL1 (h : InvAt t i t' (fold (i - 1) - 1)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.chkL1), t'⟩
        = some ⟨some (q, Ctrl.chkL2), t''⟩ ∧ InvAt t i t'' (fold (i - 1) - 2) := by
  refine ⟨(t'.write (preserve t'.head)).moveLeft, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr]
  · have := (h.write_preserve (by have := one_le_fold (i - 1); omega)).moveLeft
    simpa [show fold (i - 1) - 1 - 1 = fold (i - 1) - 2 by ring] using this

lemma step_chkL2_marker (h : InvAt t 0 t' 0) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.chkL2), t'⟩
        = some ⟨some (q, Ctrl.simR), t''⟩ ∧ InvAt t 0 t'' (fold 0) := by
  have hhd : t'.head = some Mk := by simpa using h.head_eq_Mk
  have hw : t'.write (some Mk) = t' := by rw [← hhd]; rfl
  refine ⟨t'.moveRight, ?_, ?_⟩
  · rw [normTM_step]
    simp [normTr, hhd, hw]
  · simpa [fold_zero] using h.moveRight

lemma step_chkL2_data (h : InvAt t i t' (fold i)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.chkL2), t'⟩
        = some ⟨some (q, Ctrl.simL), t''⟩ ∧ InvAt t i t'' (fold i) := by
  have hhd : t'.head ≠ some Mk := by
    have := h.head_ne_Mk (one_le_fold i)
    simpa using this
  refine ⟨t'.write (preserve t'.head), ?_, ?_⟩
  · rw [normTM_step]; simp [normTr, hhd]
  · exact h.write_preserve (by have := one_le_fold i; omega)

/-! ### Simulating one step of `tm` -/

lemma InvAt.head_decode' (h : InvAt t i t' (fold i)) : decSym t'.head = t.head := by
  simpa using h.head_decode

lemma step_sim_halt {wr : Option Bool} {mv : Option Turing.Dir} (b : Bool)
    (h : InvAt t i t' (fold i)) (htr : tm.tr q t.head = (⟨wr, mv⟩, none)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.sim b), t'⟩ = some ⟨none, t''⟩ := by
  have hd := h.head_decode'
  refine ⟨t'.write (encSym wr), ?_⟩
  cases b <;> · rw [normTM_step]; simp [normTr, simStep, hd, htr]

lemma step_sim_stay {wr : Option Bool} {q₂ : tm.State} (b : Bool)
    (h : InvAt t i t' (fold i)) (htr : tm.tr q t.head = (⟨wr, none⟩, some q₂)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.sim b), t'⟩
        = some ⟨some (q₂, Ctrl.sim b), t''⟩ ∧ InvAt (t.write wr) i t'' (fold i) := by
  have hd := h.head_decode'
  refine ⟨t'.write (encSym wr), ?_, h.write wr⟩
  cases b <;> · rw [normTM_step]; simp [normTr, simStep, hd, htr]

lemma step_sim_right_R {wr : Option Bool} {q₂ : tm.State} (hi : 0 ≤ i)
    (h : InvAt t i t' (fold i))
    (htr : tm.tr q t.head = (⟨wr, some Turing.Dir.right⟩, some q₂)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.simR), t'⟩
        = some ⟨some (q₂, Ctrl.mvRR), t''⟩
      ∧ InvAt ((t.write wr).moveRight) (i + 1) t'' (fold (i + 1) - 1) := by
  have hd := h.head_decode'
  refine ⟨(t'.write (encSym wr)).moveRight, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr, simStep, hd, htr]
  · have := ((h.write wr).moveRight).tm_moveRight
    rwa [show fold i + 1 = fold (i + 1) - 1 by rw [fold_succ_of_nonneg hi]; ring] at this

lemma step_sim_right_L {wr : Option Bool} {q₂ : tm.State}
    (h : InvAt t i t' (fold i))
    (htr : tm.tr q t.head = (⟨wr, some Turing.Dir.right⟩, some q₂)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.simL), t'⟩
        = some ⟨some (q₂, Ctrl.chkL1), t''⟩
      ∧ InvAt ((t.write wr).moveRight) (i + 1) t'' (fold (i + 1 - 1) - 1) := by
  have hd := h.head_decode'
  refine ⟨(t'.write (encSym wr)).moveLeft, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr, simStep, hd, htr]
  · have := ((h.write wr).moveLeft).tm_moveRight
    rwa [show i + 1 - 1 = i by ring]

lemma step_sim_left_R {wr : Option Bool} {q₂ : tm.State}
    (h : InvAt t i t' (fold i))
    (htr : tm.tr q t.head = (⟨wr, some Turing.Dir.left⟩, some q₂)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.simR), t'⟩
        = some ⟨some (q₂, Ctrl.chkR), t''⟩
      ∧ InvAt ((t.write wr).moveLeft) (i - 1) t'' (fold (i - 1 + 1) - 1) := by
  have hd := h.head_decode'
  refine ⟨(t'.write (encSym wr)).moveLeft, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr, simStep, hd, htr]
  · have := ((h.write wr).moveLeft).tm_moveLeft
    rwa [show i - 1 + 1 = i by ring]

lemma step_sim_left_L {wr : Option Bool} {q₂ : tm.State} (hi : i < 0)
    (h : InvAt t i t' (fold i))
    (htr : tm.tr q t.head = (⟨wr, some Turing.Dir.left⟩, some q₂)) :
    ∃ t'', (normTM tm).step ⟨some (q, Ctrl.simL), t'⟩
        = some ⟨some (q₂, Ctrl.mvRL), t''⟩
      ∧ InvAt ((t.write wr).moveLeft) (i - 1) t'' (fold (i - 1) - 1) := by
  have hd := h.head_decode'
  refine ⟨(t'.write (encSym wr)).moveRight, ?_, ?_⟩
  · rw [normTM_step]; simp [normTr, simStep, hd, htr]
  · have := ((h.write wr).moveRight).tm_moveLeft
    rwa [show fold i + 1 = fold (i - 1) - 1 by rw [fold_pred_of_neg hi]; ring] at this

end DiagonaLean.Normalize
