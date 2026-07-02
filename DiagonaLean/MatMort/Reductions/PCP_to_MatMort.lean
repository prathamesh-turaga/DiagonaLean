/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

import DiagonaLean.MatMort.Basic
import DiagonaLean.PCP.Basic

namespace DiagonaLean.MatMort.Reduction
open Matrix DiagonaLean.PCP DiagonaLean.MatMort

def S : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1; 0, 0, 0; 0, 0, 0]

def T : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; -1, 1, 0; 0, 0, 0]

variable {p q r s : ℕ → ℤ}

variable (hpq : p j > q j ∧ q j ≥ 0)
variable (hrs : r j > s j ∧ s j ≥ 0)

def W (j : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![p j, 0, 0; 0, r j, 0; q j, s j, 1]

local notation "W'" => W (p := p) (q := q) (r := r) (s := s)

variable (a b c : ℤ)

@[simp]
lemma row_prod_S : !![a, b, c] * S = a • !![1, 0, 1] := by simp [S]

@[simp]
lemma row_prod_T : !![a, b, c] * T = (a - b) • !![1, -1, 0] := by simp [T]; grind

def invW (j : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / p j, 0, 0; 0, 1 / r j, 0; -(q j / p j), -(s j / r j), 1]

lemma non_singular_W (j : ℕ) {hpq : p j > q j ∧ q ≥ 0} {hrs : r j > s j ∧ s j ≥ 0}  :
    det (W' j) ≠ 0 := by
  have hp : p j ≠ 0 := by
    have h1 : p j > q j := hpq.1
    have h2 : q j ≥ 0 := hpq.2 j
    linarith
  have hr : r j ≠ 0 := by
    have h1 : r j > s j := hrs.1
    have h2 : s j ≥ 0 := hrs.2
    linarith
  have hdet : (W' j).det = p j * r j := by
    unfold W
    simp [Matrix.det_fin_three]
  simp only [hdet]
  exact mul_ne_zero hp hr

theorem mortal_iff_exists_prod_of_Ws
    (hpq : ∀ j, p j > q j ∧ q j ≥ 0)
    (hrs : ∀ j, r j > s j ∧ s j ≥ 0) :
    HasSolution ({S, T} ∪ (Finset.Icc 1 m).biUnion
      (fun j => {W' j})) ↔ ∃ (m : ℕ) (is : List ℕ) (h : ℤ), h > 0 ∧
      (∀ i ∈ is, 1 ≤ i ∧ i ≤ m) ∧ !![(1 : ℤ), 0, 1] *
        (is.map (fun j => W' j)).prod = !![h, h, 1] := by
  sorry

end DiagonaLean.MatMort.Reduction
