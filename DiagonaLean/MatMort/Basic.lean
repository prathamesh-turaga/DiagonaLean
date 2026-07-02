/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Data.Matrix.Basic

@[expose] public section

namespace DiagonaLean.MatMort
open Matrix

def HasSolution (Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)) : Prop :=
  ∃ Ms' ⊆ Ms, (Ms'.toList).prod = 0

end DiagonaLean.MatMort
