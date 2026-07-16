/-
Copyright (c) 2026 Kshitij Salunke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke
-/

import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Synthetic.ReductionChain
import DiagonaLean.Rice.Basic

open DiagonaLean.Synthetic.Notation DiagonaLean.Synthetic.Definitions DiagonaLean.Rice
open DiagonaLean.Synthetic.ReductionChain

variable {X Y : Type*}

/-- If `P1` reduces to `P2` and `P1` is undecidable, then `P2` is undecidable. -/
theorem undecidability_of_reduction {X Y : Type*} {P1 : X → Prop} {P2 : Y → Prop}
  (h_red : P1 ⪯ₘ P2) : ¬ SDecidable P1 → ¬ SDecidable P2 := by
  intro hs1 hs2
  exact hs1 (dec_red h_red hs2)

/-- If `P1` reduces to `P2` and `P1` is not semi-decidable, then `P2` is not semi-decidable. -/
theorem un_semi_decidability_of_reduction {X Y : Type*} {P1 : X → Prop} {P2 : Y → Prop}
  (h_red : P1 ⪯ₘ P2): ¬ semi_decidable P1 → ¬ semi_decidable P2 := by
  intro hs1 hs2
  have h : semi_decidable P1 := by
    rcases h_red with ⟨f, hf⟩
    rcases hs2 with ⟨g, hg⟩
    use g ∘ f
    intro x
    rw [hf x]
    exact hg (f x)
  contradiction

/-- If `P1` reduces to `P2` and `P2` is semi-decidable, then `P1` is semi-decidable. -/
theorem semi_decidability_of_reduction {X Y : Type*} {P1 : X → Prop} {P2 : Y → Prop}
  (h_red : P1 ⪯ₘ P2) : semi_decidable P2 → semi_decidable P1 := by
  intro hs2
  rcases h_red with ⟨f, hf⟩
  rcases hs2 with ⟨g, hg⟩
  use g ∘ f
  intro x
  rw [hf x]
  exact hg (f x)
