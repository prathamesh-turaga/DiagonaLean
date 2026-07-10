import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Rice.Basic

open DiagonaLean.Synthetic.Notation DiagonaLean.Synthetic.Definitions DiagonaLean.Rice

variable {X Y : Type*}

def meow (f : X → Y) (p : X → Prop) (q : Y → Prop) : Prop := reduction f p q

theorem undecidablity_of_reduction {X Y : Type*} {P1 : X → Prop} {P2 : Y → Prop}
  (h_red : P1 ⪯ₘ P2) : ¬ SDecidable P1 → ¬ SDecidable P2 := by
  intro hs1 hs2
  have h : SDecidable P1 := by
    rcases h_red with ⟨f, hf⟩
    rcases hs2 with ⟨g, hg⟩
    use g ∘ f
    intro x
    rw [hf x]
    exact hg (f x)
  contradiction

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

theorem decidability_of_reduction {X Y : Type*} {P1 : X → Prop} {P2 : Y → Prop}
  (h_red : P1 ⪯ₘ P2) : SDecidable P2 → SDecidable P1 := by
  intro hs2
  rcases h_red with ⟨f, hf⟩
  rcases hs2 with ⟨g, hg⟩
  use g ∘ f
  intro x
  rw [hf x]
  exact hg (f x)

theorem semi_decidability_of_reduction {X Y : Type*} {P1 : X → Prop} {P2 : Y → Prop}
  (h_red : P1 ⪯ₘ P2) : semi_decidable P2 → semi_decidable P1 := by
  intro hs2
  rcases h_red with ⟨f, hf⟩
  rcases hs2 with ⟨g, hg⟩
  use g ∘ f
  intro x
  rw [hf x]
  exact hg (f x)
