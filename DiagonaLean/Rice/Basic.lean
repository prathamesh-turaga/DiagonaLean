import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.Undecidability

namespace  DiagonaLean.Rice

open DiagonaLean.Synthetic.Notation DiagonaLean.Synthetic.Definitions

def Problem (X : Type*) := X → Prop

def Problem_undecidable (P : Problem X) : Prop := undecidable P

def Problem_decidable (P : Problem X) : Prop := SDecidable P

def HasSolution (P : Problem a) : Prop :=  ∃ x, P x

end DiagonaLean.Rice
