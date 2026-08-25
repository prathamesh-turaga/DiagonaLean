import Cslib
open Lean Elab Tactic


class PInstance (α : _)where
 HasSolution : α  → Prop

class Reduction (α : _) (β: _) [PInstance α] [PInstance β] where
  encode_instance: α → β
  redn (t: α): (PInstance.HasSolution t → PInstance.HasSolution (encode_instance t))


lemma valid_redn (α: _) (β: _) [PInstance α] [PInstance β] (h: Reduction α β) (t: α): PInstance.HasSolution t  → ∃ p : β, PInstance.HasSolution p :=
 by
  intro h1
  obtain ⟨encode_instance, redn⟩ := h
  exact ⟨encode_instance t, redn t h1⟩

macro "udc" t1:term ", " t2:term : tactic =>
  `(tactic| (show Reduction $t1 $t2; refine ⟨?_, ?_⟩)
