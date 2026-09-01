import DiagonaLean.Synthetic.Undecidability

/-! # Linter test fixture (not wired into `DiagonaLean.lean`)

Demonstrates the exact failure mode `scripts/check-classical-reductions.sh` guards against:
`Even` is a genuinely decidable predicate on `ℕ`, yet the classical witness below "proves"
`Undecidable (fun n => Even n)` by branching on `Halts p.1 p.2` itself via
`Classical.propDecidable`, with no algorithmic content whatsoever. See the convention noted on
`ManyOneReduces` in `Synthetic/Definitions.lean`. -/

open DiagonaLean.Halt Cslib.Turing DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- A "reduction" `HALT → ℕ` that decides nothing: it picks `0` when the halting instance
halts and `1` otherwise, using classical excluded middle on `Halts p.1 p.2` to perform that
case split. This has no algorithmic content -- it is exactly the attack the `ManyOneReduces`
convention rules out. -/
noncomputable def vacuousReduction (p : EncodableTM Bool × List Bool) : ℕ :=
  haveI := Classical.propDecidable (Halts p.1.toSingleTapeTM p.2)
  if Halts p.1.toSingleTapeTM p.2 then 0 else 1

theorem randodec : Undecidable (fun n : ℕ => Even n) := by
  refine ⟨⟨vacuousReduction, fun p => ?_⟩⟩
  obtain ⟨M, w⟩ := p
  show Halts M.toSingleTapeTM w ↔ Even (vacuousReduction (M, w))
  unfold vacuousReduction
  by_cases h : Halts M.toSingleTapeTM w
  · simp [h]
  · simp [h, Nat.not_even_one]


def deci {α} (p:α → Prop) :=
 ∃ (f : α → Bool), ∀ (x : α), (f x) ↔ (p x)
