  /-
  Copyright (c) 2026 Kshitij Salunke. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Kshitij Salunke
  -/

  import DiagonaLean.Rice.Basic
  import DiagonaLean.Synthetic.ReductionChain
  import DiagonaLean.Halt.Encoding

/-! # Undecidability of the Empty Language

We show that the empty language property `isEmptyLang` is undecidable by reducing
`HALT` to its complement. The reduction uses a classical if-then-else:

    f(M, w) = acceptsEmptyTM   if M halts on w
            = neverHaltTM       otherwise

Then `HALT(M, w) ↔ ¬ isEmptyLang(f(M, w))`, giving `HALT ⪯ₘ complement isEmptyLang`.

We also provide the formal language definition `L_e : List Bool → Prop`
representing the set of encoded Turing machines that accept the empty language,
as described in the original proof outline.
-/

open DiagonaLean.Rice
open DiagonaLean.Halt Cslib.Turing
open DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation
open DiagonaLean.Synthetic.ReductionChain
open Classical

/-! ## Properties of `neverHaltTM` -/

/-- One step of `neverHaltTM` from state `()` produces a config still in state `()`. -/
private lemma neverHaltTM_step_eq (t : BiTape Bool) :
    neverHaltTM.step ⟨some (), t⟩ =
      some ⟨some (), (t.write none).optionMove none⟩ := by
  obtain ⟨h, l, r⟩ := t
  rfl

/-- `neverHaltTM` preserves the state `some ()` on every single step. -/
private lemma neverHaltTM_closed
    {a b : neverHaltTM.Cfg}
    (ha : a.state = some ())
    (h_step : neverHaltTM.TransitionRelation a b) :
    b.state = some () := by
  obtain ⟨_ | q, t_a⟩ := a
  · simp at ha
  · -- q : neverHaltTM.State = PUnit. Use ha : some q = some () to get q = ()
    injection ha with ha
    subst ha
    have h := neverHaltTM_step_eq t_a
    simp only [SingleTapeTM.TransitionRelation] at h_step
    rw [h, Option.some.injEq] at h_step
    subst h_step
    rfl

/-- Every config reachable from a config with state `some ()` still has state `some ()`. -/
private lemma neverHaltTM_persistent
    {a b : neverHaltTM.Cfg}
    (ha : a.state = some ())
    (h_reach : Relation.ReflTransGen neverHaltTM.TransitionRelation a b) :
    b.state = some () := by
  induction h_reach with
  | refl => exact ha
  | tail _ h_step ih => exact neverHaltTM_closed ih h_step

/-- `neverHaltTM` never halts on any input. -/
theorem neverHaltTM_not_halts (w : List Bool) : ¬ Halts neverHaltTM w := by
  rintro ⟨tape, h_halt⟩
  have := neverHaltTM_persistent (b := ⟨none, tape⟩) rfl h_halt
  simp at this

/-- `neverHaltTM` has the empty language property: it accepts nothing. -/
theorem neverHaltTM_isEmptyLang : isEmptyLang neverHaltTM := by
  intro w hAcc
  exact neverHaltTM_not_halts w ⟨BiTape.mk₁ [true], hAcc⟩

/-! ## Properties of `acceptsEmptyTM` -/

/-- On the empty input `[]`, `acceptsEmptyTM` steps directly to the halt configuration
    with output `[true]` in one step. -/
private lemma acceptsEmptyTM_step_nil :
    acceptsEmptyTM.step (SingleTapeTM.initCfg acceptsEmptyTM []) =
      some (SingleTapeTM.haltCfg acceptsEmptyTM [true]) := by
  simp [SingleTapeTM.initCfg, SingleTapeTM.haltCfg, SingleTapeTM.step,
        acceptsEmptyTM, BiTape.mk₁, BiTape.nil, BiTape.write, BiTape.optionMove,
        StackTape.mapSome]
  rfl

/-- `acceptsEmptyTM` accepts the empty input `[]`. -/
theorem acceptsEmptyTM_accepts_nil : Accepts acceptsEmptyTM [] := by
  unfold Accepts SingleTapeTM.Outputs
  exact Relation.ReflTransGen.single (show acceptsEmptyTM.TransitionRelation _ _ from by
    simp only [SingleTapeTM.TransitionRelation]
    exact acceptsEmptyTM_step_nil)

/-- `acceptsEmptyTM` does *not* have the empty language property. -/
theorem acceptsEmptyTM_not_isEmptyLang : ¬ isEmptyLang acceptsEmptyTM :=
  fun h => h [] acceptsEmptyTM_accepts_nil

/-! ## The reduction: HALT ⪯ₘ complement isEmptyLang -/

/-- The many-one reduction function from `HALT` to `complement isEmptyLang`.
    Given `(M, w)`, returns `acceptsEmptyTM` if `M` halts on `w`
    and `neverHaltTM` otherwise. Since `⪯ₘ` only requires the *existence*
    of a function (not its computability), classical choice is used. -/
noncomputable def emptyLangReduction :
    SingleTapeTM Bool × List Bool → SingleTapeTM Bool :=
  fun ⟨M, w⟩ =>
    if Halts M w then acceptsEmptyTM else neverHaltTM

/-- `HALT` many-one reduces to the complement of `isEmptyLang`. -/
theorem halt_reduces_to_complement_isEmptyLang :
    DiagonaLean.Synthetic.Notation.HALT ⪯ₘ complement isEmptyLang := by
  refine ⟨emptyLangReduction, fun ⟨M, w⟩ => ?_⟩
  simp only [DiagonaLean.Synthetic.Notation.HALT, complement, emptyLangReduction]
  constructor
  · -- Forward: Halts M w → ¬ isEmptyLang (if Halts M w then acceptsEmptyTM else neverHaltTM)
    intro h
    simp [h]
    exact acceptsEmptyTM_not_isEmptyLang
  · -- Backward: ¬ isEmptyLang (...) → Halts M w
    intro h
    by_contra h_not_halt
    simp [h_not_halt] at h
    exact h neverHaltTM_isEmptyLang

/-! ## Undecidability conclusions -/

/-- `L_e` is the language of words which represent a TM that does not accept anything. -/
def L_e (w : List Bool) : Prop :=
  ∃ (M : SingleTapeTM Bool) (_ : DecidableEq M.State),
    w = DiagonaLean.Halt.Encoding.encodeBoolTM M ∧ isEmptyLang M

/-- If `HALT` is not synthetically decidable, then neither is `isEmptyLang`.
    This follows because any decider for `isEmptyLang` can be turned into one
    for `HALT` via the reduction above. -/
theorem isEmptyLang_undecidable_of_halt
    (h_halt : ¬ SDecidable DiagonaLean.Synthetic.Notation.HALT) :
    ¬ SDecidable isEmptyLang := by
  intro h_dec
  apply h_halt
  -- SDecidable isEmptyLang → SDecidable (complement isEmptyLang) via dec_compl
  have h_dec_compl : SDecidable (complement isEmptyLang) := by
    obtain ⟨f, hf⟩ := h_dec
    refine ⟨fun x => !f x, fun x => ?_⟩
    constructor
    · intro hn
      dsimp only
      cases hfx : f x
      · rfl
      · exact absurd ((hf x).mpr hfx) hn
    · intro hfx hp
      dsimp only at hfx
      have : f x = true := (hf x).mp hp
      simp [this] at hfx
  -- HALT ⪯ₘ complement isEmptyLang + SDecidable (complement isEmptyLang) → SDecidable HALT
  exact dec_red halt_reduces_to_complement_isEmptyLang h_dec_compl
