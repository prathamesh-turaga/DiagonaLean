/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic).
-/

import DiagonaLean.Halt.Undecidable
import DiagonaLean.Synthetic.Undecidability

/-! # Universal Turing Machines
A universal Turing machine is a single machine that can simulate every other machine:
given (an encoding of) a machine `tm` together with an input `w`, it halts exactly when
`tm` halts on `w`, and produces exactly the output that `tm` produces on `w`.
This file formalises that notion for Cslib's `SingleTapeTM`, reusing the
Hopcroft-Ullman style encoding `encodeBoolTM` of `DiagonaLean.Halt.Encoding` and the
pairing `encodePair` already used to state the halting problem in `DiagonaLean.Halt`.
## Main definitions
* `instanceEncoding`: the string `⟨tm, w⟩` fed to a universal machine.
* `IsWeaklyUniversalWrt` / `IsUniversalWrt`: universality relative to an arbitrary way
  `pair` of packaging a machine encoding and an input into a single string.
* `IsWeaklyUniversal` / `IsUniversal`: the same notions for the standard pairing
  `encodePair`. A weakly universal machine reproduces the halting behaviour of every
  machine; a universal machine reproduces its input/output behaviour as well.
* `pairDelim`: an unambiguous alternative pairing (`encodePair` is ambiguous, see
  `encodePair_not_inj`). `DiagonaLean.Foundations.UniversalTuringMachine.Translation`
  shows that the choice of pairing is immaterial once the two can be translated into
  each other by a machine.
* `IsHaltDeciderFor`: a machine deciding, for a *fixed* machine `U`, whether `U` halts
  on a given string.
* `UniversalHaltProblem`: the halting problem of a fixed machine, as a decision problem
  about strings.
## Main results
* `outputs_unique`: a single-tape TM has at most one output on a given input, so the
  requirement placed on a universal machine is consistent.
* `IsUniversalWrt.behaviour_congr`: any two universal machines have the same halting and
  input/output behaviour on encoded instances.
* `IsWeaklyUniversalWrt.exists_halts` and `IsWeaklyUniversalWrt.exists_not_halts`: a
  universal machine halts on some inputs and diverges on others; in particular it is not
  total.
* `not_exists_haltDeciderFor_of_isWeaklyUniversal`: the halting problem *of a single
  universal machine* is already undecidable.
* `halt_manyOneReduces_universalHalt`: `HALT` many-one reduces to the halting problem of
  any weakly universal machine.
Universality is formalised here as a specification; this file does not construct a
concrete machine satisfying it, so all results about universal machines are conditional
on being given one.
## References
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/
@[expose] public section
open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
     DiagonaLean.Halt.Helpers DiagonaLean.Synthetic.Definitions
namespace DiagonaLean.Foundations.UniversalTuringMachine
section Determinism
variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
/-- A halted configuration has no successor configuration. -/
lemma not_transitionRelation_of_halted {tm : SingleTapeTM Symbol}
    {t : BiTape Symbol} {c : tm.Cfg} :
    ¬ tm.TransitionRelation (⟨none, t⟩ : tm.Cfg) c := by
  simp [SingleTapeTM.TransitionRelation]
/-- Nothing but a halted configuration itself is reachable from a halted configuration. -/
lemma eq_of_reflTransGen_halted {tm : SingleTapeTM Symbol}
    {t : BiTape Symbol} {c : tm.Cfg}
    (h : Relation.ReflTransGen tm.TransitionRelation ⟨none, t⟩ c) :
    c = ⟨none, t⟩ := by
  rcases h.cases_head with h | ⟨d, hstep, -⟩
  · exact h.symm
  · exact absurd hstep not_transitionRelation_of_halted
/-- The transition relation of a single-tape TM is deterministic. -/
lemma transitionRelation_deterministic {tm : SingleTapeTM Symbol} {a b c : tm.Cfg}
    (hab : tm.TransitionRelation a b) (hac : tm.TransitionRelation a c) : b = c := by
  grind
omit [Inhabited Symbol] [Fintype Symbol] in
/-- `BiTape.mk₁` is injective: distinct lists give distinct initial tapes. -/
lemma mk₁_injective : Function.Injective (BiTape.mk₁ : List Symbol → BiTape Symbol) := by
  intro l₁ l₂ h
  cases l₁ with
  | nil => cases l₂ with
    | nil => rfl
    | cons b t => simp [BiTape.mk₁, BiTape.nil] at h
  | cons a s => cases l₂ with
    | nil => simp [BiTape.mk₁, BiTape.nil] at h
    | cons b t =>
      simp only [BiTape.mk₁, BiTape.mk.injEq, Option.some.injEq] at h
      obtain ⟨hab, -, hst⟩ := h
      have hmap : (s.map some) = (t.map some) := congrArg StackTape.toList hst
      exact congrArg₂ List.cons hab
        (List.map_injective_iff.mpr (Option.some_injective Symbol) hmap)
/-- A single-tape TM produces at most one output on a given input. -/
theorem outputs_unique {tm : SingleTapeTM Symbol} {w v₁ v₂ : List Symbol}
    (h₁ : tm.Outputs w v₁) (h₂ : tm.Outputs w v₂) : v₁ = v₂ := by
  have hcfg : (tm.haltCfg v₁) = tm.haltCfg v₂ := by
    rcases reflTransGen_diamond (fun {_ _ _} => transitionRelation_deterministic) h₁ h₂ with h | h
    · exact (eq_of_reflTransGen_halted h).symm
    · exact eq_of_reflTransGen_halted h
  exact mk₁_injective (congrArg SingleTapeTM.Cfg.BiTape hcfg)
/-- A halting single-tape TM halts with a unique final tape. -/
theorem halt_tape_unique {tm : SingleTapeTM Symbol} {w : List Symbol}
    {t₁ t₂ : BiTape Symbol}
    (h₁ : Relation.ReflTransGen tm.TransitionRelation (tm.initCfg w) ⟨none, t₁⟩)
    (h₂ : Relation.ReflTransGen tm.TransitionRelation (tm.initCfg w) ⟨none, t₂⟩) :
    t₁ = t₂ := by
  rcases reflTransGen_diamond (fun {_ _ _} => transitionRelation_deterministic) h₁ h₂ with h | h
  · exact (congrArg SingleTapeTM.Cfg.BiTape (eq_of_reflTransGen_halted h)).symm
  · exact congrArg SingleTapeTM.Cfg.BiTape (eq_of_reflTransGen_halted h)
/-- If a machine outputs something on `w`, then it halts on `w`. -/
lemma halts_of_outputs {tm : SingleTapeTM Symbol} {w v : List Symbol}
    (h : tm.Outputs w v) : Halts tm w :=
  ⟨BiTape.mk₁ v, h⟩
end Determinism
/-! ## The notion of a universal machine -/
/-- A way of packaging the encoding of a machine together with an input string into a
single input string for a universal machine. -/
abbrev InstanceEncoding := List Bool → List Bool → List Bool
/-- The pairing `encodePair` used to state the halting problem in `DiagonaLean.Halt` is
ambiguous on machine encodings containing the separator `[true, true]`: the paired string
does not determine the two components. -/
theorem encodePair_not_inj :
    ∃ a₁ b₁ a₂ b₂ : List Bool,
      encodePair a₁ b₁ = encodePair a₂ b₂ ∧ (a₁, b₁) ≠ (a₂, b₂) :=
  ⟨[], [true, true], [true, true], [], rfl, by decide⟩
/-- A self-delimiting pairing: every bit of the machine encoding is doubled, and the
marker `[false, true]` — the only pair of adjacent unequal bits in the doubled prefix —
separates it from the input. Unlike `encodePair`, this pairing is unambiguous for
arbitrary machine encodings; see `pairDelim_inj`. -/
def pairDelim (a b : List Bool) : List Bool :=
  (a.flatMap fun x => [x, x]) ++ [false, true] ++ b
/-- `pairDelim` is unambiguous: the machine encoding and the input can be read back off
the paired string. -/
theorem pairDelim_inj : ∀ {a₁ b₁ a₂ b₂ : List Bool},
    pairDelim a₁ b₁ = pairDelim a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
  intro a₁
  induction a₁ with
  | nil =>
    intro b₁ a₂ b₂ h
    cases a₂ with
    | nil => simpa [pairDelim] using h
    | cons y t => cases y <;> simp [pairDelim] at h
  | cons x s ih =>
    intro b₁ a₂ b₂ h
    cases a₂ with
    | nil => cases x <;> simp [pairDelim] at h
    | cons y t =>
      simp only [pairDelim, List.flatMap_cons, List.cons_append, List.append_assoc,
        List.cons.injEq] at h
      obtain ⟨hxy, -, hrest⟩ := h
      obtain ⟨hst, hb⟩ := ih (by simpa [pairDelim] using hrest)
      exact ⟨by rw [hxy, hst], hb⟩
/-- The string `⟨tm, w⟩` handed to a universal machine: the Hopcroft-Ullman encoding of
`tm`, paired with the input `w`. -/
noncomputable def instanceEncoding (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (w : List Bool) : List Bool :=
  encodePair (encodeBoolTM tm) w
/-- `U` is *weakly universal* with respect to the pairing `pair` if, for every machine
`tm` and input `w`, it halts on `pair ⟪tm⟫ w` exactly when `tm` halts on `w`. -/
def IsWeaklyUniversalWrt (pair : InstanceEncoding) (U : SingleTapeTM Bool) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool),
    Halts U (pair (encodeBoolTM tm) w) ↔ Halts tm w
/-- `U` is *universal* with respect to the pairing `pair` if, for every machine `tm` and
input `w`, it halts on `pair ⟪tm⟫ w` exactly when `tm` halts on `w`, and it outputs `v`
on `pair ⟪tm⟫ w` exactly when `tm` outputs `v` on `w`. -/
def IsUniversalWrt (pair : InstanceEncoding) (U : SingleTapeTM Bool) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool),
    (Halts U (pair (encodeBoolTM tm) w) ↔ Halts tm w) ∧
      ∀ v : List Bool, (U.Outputs (pair (encodeBoolTM tm) w) v ↔ tm.Outputs w v)
/-- A weakly universal machine: one reproducing the halting behaviour of every machine,
on inputs encoded by the standard pairing `encodePair`. -/
abbrev IsWeaklyUniversal (U : SingleTapeTM Bool) : Prop :=
  IsWeaklyUniversalWrt encodePair U
/-- A universal machine: one reproducing the halting *and* the input/output behaviour of
every machine, on inputs encoded by the standard pairing `encodePair`. -/
abbrev IsUniversal (U : SingleTapeTM Bool) : Prop :=
  IsUniversalWrt encodePair U
variable {pair : InstanceEncoding} {U : SingleTapeTM Bool}
/-- A universal machine is weakly universal. -/
theorem IsUniversalWrt.weakly (hU : IsUniversalWrt pair U) : IsWeaklyUniversalWrt pair U :=
  fun tm _ w => (hU tm w).1
/-- Halting of a universal machine on `pair ⟪tm⟫ w` is halting of `tm` on `w`. -/
theorem IsUniversalWrt.halts_iff (hU : IsUniversalWrt pair U)
    (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool) :
    Halts U (pair (encodeBoolTM tm) w) ↔ Halts tm w := (hU tm w).1
/-- The output of a universal machine on `pair ⟪tm⟫ w` is the output of `tm` on `w`. -/
theorem IsUniversalWrt.outputs_iff (hU : IsUniversalWrt pair U)
    (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w v : List Bool) :
    U.Outputs (pair (encodeBoolTM tm) w) v ↔ tm.Outputs w v := (hU tm w).2 v
/-- Halting of a universal machine on the encoded instance `⟨tm, w⟩` is halting of `tm`
on `w`. -/
theorem IsUniversal.halts_instanceEncoding_iff (hU : IsUniversal U)
    (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool) :
    Halts U (instanceEncoding tm w) ↔ Halts tm w := (hU tm w).1
/-- The output of a universal machine on the encoded instance `⟨tm, w⟩` is the output of
`tm` on `w`. -/
theorem IsUniversal.outputs_instanceEncoding_iff (hU : IsUniversal U)
    (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w v : List Bool) :
    U.Outputs (instanceEncoding tm w) v ↔ tm.Outputs w v := (hU tm w).2 v
/-- Any two universal machines have the same behaviour on encoded instances. -/
theorem IsUniversalWrt.behaviour_congr {U₁ U₂ : SingleTapeTM Bool}
    (h₁ : IsUniversalWrt pair U₁) (h₂ : IsUniversalWrt pair U₂)
    (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool) :
    (Halts U₁ (pair (encodeBoolTM tm) w) ↔ Halts U₂ (pair (encodeBoolTM tm) w)) ∧
      ∀ v : List Bool,
        (U₁.Outputs (pair (encodeBoolTM tm) w) v ↔ U₂.Outputs (pair (encodeBoolTM tm) w) v) :=
  ⟨((h₁ tm w).1).trans ((h₂ tm w).1).symm,
    fun v => ((h₁ tm w).2 v).trans (((h₂ tm w).2 v).symm)⟩
/-! ## A universal machine is neither everywhere-halting nor everywhere-diverging -/
/-- A machine that never halts: whatever it reads, it blanks the cell and stays in its
single state. -/
def loopTM : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨none, none⟩, some ())
instance : DecidableEq loopTM.State := fun _ _ => isTrue rfl
/-- Every configuration reachable in `loopTM` is still in its (unique) state. -/
private lemma loopTM_state_persists {c d : loopTM.Cfg}
    (hc : c.state = some ())
    (h : Relation.ReflTransGen loopTM.TransitionRelation c d) :
    d.state = some () := by
  induction h with
  | refl => exact hc
  | @tail b e _ hstep ih =>
    obtain ⟨_ | q, t⟩ := b
    · simp [SingleTapeTM.TransitionRelation] at hstep
    · simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at hstep
      grind [loopTM]
/-- `loopTM` halts on no input. -/
theorem not_halts_loopTM (w : List Bool) : ¬ Halts loopTM w := by
  rintro ⟨t, h⟩
  have := loopTM_state_persists (c := loopTM.initCfg w) rfl h
  simp at this
/-- A machine that halts immediately, on every input. -/
def haltTM : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ x := (⟨x, none⟩, none)
instance : DecidableEq haltTM.State := fun _ _ => isTrue rfl
/-- `haltTM` halts on every input. -/
theorem halts_haltTM (w : List Bool) : Halts haltTM w :=
  ⟨BiTape.mk₁ w, Relation.ReflTransGen.single (by
    cases w <;> rfl)⟩
/-- A weakly universal machine halts on at least one input. -/
theorem IsWeaklyUniversalWrt.exists_halts (hU : IsWeaklyUniversalWrt pair U) :
    ∃ x : List Bool, Halts U x :=
  ⟨pair (encodeBoolTM haltTM) [], (hU haltTM []).mpr (halts_haltTM [])⟩
/-- A weakly universal machine diverges on at least one input: it is not a total machine. -/
theorem IsWeaklyUniversalWrt.exists_not_halts (hU : IsWeaklyUniversalWrt pair U) :
    ∃ x : List Bool, ¬ Halts U x :=
  ⟨pair (encodeBoolTM loopTM) [], fun h => not_halts_loopTM [] ((hU loopTM []).mp h)⟩
/-! ## Undecidability of the halting problem of a universal machine -/
/-- `D` decides the halting problem of the fixed machine `U` if, on every input string
`x`, it outputs `[true]` when `U` halts on `x` and `[false]` when it does not. -/
def IsHaltDeciderFor (U D : SingleTapeTM Bool) : Prop :=
  ∀ x : List Bool, (Halts U x → D.Outputs x [true]) ∧ (¬ Halts U x → D.Outputs x [false])
/-- A machine deciding the halting problem of a weakly universal machine decides the
general halting problem. -/
theorem isHaltDecider_of_isHaltDeciderFor {D : SingleTapeTM Bool}
    (hU : IsWeaklyUniversal U) (hD : IsHaltDeciderFor U D) : IsHaltDecider D := by
  intro tm _ w
  refine ⟨fun h => (hD _).1 ((hU tm w).mpr h), fun h => (hD _).2 ?_⟩
  exact fun h' => h ((hU tm w).mp h')
/-- The halting problem of a single weakly universal machine is undecidable. -/
theorem not_exists_haltDeciderFor_of_isWeaklyUniversal (hU : IsWeaklyUniversal U) :
    ¬ ∃ D : SingleTapeTM Bool, IsHaltDeciderFor U D := by
  rintro ⟨D, hD⟩
  exact DiagonaLean.Halt.Undecidable.halt_undecidable
    ⟨D, isHaltDecider_of_isHaltDeciderFor hU hD⟩
/-- The halting problem of the fixed machine `U`, as a decision problem about strings. -/
def UniversalHaltProblem (U : SingleTapeTM Bool) : List Bool → Prop := fun x => Halts U x
/-- The halting problem many-one reduces to the halting problem of any weakly universal
machine: an instance `(M, w)` is mapped to the encoded instance `⟪ M ⟫ w`. -/
theorem halt_manyOneReduces_universalHalt (hU : IsWeaklyUniversal U) :
    Synthetic.Notation.HALT ⪯ₘ UniversalHaltProblem U := by
  classical
  exact ⟨fun p => instanceEncoding p.1 p.2, fun p => (hU p.1 p.2).symm⟩
end DiagonaLean.Foundations.UniversalTuringMachine
