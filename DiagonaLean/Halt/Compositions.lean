/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic).
-/

import Mathlib.Tactic
import DiagonaLean.Halt.Basic
import DiagonaLean.Halt.Helpers
import Mathlib.Data.Nat.SuccPred

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Helpers DiagonaLean.Halt.Encoding

/-! # Sequential Composition and Self-Pairing

Sequential composition of single-tape TMs and the self-pairing machine `pairSelfTM`,
which computes `w ↦ encodePair w w = w ++ [true, true] ++ w`. Together these are used
to reduce `IsHaltDecider` to `IsSelfHaltDecider` by preprocessing the input.
-/

namespace DiagonaLean.Halt.Compositions

/-- Projects a `tm1` configuration into the composed machine, mapping a halted `tm1`
configuration to the initial state of `tm2`. -/
def compCfgL (tm1 tm2 : SingleTapeTM Symbol) : tm1.Cfg → (compComputer tm1 tm2).Cfg
  | ⟨some q, t⟩ => ⟨some (Sum.inl q), t⟩
  | ⟨none, t⟩   => ⟨some (Sum.inr tm2.q₀), t⟩

/-- Projects a `tm2` configuration into the composed machine. -/
def compCfgR (tm1 tm2 : SingleTapeTM Symbol) : tm2.Cfg → (compComputer tm1 tm2).Cfg
  | ⟨st, t⟩ => ⟨Option.map Sum.inr st, t⟩

/-- A single step of `tm1` lifts to a single step of the composed machine. -/
lemma compCfgL_step {tm1 tm2 : SingleTapeTM Symbol} {a b : tm1.Cfg}
    (h : tm1.TransitionRelation a b) :
    (compComputer tm1 tm2).TransitionRelation (compCfgL tm1 tm2 a) (compCfgL tm1 tm2 b) := by
  rcases a with ⟨ _ | q, t ⟩ <;> rcases b with ⟨ _ | q', t' ⟩ <;>
    simp_all +decide [ SingleTapeTM.TransitionRelation ];
  · unfold compCfgL compComputer; aesop;
  · unfold compCfgL;
    unfold SingleTapeTM.compComputer; aesop;

/-- A single step of `tm2` lifts to a single step of the composed machine. -/
lemma compCfgR_step {tm1 tm2 : SingleTapeTM Symbol} {a b : tm2.Cfg}
    (h : tm2.TransitionRelation a b) :
    (compComputer tm1 tm2).TransitionRelation (compCfgR tm1 tm2 a) (compCfgR tm1 tm2 b) := by
  cases a ; cases b ; simp_all +decide [ compComputer ];
  cases ‹Option tm2.State› <;> cases ‹Option tm2.State› <;>
    simp_all +decide [ compCfgR, SingleTapeTM.TransitionRelation,
                        SingleTapeTM.step, compComputer ]

/-- The first phase: running `tm1` from its initial config on `w` to a halt with output
`mid` corresponds, in the composed machine, to reaching the start of `tm2`'s phase. -/
lemma comp_left_trace {tm1 tm2 : SingleTapeTM Symbol} {w mid : List Symbol}
    (h : tm1.Outputs w mid) :
    Relation.ReflTransGen (compComputer tm1 tm2).TransitionRelation
      (SingleTapeTM.initCfg (compComputer tm1 tm2) w)
      ⟨some (Sum.inr tm2.q₀), BiTape.mk₁ mid⟩ := by
  have hlift := Relation.ReflTransGen.lift (compCfgL tm1 tm2)
    (fun _ _ hab => compCfgL_step hab) _ _ h
  simpa [Function.onFun, compCfgL, SingleTapeTM.initCfg, SingleTapeTM.haltCfg, compComputer]
    using hlift

/-- The second phase: running `tm2` from `mid` to a halt with output `out` corresponds,
in the composed machine, to going from the start of `tm2`'s phase to the final halt. -/
lemma comp_right_trace {tm1 tm2 : SingleTapeTM Symbol} {mid out : List Symbol}
    (h : tm2.Outputs mid out) :
    Relation.ReflTransGen (compComputer tm1 tm2).TransitionRelation
      ⟨some (Sum.inr tm2.q₀), BiTape.mk₁ mid⟩
      (SingleTapeTM.haltCfg (compComputer tm1 tm2) out) := by
  have hlift := Relation.ReflTransGen.lift (compCfgR tm1 tm2)
    (fun _ _ hab => compCfgR_step hab) _ _ h
  simpa [Function.onFun, compCfgR, SingleTapeTM.initCfg, SingleTapeTM.haltCfg, compComputer]
    using hlift

/-- If `tm1` outputs `mid` from `w` and `tm2` outputs `out` from `mid`,
their sequential composition outputs `out` from `w`. -/
lemma compComputer_seq_outputs {tm1 tm2 : SingleTapeTM Symbol}
    {w mid out : List Symbol}
    (h1 : tm1.Outputs w mid)
    (h2 : tm2.Outputs mid out) :
    (compComputer tm1 tm2).Outputs w out :=
  (comp_left_trace h1).trans (comp_right_trace h2)

/-- States of `pairSelfTM`. `start` reads the next input symbol; `fwd1/2/3` scan right to
the write position; `ret1/2/3` scan back left to the hole; `fin2` and `finL` write the
separator and walk left to halt. -/
inductive PairSelfState where
  | start
  | fwd1 (c : Bool) | fwd2 (c : Bool) | fwd3 (c : Bool)
  | ret1 (c : Bool) | ret2 (c : Bool) | ret3 (c : Bool)
  | fin2
  | finL
  deriving DecidableEq, Fintype, Inhabited

/-- Single-tape TM computing `w ↦ encodePair w w = w ++ [true, true] ++ w`.

On each iteration the machine reads symbol `w[i]`, blanks the cell, scans right over the
remaining input and the two-blank gap to the end of the partial copy, writes `w[i]` there,
scans back to the hole, restores `w[i]`, and advances to position `i+1`.
When the head reaches a blank in state `start` the copy is complete; the machine writes
`true` into the two gap cells, walks left to the beginning, and halts. -/
def pairSelfTM : SingleTapeTM Bool := {
  State := PairSelfState
  q₀ := PairSelfState.start
  tr := fun st sym => match st with
    | .start => match sym with
      | some c => (⟨none, some .right⟩, some (.fwd1 c))
      | none   => (⟨some true, some .right⟩, some .fin2)
    | .fwd1 c => match sym with
        | some _ => (⟨sym, some .right⟩, some (.fwd1 c))
        | none   => (⟨none, some .right⟩, some (.fwd2 c))
    | .fwd2 c => (⟨sym, some .right⟩, some (.fwd3 c))
    | .fwd3 c => match sym with
        | some _ => (⟨sym, some .right⟩, some (.fwd3 c))
        | none   => (⟨some c, some .left⟩, some (.ret1 c))
    | .ret1 c => match sym with
        | some _ => (⟨sym, some .left⟩, some (.ret1 c))
        | none   => (⟨none, some .left⟩, some (.ret2 c))
    | .ret2 c => (⟨sym, some .left⟩, some (.ret3 c))
    | .ret3 c => match sym with
        | some _ => (⟨sym, some .left⟩, some (.ret3 c))
        | none   => (⟨some c, some .right⟩, some .start)
    | .fin2 => (⟨some true, some .left⟩, some .finL)
    | .finL => match sym with
        | some _ => (⟨sym, some .left⟩, some .finL)
        | none   => (⟨none, some .right⟩, none)
}

namespace PairSelf
open PairSelfState

/-- Builds a `StackTape` from a list of cells; trailing blanks are trimmed by `StackTape.cons`. -/
def ofList (l : List (Option Bool)) : StackTape Bool := l.foldr StackTape.cons StackTape.nil

@[simp]
lemma ofList_nil : ofList [] = StackTape.nil := rfl

@[simp]
lemma ofList_cons (a : Option Bool) (l : List (Option Bool)) :
    ofList (a :: l) = StackTape.cons a (ofList l) := rfl

/-- The head of `ofList l` equals the first element of `l`, defaulting to `none`. -/
lemma ofList_headD (l : List (Option Bool)) : (ofList l).head = l.headD none := by
  induction l <;> simp +decide [ *, ofList ]

/-- The tail of `ofList l` equals `ofList l.tail`. -/
lemma ofList_tail (l : List (Option Bool)) : (ofList l).tail = ofList l.tail := by
  cases l <;> simp +decide [ * ]
  rfl

/-- Appending a trailing `none` to `ofList l` is a no-op. -/
lemma ofList_append_none (l : List (Option Bool)) : ofList (l ++ [none]) = ofList l := by
  induction l <;> aesop

/-- A `pairSelfTM` configuration in list form: `left` are the cells to the left of the head
(nearest first), `right` are the cells from the head rightwards. -/
def cfgOf (q : PairSelfState) (left right : List (Option Bool)) : pairSelfTM.Cfg :=
  ⟨some q, ⟨right.headD none, ofList left, ofList right.tail⟩⟩

/-- A rightward step. -/
lemma step_right {q q' : PairSelfState} {wr : Option Bool} {left right : List (Option Bool)}
    (h : pairSelfTM.tr q (right.headD none) = (⟨wr, some Turing.Dir.right⟩, some q')) :
    pairSelfTM.TransitionRelation (cfgOf q left right) (cfgOf q' (wr :: left) right.tail) := by
  unfold cfgOf; simp +decide [ *, SingleTapeTM.TransitionRelation ]
  cases right <;> simp_all +decide
  · cases q <;> cases wr <;> cases h; all_goals simp [StackTape.nil]; exact ⟨rfl, rfl⟩
  · cases ‹List ( Option Bool )› <;>
    simp_all +decide [ BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight ]
    simp [StackTape.nil]
    exact ⟨rfl, rfl⟩
    rfl

/-- A leftward step. -/
lemma step_left {q q' : PairSelfState} {wr : Option Bool} {left right : List (Option Bool)}
    (h : pairSelfTM.tr q (right.headD none) = (⟨wr, some Turing.Dir.left⟩, some q')) :
    pairSelfTM.TransitionRelation (cfgOf q left right)
      (cfgOf q' left.tail (left.headD none :: wr :: right.tail)) := by
  unfold cfgOf; simp +decide [ *, SingleTapeTM.TransitionRelation ]
  cases left <;> cases right <;>
    simp_all +decide [ BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft ]
  all_goals first | exact ⟨rfl, rfl⟩ | rfl

/-- Scans rightwards over a block of data cells, preserving their contents. -/
lemma scan_right {q : PairSelfState}
    (hq : ∀ b : Bool, pairSelfTM.tr q (some b) = (⟨some b, some Turing.Dir.right⟩, some q))
    (pre : List Bool) (left right : List (Option Bool)) :
    Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf q left (pre.map some ++ right))
      (cfgOf q (pre.reverse.map some ++ left) right) := by
  induction' pre with a pre ih generalizing left right
  · rfl
  · simp only [List.reverse_cons, List.map_append, List.append_assoc]
    exact Relation.ReflTransGen.head (step_right (hq a)) (ih (some a :: left) right)

/-- Scans leftwards over a block of data cells, preserving their contents, stopping one cell
past the block. -/
lemma scan_left {q : PairSelfState}
    (hq : ∀ b : Bool, pairSelfTM.tr q (some b) = (⟨some b, some Turing.Dir.left⟩, some q))
    (pre : List Bool) (a : Bool) (left right : List (Option Bool)) :
    Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf q (pre.map some ++ left) (some a :: right))
      (cfgOf q left.tail (left.headD none :: pre.reverse.map some ++ some a :: right)) := by
  induction' pre with b pre ih generalizing a left right
  · exact Relation.ReflTransGen.single (step_left (hq a))
  · simp only [List.reverse_cons, List.map_append, List.append_assoc, List.map_cons, List.map_nil,
                  List.cons_append, List.nil_append]
    exact Relation.ReflTransGen.head (step_left (hq a)) (ih b left (some a :: right))

/-- The prefix `w[0..i-1]` in head-first (reversed) order, as the left cells at iteration `i`. -/
def startLeft (w : List Bool) (i : ℕ) : List (Option Bool) := (w.take i).reverse.map some

/-- The cells from the head rightwards at iteration `i`:
`w[i..]`, the two-blank gap, then the partial copy `w[0..i-1]`. -/
def startRight (w : List Bool) (i : ℕ) : List (Option Bool) :=
  (w.drop i).map some ++ [none, none] ++ (w.take i).map some

/-- Writes symbol `c` at the end of the partial copy and scans back left over it to the gap. -/
lemma run_deposit (c : Bool) (zr : List Bool) (rest : List (Option Bool)) :
    Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf (.fwd3 c) (zr.map some ++ none :: rest) [])
      (cfgOf (.ret1 c) rest (none :: zr.reverse.map some ++ [some c])) := by
  cases zr with
  | nil =>
    exact Relation.ReflTransGen.single (step_left rfl)
  | cons z zs =>
    simp only [List.map_cons, List.cons_append, List.reverse_cons, List.map_append,
                  List.append_assoc, List.map_nil, List.nil_append]
    exact Relation.ReflTransGen.head (step_left rfl)
      (scan_left (fun _ => rfl) zs z (none :: rest) [some c])

/-- Scans back left over the remaining input tail to the hole, restores `c`, and steps right
to the start of the next iteration. -/
lemma run_restore (c : Bool) (br : List Bool) (LA M : List (Option Bool)) :
  Relation.ReflTransGen pairSelfTM.TransitionRelation
    (cfgOf (.ret2 c) (br.map some ++ none :: LA) (none :: none :: M))
    (cfgOf .start (some c :: LA) (br.reverse.map some ++ none :: none :: M)) := by
  induction' br with d br ih generalizing LA M;
  · convert Relation.ReflTransGen.head _ _;
    exact cfgOf ( ret3 c ) LA ( none :: none :: none :: M );
    · exact step_left rfl;
    · convert Relation.ReflTransGen.single _;
      exact step_right ( by cases c <;> rfl );
  · have h_step_left : Relation.ReflTransGen pairSelfTM.TransitionRelation (cfgOf (ret2 c)
    (some d :: br.map some ++ none :: LA) (none :: none :: M)) (cfgOf (ret3 c)
      (br.map some ++ none :: LA) (some d :: none :: none :: M)) := by
      apply Relation.ReflTransGen.single
      exact step_left rfl
    have h_scan_left : Relation.ReflTransGen pairSelfTM.TransitionRelation (cfgOf (ret3 c)
      (br.map some ++ none :: LA) (some d :: none :: none :: M)) (cfgOf (ret3 c) LA
        (none :: br.reverse.map some ++ some d :: none :: none :: M)) := by
      apply scan_left
      aesop
    have h_step_right : Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf (ret3 c) LA (none :: br.reverse.map some ++ some d :: none :: none :: M))
      (cfgOf start (some c :: LA) (br.reverse.map some ++ some d :: none :: none :: M)) := by
      apply Relation.ReflTransGen.single
      exact step_right (by cases c <;> rfl)
    simpa using h_step_left.trans (h_scan_left.trans h_step_right)

/-- Advances from the start of iteration `i` to the start of iteration `i+1`. -/
lemma macro_step (w : List Bool) (i : ℕ) (hi : i < w.length) :
    Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf .start (startLeft w i) (startRight w i))
      (cfgOf .start (startLeft w (i+1)) (startRight w (i+1))) := by
  convert Relation.ReflTransGen.trans ( Relation.ReflTransGen.head _ _ ) _ using 1
  exact cfgOf (.fwd1 ( w[i]! )) ( none :: startLeft w i )
    ( w.drop ( i + 1 ) |> List.map some |> List.append <| none :: none ::
      ( w.take i |> List.map some ) )
  exact cfgOf ( .fwd1 w[i]! ) ( ( w.drop ( i + 1 ) |> List.reverse |> List.map some ) ++
    none :: startLeft w i ) ( none :: none :: List.map some ( List.take i w ) )
  · convert step_right _ using 1
    rotate_left
    exact PairSelfState.fwd1 ( w[i]! )
    exact none
    all_goals unfold startRight
    all_goals first
      | rfl
      | aesop
  · convert scan_right _ _ _ _ using 1
    all_goals first
      | rfl
      | (intro b; rfl)
  · convert Relation.ReflTransGen.trans ( Relation.ReflTransGen.head _ _ ) _ using 1
    exact cfgOf ( .fwd2 w[i]! ) ( none :: List.map some ( List.drop ( i + 1 ) w ).reverse ++
      none :: startLeft w i ) ( none :: List.map some ( List.take i w ) )
    exact cfgOf ( .fwd3 w[i]! ) ( none :: none :: List.map some
      ( List.drop ( i + 1 ) w ).reverse ++
      none :: startLeft w i ) ( List.map some ( List.take i w ) )
    · convert step_right _ using 1
      all_goals first
        | rfl
    · convert Relation.ReflTransGen.single _ using 1
      exact step_right rfl
    · convert Relation.ReflTransGen.trans ( scan_right _ _ _ _ ) _ using 1
      rotate_left
      exact .fwd3 w[i]!
      rotate_left
      exact List.take i w
      exact none :: none :: List.map some ( List.drop ( i + 1 ) w ).reverse ++ none :: startLeft w i
      exact [ ]
      · convert run_deposit w[i]! ( List.reverse ( List.take i w ) ) ( none :: List.map some
        ( List.drop ( i + 1 ) w ).reverse ++ none :: startLeft w i )
          |> Relation.ReflTransGen.trans <| Relation.ReflTransGen.head _ _ using 1
        simp
        exact cfgOf ( PairSelfState.ret2 w[i]! ) ( List.map some ( List.drop ( i + 1 ) w ).reverse
          ++ none :: startLeft w i ) ( none :: none :: List.map some
            ( List.take i w ).reverse.reverse ++ [ some w[i]! ] )
        · convert step_left _ using 1
          unfold pairSelfTM
          all_goals first
            | rfl
        · convert (run_restore w[i]! ( List.reverse ( List.drop ( i + 1 ) w ) ) ( startLeft w i )
          ( List.map some ( List.take i w ).reverse.reverse ++ [ some w[i]! ] )) using 1
          simp +decide [ startLeft ]
          cases h : w[i]?
          · grind
          · simp [startLeft, startRight, List.reverse_reverse, List.take_add_one]
            grind
      · simp +decide [ cfgOf ]
      · aesop

/-- After `i` iterations the machine is at the start of iteration `i`. -/
lemma loop (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf .start (startLeft w 0) (startRight w 0))
      (cfgOf .start (startLeft w i) (startRight w i)) := by
  induction i with
  | zero => exact .refl
  | succ k ih => exact (ih (by omega)).trans (macro_step w k (by omega))

/-- The initial configuration equals `cfgOf .start (startLeft w 0) (startRight w 0)`. -/
lemma init_eq (w : List Bool) :
    SingleTapeTM.initCfg pairSelfTM w = cfgOf .start (startLeft w 0) (startRight w 0) := by
  cases w <;> simp +decide [ initCfg ];
  · rfl;
  · rename_i h t; simp [BiTape.mk₁, BiTape.mk₁, startLeft, startRight];
    congr;
    induction t <;> simp_all +decide [ StackTape.mapSome, ofList ];
    · congr;
    · congr;
      simp +decide [ ← ‹_› ]

/-- From the end of copying, writes the separator and walks left to produce the halting
configuration with output `encodePair w w`. -/
lemma finalize (w : List Bool) :
    Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf .start (startLeft w w.length) (startRight w w.length))
      (SingleTapeTM.haltCfg pairSelfTM (encodePair w w)) := by
  have h_step_right : pairSelfTM.TransitionRelation (cfgOf .start (startLeft w w.length)
    (startRight w w.length)) (cfgOf .fin2 (some true :: (startLeft w w.length))
      (startRight w w.length).tail) := by
    convert step_right _;
    unfold startRight; aesop;
  have h_step_left : pairSelfTM.TransitionRelation (cfgOf .fin2 (some true ::
    (startLeft w w.length)) (startRight w w.length).tail) (cfgOf .finL (startLeft w w.length)
      (some true :: some true :: (startRight w w.length).tail.tail)) := by
    unfold startRight; aesop;
  have h_scan_left : Relation.ReflTransGen pairSelfTM.TransitionRelation (cfgOf .finL
    (startLeft w w.length) (some true :: some true :: (startRight w w.length).tail.tail))
      (cfgOf .finL [] (none :: (encodePair w w).map some)) := by
    have h_scan_left : ∀ (pre : List Bool) (a : Bool) (left : List (Option Bool))
      (right : List (Option Bool)), Relation.ReflTransGen pairSelfTM.TransitionRelation
      (cfgOf .finL (pre.map some ++ left) (some a :: right)) (cfgOf .finL left.tail
        (left.headD none :: pre.reverse.map some ++ some a :: right)) := by
      intros pre a left right
      apply scan_left;
      aesop;
    convert h_scan_left ( List.reverse w ) true []
      ( some true :: ( startRight w w.length ).tail.tail ) using 1;
    · unfold startLeft; aesop;
    · simp +decide [ encodePair, startRight ];
  convert h_step_right |> fun h => Relation.ReflTransGen.head h <| h_step_left |>
    fun h => Relation.ReflTransGen.head h <| h_scan_left.trans <|
      Relation.ReflTransGen.single _ using 1;
  unfold SingleTapeTM.haltCfg;
  unfold cfgOf; simp +decide [ BiTape.mk₁ ] ;
  cases h : encodePair w w <;> simp_all +decide;
  · unfold encodePair at h; aesop;
  · unfold pairSelfTM; simp +decide [ SingleTapeTM.TransitionRelation ] ;
    unfold BiTape.write; simp +decide [ BiTape.optionMove ] ;
    unfold BiTape.move; simp +decide [ BiTape.moveRight ] ;
    exact ⟨ rfl, by
      unfold ofList; simp +decide [ StackTape.mapSome ] ;
      induction ‹List Bool› <;> simp +decide [ *, StackTape.cons ];
      · rfl;
      · rename_i k hk ih; exact (by
        exact List.recOn hk rfl fun _ _ ih => by simp +decide [ *, StackTape.cons ] ;); ⟩
end PairSelf

/-- `pairSelfTM` outputs `encodePair w w` on input `w`. -/
theorem pairSelfTM_outputs (w : List Bool) : pairSelfTM.Outputs w (encodePair w w) := by
  have := (PairSelf.loop w w.length (le_refl _)).trans (PairSelf.finalize w)
  rwa [← PairSelf.init_eq w] at this

/-- `pairSelfTM` halts on every input. -/
theorem pairSelfTM_halts (w : List Bool) : Halts pairSelfTM w :=
  ⟨_, pairSelfTM_outputs w⟩

omit [Inhabited Symbol] [Fintype Symbol] in
/-- `BiTape.mk₁` is injective on lists. -/
private lemma mk₁_injective {l l' : List Symbol} (h : BiTape.mk₁ l = BiTape.mk₁ l') : l = l' := by
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b t => simp [BiTape.mk₁, BiTape.nil] at h
  | cons a s =>
    cases l' with
    | nil => simp [BiTape.mk₁, BiTape.nil] at h
    | cons b t =>
      simp only [BiTape.mk₁, BiTape.mk.injEq, Option.some.injEq] at h
      obtain ⟨hab, _, hst⟩ := h
      subst hab
      have : s = t := by
        have := congrArg StackTape.toList hst
        simpa [StackTape.mapSome, List.map_inj_right] using this
      subst this; rfl

/-- The transition relation of `pairSelfTM` is deterministic. -/
lemma pairSelfTM_det {a b c : pairSelfTM.Cfg}
    (hab : pairSelfTM.TransitionRelation a b) (hac : pairSelfTM.TransitionRelation a c) :
    b = c := by
  simp only [SingleTapeTM.TransitionRelation] at hab hac
  rw [hab] at hac
  exact Option.some.injEq _ _ |>.mp hac

/-- Any two halting configurations reachable from the same starting configuration are equal. -/
lemma pairSelfTM_reflTransGen_out_unique {a b c : pairSelfTM.Cfg}
    (hb : b.state = none) (hc : c.state = none)
    (hab : Relation.ReflTransGen pairSelfTM.TransitionRelation a b)
    (hac : Relation.ReflTransGen pairSelfTM.TransitionRelation a c) :
    b = c := by
  have diamond := reflTransGen_diamond (r := pairSelfTM.TransitionRelation) pairSelfTM_det hab hac
  rcases diamond with h | h
  · rcases h.cases_head with h_eq | ⟨x, h1, _⟩
    · exact h_eq
    · exfalso
      obtain ⟨bs, bt⟩ := b
      subst hb
      simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h1
  · rcases h.cases_head with h_eq | ⟨x, h1, _⟩
    · exact h_eq.symm
    · exfalso
      obtain ⟨cs, ct⟩ := c
      subst hc
      simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at h1

/-- `pairSelfTM` halts on every input, and its unique output on `w` is `encodePair w w`. -/
theorem pairSelfTM_correct (w : List Bool) :
    Halts pairSelfTM w ∧ ∀ out, pairSelfTM.Outputs w out ↔ out = encodePair w w := by
  refine ⟨pairSelfTM_halts w, fun out => ⟨fun hOut => ?_, fun hEq => hEq ▸ pairSelfTM_outputs w⟩⟩
  have h := pairSelfTM_reflTransGen_out_unique (b := SingleTapeTM.haltCfg pairSelfTM out)
    (c := SingleTapeTM.haltCfg pairSelfTM (encodePair w w)) rfl rfl hOut (pairSelfTM_outputs w)
  have : BiTape.mk₁ out = BiTape.mk₁ (encodePair w w) := by
    simpa [SingleTapeTM.haltCfg] using congrArg SingleTapeTM.Cfg.BiTape h
  exact mk₁_injective this

end DiagonaLean.Halt.Compositions
