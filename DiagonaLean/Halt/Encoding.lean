/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Shashank Pandey
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

open Cslib.Turing SingleTapeTM

/-! # Encoding of Turing Machines as Binary Strings

We define an encoding of single-tape Turing machines over `Bool` as binary strings
(`List Bool`), following the Hopcroft-Ullman encoding (§9.3 of [HopcroftMotwaniUllman2006]).

States, tape symbols, and head directions are assigned unary indices. A transition
`δ(q, x) = (q', sym, dir)` is encoded as five unary fields separated by `[true]` bits.
Transitions are separated by `[true, true]`. The full machine encoding prepends the initial
state index and transition count, separated by longer `true` sequences.

All the encodings are invertible and injective.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.Halt.Encoding

/-- Encodes a natural number `n` as a unary string of `n` `false` bits. -/
def encodeNat (n : ℕ) : List Bool := List.replicate n false

@[simp]
lemma encodeNat_zero : encodeNat 0 = [] := rfl

@[simp]
lemma encodeNat_succ (n : ℕ) :
    encodeNat (n + 1) = false :: encodeNat n := by simp [encodeNat, List.replicate_succ]

/-- Decodes a unary string back to a natural number. Returns `none` if the string contains
any `true` bits. -/
def decodeNat (l : List Bool) : Option ℕ :=
  if l.all (· == false) then some l.length
  else none

@[simp]
private lemma decodeNat_encodeNat (n : ℕ) : decodeNat (encodeNat n) = some n := by
  simp [decodeNat, encodeNat, List.all_replicate, List.length_replicate]

/-- Encodes a pair of binary strings as a single string, separating them with `[true, true]`.
Requires `a` to contain no `true` bits for the encoding to be unambiguous. -/
def encodePair (a b : List Bool) : List Bool :=
  a ++ [true, true] ++ b

/-- Decodes a pair of binary strings encoded by `encodePair`. -/
def decodePair (l : List Bool) : Option (List Bool × List Bool) :=
  let (a, rest) := l.span (· == false)
  match rest with
  | true :: true :: b => some (a, b)
  | _                 => none

private lemma span_encodePair (a b : List Bool) (ha : ∀ x ∈ a, x = false) :
    (encodePair a b).span (· == false) = (a, true :: true :: b) := by
  have hp : ∀ x ∈ a, (x == false) = true := fun x hx => by simp [ha x hx]
  rw [List.span_eq_takeWhile_dropWhile, encodePair, List.append_assoc,
      List.takeWhile_append_of_pos hp, List.dropWhile_append_of_pos hp]
  simp

@[simp]
private lemma decodePair_encodePair (a b : List Bool) (ha : ∀ x ∈ a, x = false) :
    decodePair (encodePair a b) = some (a, b) := by
  unfold decodePair
  rw [span_encodePair a b ha]

/-- `encodePair` is injective on pairs whose first component contains no `true` bits. -/
theorem encodePair_injective :
    Function.Injective
      (fun p : {a : List Bool // ∀ x ∈ a, x = false} × List Bool =>
        encodePair p.1.1 p.2) := by
  intro p q h
  have hp := decodePair_encodePair p.1.1 p.2 p.1.2
  have hq := decodePair_encodePair q.1.1 q.2 q.1.2
  simp only at h
  rw [h, hq, Option.some_inj, Prod.mk.injEq] at hp
  exact Prod.ext (Subtype.ext hp.1.symm) hp.2.symm

/-- Enumerates a binary string as a natural number via binary interpretation,
with a leading 1 bit to preserve leading zeros. -/
def enumeratedBinaryString (w : List Bool) : ℕ :=
  w.foldl (fun acc b => acc * 2 + if b then 1 else 0) 1

/-- Inverse of `enumeratedBinaryString`: recovers a binary string from its enumeration index. -/
def unenumeratedBinaryString (n : ℕ) : List Bool := ((Nat.bits n).reverse).tail

private lemma foldl_eq (w : List Bool) (k : ℕ) :
    w.foldl (fun acc b => acc * 2 + if b then 1 else 0) k =
    k * 2 ^ w.length +
      w.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0 := by
  induction w generalizing k with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl]
    have ih' := ih (if hd then 1 else 0)
    specialize ih (k * 2 + if hd then 1 else 0)
    rw [ih, ih']
    ring

/-- Assigns a unary index to a head direction: `left ↦ 1`, `right ↦ 2`, `none ↦ 3`. -/
def dirIdx (d : Option Turing.Dir) : ℕ :=
  match d with
  | some Turing.Dir.left  => 1
  | some Turing.Dir.right => 2
  | none                  => 3

/-- Decodes a direction index back to a head direction. -/
def decodeDirIdx (n : ℕ) : Option (Option Turing.Dir) :=
 match n with
 | 1 => some (some Turing.Dir.left)
 | 2 => some (some Turing.Dir.right)
 | 3 => some none
 | _ => none

@[simp]
private lemma decodeDirIdx_dirIdx (d : Option Turing.Dir) : decodeDirIdx (dirIdx d) = some d := by
  cases d with
  | none => rfl
  | some dir => cases dir with | left => rfl | right => rfl

/-- `dirIdx` is injective. -/
@[simp]
theorem dirIdx_injective : Function.Injective dirIdx := by
  intro d1 d2 h
  replace h := congr_arg decodeDirIdx h
  simpa using h

/-- Assigns a unary index to a tape symbol: `false ↦ 1`, `true ↦ 2`, `blank ↦ 3`. -/
def boolSymbolIdx (s : Option Bool) : ℕ :=
  match s with
  | some false => 1
  | some true  => 2
  | none       => 3

/-- Decodes a symbol index back to a tape symbol. -/
def decodeBoolSymbolIdx (n : ℕ) : Option (Option Bool) :=
  match n with
    | 1 => some (some false)
    | 2 => some (some true)
    | 3 => some none
    | _ => none

@[simp]
private lemma decodeBoolSymbolIdx_boolSymbolIdx (d : Option Bool) :
    decodeBoolSymbolIdx (boolSymbolIdx d) = some d := by
  cases d with
  | none => rfl
  | some b => cases b with | true => rfl | false => rfl

/-- `boolSymbolIdx` is injective. -/
@[simp]
theorem boolSymbolIdx_injective : Function.Injective boolSymbolIdx := by
  intro s1 s2 h
  replace h := congr_arg decodeBoolSymbolIdx h
  simpa using h

/-- Assigns a unary index to a state, via the machine's `Encodable tm.State` instance,
shifted up by one so that no state ever gets index `0`. -/
noncomputable def boolStateIdx (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) : ℕ :=
  Encodable.encode q + 1

/-- Decodes a state index back to a state of `tm`. -/
noncomputable def decodeBoolStateIdx (tm : SingleTapeTM Bool) [Encodable tm.State]
    (n : ℕ) : Option tm.State :=
  Encodable.decode (n - 1)

@[simp]
private lemma decodeBoolStateIdx_boolStateIdx (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) : decodeBoolStateIdx tm (boolStateIdx tm q) = some q := by
  simp [boolStateIdx, decodeBoolStateIdx]

/-- `boolStateIdx` is injective. -/
theorem boolStateIdx_injective (tm : SingleTapeTM Bool) [Encodable tm.State] :
    Function.Injective (boolStateIdx tm) := by
  intro q1 q2 h
  replace h := congr_arg (fun x => decodeBoolStateIdx tm x) h
  simpa using h

/-- A transition encoded as a 5-tuple of unary indices `(q, x, q', sym, dir)`. -/
abbrev TransitionTuple := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Encodes a single transition `δ(q, x) = (q', sym, dir)` as a `TransitionTuple`. -/
noncomputable def encodeBoolTransition' (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) (x : Option Bool)
    (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) : TransitionTuple :=
  (boolStateIdx tm q, boolSymbolIdx x, boolStateIdx tm q',
   boolSymbolIdx stmt.symbol, dirIdx stmt.movement)

/-- Decodes a `TransitionTuple` back to a transition. -/
noncomputable def decodeBoolTransition' (tm : SingleTapeTM Bool) [Encodable tm.State]
    (encoded : TransitionTuple) :
    Option (tm.State × Option Bool × tm.State × Option Bool × Option Turing.Dir) :=
  let (i, j, k, l, m) := encoded
  match decodeBoolStateIdx tm i, decodeBoolSymbolIdx j, decodeBoolStateIdx tm k,
        decodeBoolSymbolIdx l, decodeDirIdx m with
  | some q, some x, some q', some sym, some dir => some (q, x, q', sym, dir)
  | _, _, _, _, _ => none

@[simp]
private lemma decodeBoolTransition'_encodeBoolTransition'
    (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) :
    decodeBoolTransition' tm (encodeBoolTransition' tm q x stmt q') =
    some (q, x, q', stmt.symbol, stmt.movement) := by
  unfold encodeBoolTransition' decodeBoolTransition'
  simp only [decodeBoolStateIdx_boolStateIdx, decodeBoolSymbolIdx_boolSymbolIdx,
             decodeDirIdx_dirIdx]

/-- `encodeBoolTransition'` is injective in all five components. -/
lemma encodeBoolTransition'_injective
    (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q1 q2 : tm.State) (x1 x2 : Option Bool)
    (stmt1 stmt2 : SingleTapeTM.Stmt Bool) (q'1 q'2 : tm.State)
    (h : encodeBoolTransition' tm q1 x1 stmt1 q'1 = encodeBoolTransition' tm q2 x2 stmt2 q'2) :
    q1 = q2 ∧ x1 = x2 ∧ stmt1 = stmt2 ∧ q'1 = q'2 := by
  have h_decode := congr_arg (decodeBoolTransition' tm) h
  simp only [decodeBoolTransition'_encodeBoolTransition'] at h_decode
  injection h_decode with h_eq
  simp only [Prod.mk.injEq] at h_eq
  rcases h_eq with ⟨hq, hx, hq', hsym, hmov⟩
  cases stmt1; cases stmt2; simp_all

/-- Flattens a `TransitionTuple` to a binary string: five unary fields separated by `[true]`. -/
def flattenTransition (t : TransitionTuple) : List Bool :=
  let (i, j, k, l, m) := t
  encodeNat i ++ [true] ++ encodeNat j ++ [true] ++ encodeNat k ++ [true] ++
  encodeNat l ++ [true] ++ encodeNat m

/-- Reads a single `true`-terminated unary field off the front of a binary string,
returning the decoded number and the remaining string. -/
def readField : List Bool → Option (ℕ × List Bool)
  | []            => none
  | true :: rest  => some (0, rest)
  | false :: rest => (readField rest).map (fun p => (p.1 + 1, p.2))

private lemma readField_append (n : ℕ) (rest : List Bool) :
    readField (encodeNat n ++ true :: rest) = some (n, rest) := by
  induction n with
  | zero => simp [readField]
  | succ n ih => simp [encodeNat_succ, readField, ih]

/-- Reads the last unary field of a transition, which has no terminating `true` bit.
Stops at the first `true` (or end of string) without consuming it. -/
def readLastField : List Bool → ℕ × List Bool
  | []            => (0, [])
  | false :: rest => let (n, l) := readLastField rest; (n + 1, l)
  | true :: rest  => (0, true :: rest)

private lemma readLastField_encodeNat (n : ℕ) : readLastField (encodeNat n) = (n, []) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodeNat_succ, readLastField, ih]

private lemma readLastField_encodeNat_true (n : ℕ) (rest : List Bool) :
    readLastField (encodeNat n ++ true :: rest) = (n, true :: rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodeNat_succ, readLastField, ih]

/-- A transition record `(q, x, q', sym, dir)` for a `Bool`-tape TM. -/
abbrev BoolTransData (tm : SingleTapeTM Bool) :=
  tm.State × Option Bool × tm.State × Option Bool × Option Turing.Dir

/-- Encodes a single transition to a binary string via `flattenTransition`. -/
noncomputable def encodeBoolTransition (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) :
    List Bool :=
  flattenTransition (encodeBoolTransition' tm q x stmt q')

/-- Decodes a binary string to a transition record and the remaining string. -/
noncomputable def decodeBoolTransition (tm : SingleTapeTM Bool) [Encodable tm.State]
    (l : List Bool) : Option (BoolTransData tm × List Bool) := do
  let (i, l) ← readField l
  let (j, l) ← readField l
  let (k, l) ← readField l
  let (lIdx, l) ← readField l
  let (m, l) := readLastField l
  let q ← decodeBoolStateIdx tm i
  let x ← decodeBoolSymbolIdx j
  let q' ← decodeBoolStateIdx tm k
  let sym ← decodeBoolSymbolIdx lIdx
  let dir ← decodeDirIdx m
  some ((q, x, q', sym, dir), l)

@[simp]
private lemma decodeBoolTransition_nil (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) :
    decodeBoolTransition tm (encodeBoolTransition tm q x stmt q') =
      some ((q, x, q', stmt.symbol, stmt.movement), []) := by
  cases stmt
  unfold encodeBoolTransition decodeBoolTransition encodeBoolTransition' flattenTransition
  simp [List.append_assoc, List.cons_append, List.nil_append, readField_append,
        readLastField_encodeNat, decodeBoolStateIdx_boolStateIdx,
        decodeBoolSymbolIdx_boolSymbolIdx, decodeDirIdx_dirIdx, bind]

@[simp]
private lemma decodeBoolTransition_true (tm : SingleTapeTM Bool) [Encodable tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State)
    (rest : List Bool) :
    decodeBoolTransition tm (encodeBoolTransition tm q x stmt q' ++ true :: rest) =
      some ((q, x, q', stmt.symbol, stmt.movement), true :: rest) := by
  cases stmt
  unfold encodeBoolTransition decodeBoolTransition encodeBoolTransition' flattenTransition
  simp [List.append_assoc, List.cons_append, List.nil_append, readField_append,
        readLastField_encodeNat_true, decodeBoolStateIdx_boolStateIdx,
        decodeBoolSymbolIdx_boolSymbolIdx, decodeDirIdx_dirIdx, bind]

/-- Encodes a list of transition records as a binary string,
separating adjacent transitions with `[true, true]`. -/
noncomputable def encodeBoolTr (tm : SingleTapeTM Bool) [Encodable tm.State] :
    List (BoolTransData tm) → List Bool
  | []      => []
  | [t]     => encodeBoolTransition tm t.1 t.2.1 ⟨t.2.2.2.1, t.2.2.2.2⟩ t.2.2.1
  | t :: t' :: ts =>
      encodeBoolTransition tm t.1 t.2.1 ⟨t.2.2.2.1, t.2.2.2.2⟩ t.2.2.1
        ++ [true, true] ++ encodeBoolTr tm (t' :: ts)

/-- Decodes up to `fuel` transition records from a binary string. -/
noncomputable def decodeBoolTr (tm : SingleTapeTM Bool) [Encodable tm.State] :
    ℕ → List Bool → Option (List (BoolTransData tm) × List Bool)
  | 0, l => some ([], l)
  | fuel + 1, l => do
      let (t, l) ← decodeBoolTransition tm l
      match l with
      | true :: true :: l =>
          let (ts, rest) ← decodeBoolTr tm fuel l
          some (t :: ts, rest)
      | _ => some ([t], l)

@[simp]
private lemma decodeBoolTr_encodeBoolTr (tm : SingleTapeTM Bool) [Encodable tm.State]
    (ts : List (BoolTransData tm)) :
    decodeBoolTr tm ts.length (encodeBoolTr tm ts) = some (ts, []) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨q, x, q', sym, dir⟩ := t
      cases ts with
      | nil =>
          unfold encodeBoolTr decodeBoolTr
          simp [decodeBoolTransition_nil]
      | cons t' ts' =>
          simp only [List.length]
          unfold encodeBoolTr decodeBoolTr
          simp only [List.append_assoc, List.length_cons] at *
          simp [bind, ih]

/-- The data needed to encode a `Bool`-tape TM: its initial state and transition table. -/
abbrev BoolMachineData (tm : SingleTapeTM Bool) :=
  tm.State × List (BoolTransData tm)

/-- Encodes a `BoolMachineData` record as a binary string. The format is:
`unary(q₀) ++ [true,true,true] ++ unary(n) ++ [true,true,true,true] ++ transitions`. -/
noncomputable def encodeBoolTMData (tm : SingleTapeTM Bool) [Encodable tm.State]
    (md : BoolMachineData tm) : List Bool :=
  encodeNat (boolStateIdx tm md.1) ++ [true, true, true] ++
  encodeNat md.2.length ++ [true, true, true, true] ++
  encodeBoolTr tm md.2

/-- Decodes a binary string back to a `BoolMachineData` record. -/
noncomputable def decodeBoolTMData (tm : SingleTapeTM Bool) [Encodable tm.State]
    (l : List Bool) : Option (BoolMachineData tm) := do
  let (i, l) ← readField l
  match l with
  | true :: true :: l =>
      let (n, l) ← readField l
      match l with
      | true :: true :: true :: l =>
          let q ← decodeBoolStateIdx tm i
          let (ts, _) ← decodeBoolTr tm n l
          some (q, ts)
      | _ => none
  | _ => none

@[simp]
private lemma decodeBoolTMData_encodeBoolTMData (tm : SingleTapeTM Bool) [Encodable tm.State]
    (md : BoolMachineData tm) :
    decodeBoolTMData tm (encodeBoolTMData tm md) = some md := by
  rcases md with ⟨q, ts⟩
  unfold encodeBoolTMData decodeBoolTMData
  simp [List.append_assoc, List.cons_append, List.nil_append,
        readField_append, decodeBoolStateIdx_boolStateIdx,
        decodeBoolTr_encodeBoolTr, bind]

/-- `encodeBoolTMData` is injective: distinct machine data records produce distinct encodings. -/
theorem encodeBoolTMData_injective (tm : SingleTapeTM Bool) [Encodable tm.State] :
    Function.Injective (encodeBoolTMData tm) := by
  intro md1 md2 h
  have := congr_arg (decodeBoolTMData tm) h
  simpa using this

end DiagonaLean.Halt.Encoding

namespace Cslib.Turing.SingleTapeTM

open DiagonaLean.Halt.Encoding

/-- Extracts the `BoolMachineData` of a TM: its initial state paired with the list of all
transitions that have a successor state, enumerated over all states and tape symbols. -/
noncomputable def toBoolMachineData (tm : SingleTapeTM Bool) :
    BoolMachineData tm :=
  (tm.q₀,
   ((@Finset.univ tm.State tm.stateFintype).toList ×ˢ [none, some false, some true]).filterMap
     fun qx : tm.State × Option Bool =>
       match tm.tr qx.1 qx.2 with
       | (stmt, some q') => some (qx.1, qx.2, q', stmt.symbol, stmt.movement)
       | (_, none)       => none)

end Cslib.Turing.SingleTapeTM

namespace DiagonaLean.Halt.Encoding

/-- Encodes a `Bool`-tape TM as a binary string by encoding its `toBoolMachineData`. -/
noncomputable def encodeBoolTM (tm : SingleTapeTM Bool) [Encodable tm.State] :
    List Bool :=
  encodeBoolTMData tm (tm.toBoolMachineData)

end DiagonaLean.Halt.Encoding
