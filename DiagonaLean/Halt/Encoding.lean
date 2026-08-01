/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

open Cslib.Turing SingleTapeTM

namespace DiagonaLean.Halt.Encoding

/- From Hopcroft et al.'s textbook: δ(qi, Xj ) = (qk, Xl, Dm), for some integers i, j , k, l, and
m. We shall code this rule by the string 0i 10j 10k 10l 10m. Notice that, since all of i, j , k, l,
and m are at least one, there are no occurrences of two or more consecutive 1's within the code for
a single transition. A code for the entire TM M consists of all the codes for the transitions, in
some order, separated by pairs of 1's: C1 11 C2 11 ... 11 Cn-1 11Cn. We shall assume the states are
q1,...,  qr for some r. The start state will always be q1, and q2 will be the only accepting state.
Note that, since we may assume the TM halts whenever it enters an accepting state, there is never
any need for more than one accepting state. We shall assume the tape symbols are X1,... , Xs for
some s. X1 always will be the symbol 0, X2 will be 1, and X3 will be ⊔, the blank. However, other
tape symbols can be assigned to the remaining integers arbitrarily. We shall refer to direction L as
D1 and direction R as D2. The encoding is an injection. -/

def encodeNat (n : ℕ) : List Bool := List.replicate n false

@[simp]
lemma encodeNat_zero : encodeNat 0 = [] := rfl

@[simp]
lemma encodeNat_succ (n : ℕ) :
    encodeNat (n + 1) = false :: encodeNat n := by simp [encodeNat, List.replicate_succ]

def decodeNat (l : List Bool) : Option ℕ :=
  if l.all (· == false) then some l.length
  else none

@[simp]
private lemma decodeNat_encodeNat (n : ℕ) : decodeNat (encodeNat n) = some n := by
  simp [decodeNat, encodeNat, List.all_replicate, List.length_replicate]

def encodePair (a b : List Bool) : List Bool :=
  a ++ [true, true] ++ b

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

def enumeratedBinaryString (w : List Bool) : ℕ :=
  w.foldl (fun acc b => acc * 2 + if b then 1 else 0) 1

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

def dirIdx (d : Option Turing.Dir) : ℕ :=
  match d with
  | some Turing.Dir.left  => 1
  | some Turing.Dir.right => 2
  | none           => 3

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
  | some dir =>
    cases dir with
    | left => rfl
    | right => rfl

@[simp]
theorem dirIdx_injective : Function.Injective dirIdx := by
  intro d1 d2 h
  replace h := congr_arg decodeDirIdx h
  simpa using h

def boolSymbolIdx (s : Option Bool) : ℕ :=
  match s with
  | some false => 1
  | some true  => 2
  | none       => 3

def decodeBoolSymbolIdx (n : ℕ) : Option (Option Bool) :=
  match n with
    | 1 => some (some false)
    | 2 => some (some true)
    | 3 => some none
    | _ => none

@[simp]
private lemma decodeBoolSymbolIdx_boolSymbolIdx (d : Option Bool) : decodeBoolSymbolIdx (boolSymbolIdx (d)) = some d := by
  cases  d with
  | none => rfl
  | some  Bool =>
     cases Bool with
      | true => rfl
      | false => rfl

@[simp]
theorem boolSymbolIdx_injective : Function.Injective boolSymbolIdx := by
  intro s1 s2 h
  replace h := congr_arg decodeBoolSymbolIdx h
  simpa using h

noncomputable def boolStateIdx (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) : ℕ :=
  if q == tm.q₀ then 1
  else Finset.univ.toList.findIdx (· == q) + 2

noncomputable def decodeBoolStateIdx (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (n : ℕ) : Option tm.State :=
  if n = 1 then some tm.q₀
  else (Finset.univ.toList)[n - 2]?

@[simp]
private lemma decodeBoolStateIdx_boolStateIdx (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) : decodeBoolStateIdx tm (boolStateIdx tm q) = some q := by
  by_cases h : q = tm.q₀
  · subst h
    simp [boolStateIdx, decodeBoolStateIdx]
  · have hex : ∃ x ∈ (Finset.univ : Finset tm.State).toList, (x == q) = true :=
      ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), beq_self_eq_true q⟩
    have hlt := List.findIdx_lt_length_of_exists hex
    have hq : (Finset.univ : Finset tm.State).toList[(Finset.univ : Finset tm.State).toList.findIdx (· == q)] = q := by
      simpa using List.findIdx_getElem (w := hlt)
    have hcode : boolStateIdx tm q
        = (Finset.univ : Finset tm.State).toList.findIdx (· == q) + 2 := by
      simp [boolStateIdx, h]
    rw [hcode]
    unfold decodeBoolStateIdx
    grind

theorem boolStateIdx_injective (tm : SingleTapeTM Bool) [DecidableEq tm.State] :
    Function.Injective (boolStateIdx tm) := by
  intro q1 q2 h
  replace h := congr_arg (fun x => decodeBoolStateIdx tm x) h
  simpa using h

abbrev TransitionTuple := ℕ × ℕ × ℕ × ℕ × ℕ

noncomputable def encodeBoolTransition' (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool)
    (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) : TransitionTuple :=
  let i := boolStateIdx tm q
  let j := boolSymbolIdx x
  let k := boolStateIdx tm q'
  let l := boolSymbolIdx stmt.symbol
  let m := dirIdx stmt.movement
  (i, j, k, l, m)

noncomputable def decodeBoolTransition' (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (encoded : TransitionTuple) :
    Option (tm.State × Option Bool × tm.State × Option Bool × Option Turing.Dir) :=
  let (i, j, k, l, m) := encoded
  match decodeBoolStateIdx tm i, decodeBoolSymbolIdx j, decodeBoolStateIdx tm k, decodeBoolSymbolIdx l, decodeDirIdx m with
  | some q, some x, some q', some sym, some dir => some (q, x, q', sym, dir)
  | _, _, _, _, _ => none

@[simp]
private lemma decodeBoolTransition'_encodeBoolTransition' (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) :
    decodeBoolTransition' tm (encodeBoolTransition' tm q x stmt q') =
    some (q, x, q', stmt.symbol, stmt.movement) := by
  unfold encodeBoolTransition' decodeBoolTransition'
  simp only [decodeBoolStateIdx_boolStateIdx, decodeBoolSymbolIdx_boolSymbolIdx, decodeDirIdx_dirIdx]

lemma encodeBoolTransition'_injective
    (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q1 q2 : tm.State) (x1 x2 : Option Bool) (stmt1 stmt2 : SingleTapeTM.Stmt Bool) (q'1 q'2 : tm.State)
    (h : encodeBoolTransition' tm q1 x1 stmt1 q'1 = encodeBoolTransition' tm q2 x2 stmt2 q'2) :
    q1 = q2 ∧ x1 = x2 ∧ stmt1 = stmt2 ∧ q'1 = q'2 := by
  have h_decode := congr_arg (decodeBoolTransition' tm) h
  simp only [decodeBoolTransition'_encodeBoolTransition'] at h_decode
  injection h_decode with h_eq
  simp only [Prod.mk.injEq] at h_eq
  rcases h_eq with ⟨hq, hx, hq', hsym, hmov⟩
  cases stmt1
  cases stmt2
  simp_all

def flattenTransition (t : TransitionTuple) : List Bool :=
  let (i, j, k, l, m) := t
  encodeNat i ++ [true] ++
  encodeNat j ++ [true] ++
  encodeNat k ++ [true] ++
  encodeNat l ++ [true] ++
  encodeNat m

/- ### Reading one field back off a bitstring

`readField` reads a single `true`-terminated unary number off the front
of a list, returning the number and whatever's left. `readLastField`
reads the *last* field of a transition, which has no terminator of its
own — it just stops at the first `true` (or the end of the list)
without consuming it. -/

def readField : List Bool → Option (ℕ × List Bool)
  | []            => none
  | true :: rest  => some (0, rest)
  | false :: rest => (readField rest).map (fun p => (p.1 + 1, p.2))

private lemma readField_append (n : ℕ) (rest : List Bool) :
    readField (encodeNat n ++ true :: rest) = some (n, rest) := by
  induction n with
  | zero => simp [readField]
  | succ n ih => simp [encodeNat_succ, readField, ih]

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

abbrev BoolTransData (tm : SingleTapeTM Bool) :=
  tm.State × Option Bool × tm.State × Option Bool × Option Turing.Dir

noncomputable def encodeBoolTransition (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) :
    List Bool :=
  flattenTransition (encodeBoolTransition' tm q x stmt q')

noncomputable def decodeBoolTransition (tm : SingleTapeTM Bool) [DecidableEq tm.State]
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
private lemma decodeBoolTransition_nil (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) :
    decodeBoolTransition tm (encodeBoolTransition tm q x stmt q') =
      some ((q, x, q', stmt.symbol, stmt.movement), []) := by
  cases stmt
  unfold encodeBoolTransition decodeBoolTransition encodeBoolTransition' flattenTransition
  simp [List.append_assoc, List.cons_append, List.nil_append, readField_append,
        readLastField_encodeNat, decodeBoolStateIdx_boolStateIdx,
        decodeBoolSymbolIdx_boolSymbolIdx, decodeDirIdx_dirIdx, bind]

@[simp]
private lemma decodeBoolTransition_true (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool) (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State)
    (rest : List Bool) :
    decodeBoolTransition tm (encodeBoolTransition tm q x stmt q' ++ true :: rest) =
      some ((q, x, q', stmt.symbol, stmt.movement), true :: rest) := by
  cases stmt
  unfold encodeBoolTransition decodeBoolTransition encodeBoolTransition' flattenTransition
  simp [List.append_assoc, List.cons_append, List.nil_append, readField_append,
        readLastField_encodeNat_true, decodeBoolStateIdx_boolStateIdx,
        decodeBoolSymbolIdx_boolSymbolIdx, decodeDirIdx_dirIdx, bind]

noncomputable def encodeBoolTr (tm : SingleTapeTM Bool) [DecidableEq tm.State] :
    List (BoolTransData tm) → List Bool
  | []      => []
  | [t]     => encodeBoolTransition tm t.1 t.2.1 ⟨t.2.2.2.1, t.2.2.2.2⟩ t.2.2.1
  | t :: t' :: ts =>
      encodeBoolTransition tm t.1 t.2.1 ⟨t.2.2.2.1, t.2.2.2.2⟩ t.2.2.1
        ++ [true, true] ++ encodeBoolTr tm (t' :: ts)

noncomputable def decodeBoolTr (tm : SingleTapeTM Bool) [DecidableEq tm.State] :
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
private lemma decodeBoolTr_encodeBoolTr (tm : SingleTapeTM Bool) [DecidableEq tm.State]
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
          simp only [List.append_assoc]
          simp only [List.length_cons] at ih
          simp [bind, ih]

abbrev BoolMachineData (tm : SingleTapeTM Bool) :=
  tm.State × List (BoolTransData tm)

noncomputable def encodeBoolTMData (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (md : BoolMachineData tm) : List Bool :=
  encodeNat (boolStateIdx tm md.1) ++ [true, true, true] ++
  encodeNat md.2.length ++ [true, true, true, true] ++
  encodeBoolTr tm md.2

noncomputable def decodeBoolTMData (tm : SingleTapeTM Bool) [DecidableEq tm.State]
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
private lemma decodeBoolTMData_encodeBoolTMData (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (md : BoolMachineData tm) :
    decodeBoolTMData tm (encodeBoolTMData tm md) = some md := by
  rcases md with ⟨q, ts⟩
  unfold encodeBoolTMData decodeBoolTMData
  simp [List.append_assoc, List.cons_append, List.nil_append,
        readField_append, decodeBoolStateIdx_boolStateIdx,
        decodeBoolTr_encodeBoolTr, bind]

theorem encodeBoolTMData_injective (tm : SingleTapeTM Bool) [DecidableEq tm.State] :
    Function.Injective (encodeBoolTMData tm) := by
  intro md1 md2 h
  have := congr_arg (decodeBoolTMData tm) h
  simpa using this

end DiagonaLean.Halt.Encoding

namespace Cslib.Turing.SingleTapeTM

open DiagonaLean.Halt.Encoding

noncomputable def toBoolMachineData (tm : SingleTapeTM Bool) [DecidableEq tm.State] :
    BoolMachineData tm :=
  (tm.q₀,
   ((@Finset.univ tm.State tm.stateFintype).toList ×ˢ [none, some false, some true]).filterMap
     fun qx : tm.State × Option Bool =>
       match tm.tr qx.1 qx.2 with
       | (stmt, some q') => some (qx.1, qx.2, q', stmt.symbol, stmt.movement)
       | (_, none)       => none)
end Cslib.Turing.SingleTapeTM

namespace DiagonaLean.Halt.Encoding

noncomputable def encodeBoolTM (tm : SingleTapeTM Bool) [DecidableEq tm.State] :
    List Bool :=
  encodeBoolTMData tm (tm.toBoolMachineData)

end DiagonaLean.Halt.Encoding
