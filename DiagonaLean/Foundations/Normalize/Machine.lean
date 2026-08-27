/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Foundations.Normalize.Cell
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-! # The normalised machine

Given a single tape Turing machine `tm` over the alphabet `Bool`, we build a machine
`normTM tm` over the alphabet `Bool × Bool` which

* never writes the blank symbol (`NoBlankWrites`), and
* never moves left of its starting cell (`NoLeftBoundary`),

and which halts on the encoded input `encInput w` exactly when `tm` halts on `w`.

## The construction

The tape of `normTM tm` is one-way infinite in the following sense: cell `0` holds a special
marker symbol `Mk`, and the bi-infinite tape of `tm` is *folded* onto the cells `1, 2, 3, …`
by the map `fold`:

```
tm cell     …   -3   -2   -1    0    1    2   …
normTM cell …    6    4    2    1    3    5  …
```

Cell `2 * j + 1` of `normTM tm` holds cell `j ≥ 0` of `tm`, and cell `-2 * j` holds cell
`j < 0` of `tm`.  A symbol `b : Bool` of `tm` is stored as `(b, true)`, and a blank of `tm`
is stored either as a genuine blank or as `Bl = (false, false)`; this way `normTM tm` never
has to write a blank.  The marker `Mk = (true, false)` occurs only in cell `0`, which lets
the machine detect the fold point (the only place where the position bookkeeping is
irregular).

One step of `tm` is simulated by one to three steps of `normTM tm`, using the auxiliary
control states in `Ctrl`.
-/

@[expose] public section
namespace DiagonaLean.Foundations.Normalize

open Cslib.Turing SingleTapeTM

/-- The alphabet of the normalised machine. -/
abbrev Sym2 := Bool × Bool

/-- The left end marker, which sits in cell `0` of the normalised machine forever. -/
def Mk : Sym2 := (true, false)

/-- The symbol used to represent a blank that has been written by the simulated machine. -/
def Bl : Sym2 := (false, false)

lemma Bl_ne_Mk : Bl ≠ Mk := by decide

/-- Encoding of a symbol of the simulated machine. -/
def encSym : Option Bool → Option Sym2
  | none => some Bl
  | some b => some (b, true)

/-- Decoding: which symbol of the simulated machine a cell of the normalised machine holds. -/
def decSym : Option Sym2 → Option Bool
  | some (b, true) => some b
  | _ => none

/-- Rewriting a cell with its own contents, avoiding blank writes. -/
def preserve (a : Option Sym2) : Option Sym2 := some (a.getD Bl)

@[simp] lemma decSym_encSym (c : Option Bool) : decSym (encSym c) = c := by
  cases c <;> rfl

@[simp] lemma encSym_ne_none (c : Option Bool) : encSym c ≠ none := by
  cases c <;> simp [encSym]

@[simp] lemma encSym_ne_Mk (c : Option Bool) : encSym c ≠ some Mk := by
  cases c <;> simp [encSym, Mk, Bl]

@[simp] lemma preserve_ne_none (a : Option Sym2) : preserve a ≠ none := by simp [preserve]

@[simp] lemma decSym_preserve (a : Option Sym2) : decSym (preserve a) = decSym a := by
  match a with
  | none => rfl
  | some (b, c) => rfl

lemma preserve_ne_Mk {a : Option Sym2} (h : a ≠ some Mk) : preserve a ≠ some Mk := by
  match a with
  | none => simp [preserve, Bl, Mk]
  | some (b, c) => simpa [preserve] using h

/-- Control states of the normalised machine. -/
inductive Ctrl
  /-- Initial state: sitting on the marker, about to start the simulation. -/
  | start
  /-- Simulating a step of `tm`, with the head on a cell of the right half of `tm`'s tape. -/
  | simR
  /-- Simulating a step of `tm`, with the head on a cell of the left half of `tm`'s tape. -/
  | simL
  /-- One more step to the right, then continue simulating on the right half. -/
  | mvRR
  /-- One more step to the right, then continue simulating on the left half. -/
  | mvRL
  /-- Checking whether the cell reached after a left move is the marker (right half). -/
  | chkR
  /-- First half of a two cell left move (left half of `tm`'s tape). -/
  | chkL1
  /-- Checking whether the cell reached after a left move is the marker (left half). -/
  | chkL2
  deriving DecidableEq, Inhabited

instance : Fintype Ctrl :=
  ⟨⟨([Ctrl.start, Ctrl.simR, Ctrl.simL, Ctrl.mvRR, Ctrl.mvRL, Ctrl.chkR, Ctrl.chkL1,
      Ctrl.chkL2] : List Ctrl), by decide⟩, fun x => by cases x <;> decide⟩

/-- The `sim` control state for a head on the right (`true`) or left (`false`) half. -/
def Ctrl.sim (right : Bool) : Ctrl := if right then .simR else .simL

@[simp] lemma Ctrl.sim_true : Ctrl.sim true = .simR := rfl
@[simp] lemma Ctrl.sim_false : Ctrl.sim false = .simL := rfl

variable (tm : SingleTapeTM Bool)

/-- The transition performed while simulating one step of `tm`. -/
def simStep (q : tm.State) (right : Bool) (a : Option Sym2) :
    Stmt Sym2 × Option (tm.State × Ctrl) :=
  let r := tm.tr q (decSym a)
  let wr := encSym r.1.symbol
  match r.2 with
  | none => (⟨wr, none⟩, none)
  | some q₂ =>
    match r.1.movement with
    | none => (⟨wr, none⟩, some (q₂, Ctrl.sim right))
    | some Turing.Dir.right =>
        if right then (⟨wr, some Turing.Dir.right⟩, some (q₂, .mvRR))
        else (⟨wr, some Turing.Dir.left⟩, some (q₂, .chkL1))
    | some Turing.Dir.left =>
        if right then (⟨wr, some Turing.Dir.left⟩, some (q₂, .chkR))
        else (⟨wr, some Turing.Dir.right⟩, some (q₂, .mvRL))

/-- The transition function of the normalised machine. -/
def normTr (q : tm.State) (ctrl : Ctrl) (a : Option Sym2) :
    Stmt Sym2 × Option (tm.State × Ctrl) :=
  match ctrl with
  | .start => (⟨some Mk, some Turing.Dir.right⟩, some (q, .simR))
  | .mvRR => (⟨preserve a, some Turing.Dir.right⟩, some (q, .simR))
  | .mvRL => (⟨preserve a, some Turing.Dir.right⟩, some (q, .simL))
  | .chkR =>
      if a = some Mk then (⟨some Mk, some Turing.Dir.right⟩, some (q, .mvRL))
      else (⟨preserve a, some Turing.Dir.left⟩, some (q, .simR))
  | .chkL1 => (⟨preserve a, some Turing.Dir.left⟩, some (q, .chkL2))
  | .chkL2 =>
      if a = some Mk then (⟨some Mk, some Turing.Dir.right⟩, some (q, .simR))
      else (⟨preserve a, none⟩, some (q, .simL))
  | .simR => simStep tm q true a
  | .simL => simStep tm q false a

/-- The normalised machine simulating `tm`. -/
def normTM : SingleTapeTM Sym2 where
  State := tm.State × Ctrl
  q₀ := (tm.q₀, .start)
  tr := fun s a => normTr tm s.1 s.2 a

@[simp] lemma normTM_State : (normTM tm).State = (tm.State × Ctrl) := rfl

@[simp] lemma normTM_tr (s : tm.State × Ctrl) (a : Option Sym2) :
    (normTM tm).tr s a = normTr tm s.1 s.2 a := rfl

/-- The encoded input: the marker, followed by the input interleaved with blanks. -/
def encInput (w : List Bool) : List Sym2 := Mk :: w.flatMap (fun b => [(b, true), Bl])

/-- The fold of `tm`'s bi-infinite tape onto the cells `1, 2, 3, …`. -/
def fold (j : ℤ) : ℤ := if 0 ≤ j then 2 * j + 1 else -2 * j

lemma fold_of_nonneg {j : ℤ} (h : 0 ≤ j) : fold j = 2 * j + 1 := by simp [fold, h]

lemma fold_of_neg {j : ℤ} (h : j < 0) : fold j = -2 * j := by
  simp [fold, h.not_ge]

lemma one_le_fold (j : ℤ) : 1 ≤ fold j := by
  rcases le_or_gt 0 j with h | h
  · rw [fold_of_nonneg h]; omega
  · rw [fold_of_neg h]; omega

lemma fold_pos (j : ℤ) : 0 < fold j := lt_of_lt_of_le zero_lt_one (one_le_fold j)

lemma fold_injective : Function.Injective fold := by
  intro a b hab
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb <;>
    simp only [fold_of_nonneg, fold_of_neg, ha, hb] at hab <;> omega

lemma fold_eq_iff {a b : ℤ} : fold a = fold b ↔ a = b :=
  ⟨fun h => fold_injective h, fun h => by rw [h]⟩

lemma fold_succ_of_nonneg {i : ℤ} (h : 0 ≤ i) : fold (i + 1) = fold i + 2 := by
  rw [fold_of_nonneg h, fold_of_nonneg (by omega)]; ring

lemma fold_pred_of_neg {i : ℤ} (h : i < 0) : fold (i - 1) = fold i + 2 := by
  rw [fold_of_neg h, fold_of_neg (by omega)]; ring

lemma fold_pred_of_pos {i : ℤ} (h : 0 < i) : fold (i - 1) = fold i - 2 := by
  rw [fold_of_nonneg h.le, fold_of_nonneg (by omega)]; ring

lemma fold_succ_of_lt_neg_one {i : ℤ} (h : i < -1) : fold (i + 1) = fold i - 2 := by
  rw [fold_of_neg (by omega), fold_of_neg (by omega)]; ring

lemma fold_zero : fold 0 = 1 := rfl

lemma fold_neg_one : fold (-1) = 2 := rfl

end DiagonaLean.Foundations.Normalize
