import Cslib.Foundations.Data.BiTape
import Mathlib.Tactic

/-! # Cell-wise view of a `BiTape`

A `BiTape` is a bi-infinite tape.  For reasoning about Turing machine simulations it is
much more convenient to view it as a function `ℤ → Option Symbol`, sending an offset
relative to the head to the symbol stored there.  This file sets up that view and the
lemmas describing how it interacts with `write`, `move` and `mk₁`.
-/

namespace DiagonaLean.Normalize

open Cslib.Turing

variable {S : Type*}

/-- The `n`-th entry of a `StackTape` (blank if beyond the stored prefix). -/
def stCell (l : StackTape S) (n : ℕ) : Option S := (l.toList[n]?).getD none

@[simp]
lemma stCell_nil (n : ℕ) : stCell (StackTape.nil : StackTape S) n = none := by
  simp [stCell]

lemma stCell_zero (l : StackTape S) : stCell l 0 = l.head := by
  unfold stCell StackTape.head
  cases l.toList with
  | nil => simp
  | cons a t => simp

lemma stCell_succ (l : StackTape S) (n : ℕ) : stCell l (n + 1) = stCell l.tail n := by
  obtain ⟨L, hL⟩ := l
  cases L with
  | nil => simp [stCell, StackTape.tail]
  | cons a t => simp [stCell, StackTape.tail]

lemma stCell_cons_zero (o : Option S) (l : StackTape S) : stCell (StackTape.cons o l) 0 = o := by
  rw [stCell_zero, StackTape.head_cons]

lemma stCell_cons_succ (o : Option S) (l : StackTape S) (n : ℕ) :
    stCell (StackTape.cons o l) (n + 1) = stCell l n := by
  rw [stCell_succ, StackTape.tail_cons]

lemma stCell_eq_none_of_toList_nil {l : StackTape S} (h : l.toList = []) (n : ℕ) :
    stCell l n = none := by
  simp [stCell, h]

lemma stCell_mapSome (l : List S) (n : ℕ) : stCell (StackTape.mapSome l) n = l[n]? := by
  simp only [stCell, StackTape.mapSome, List.getElem?_map]
  cases l[n]? <;> simp

/-- The symbol at offset `d` from the head of a `BiTape`. -/
def cellAt (t : BiTape S) (d : ℤ) : Option S :=
  if d = 0 then t.head
  else if 0 < d then stCell t.right (d - 1).toNat
  else stCell t.left (-d - 1).toNat

@[simp]
lemma cellAt_zero (t : BiTape S) : cellAt t 0 = t.head := by simp [cellAt]

lemma cellAt_pos (t : BiTape S) {d : ℤ} (h : 0 < d) :
    cellAt t d = stCell t.right (d - 1).toNat := by
  rw [cellAt, if_neg (by omega), if_pos h]

lemma cellAt_neg (t : BiTape S) {d : ℤ} (h : d < 0) :
    cellAt t d = stCell t.left (-d - 1).toNat := by
  rw [cellAt, if_neg (by omega), if_neg (by omega)]

@[simp]
lemma cellAt_write (t : BiTape S) (a : Option S) (d : ℤ) :
    cellAt (t.write a) d = if d = 0 then a else cellAt t d := by
  unfold cellAt BiTape.write
  split <;> simp_all

lemma cellAt_moveRight (t : BiTape S) (d : ℤ) : cellAt t.moveRight d = cellAt t (d + 1) := by
  rcases lt_trichotomy d 0 with h | h | h
  · rcases eq_or_lt_of_le (by omega : d + 1 ≤ 0) with h1 | h1
    · have hd : d = -1 := by omega
      subst hd
      rw [cellAt_neg _ h]
      simp only [BiTape.moveRight]
      norm_num
      rw [stCell_cons_zero]
    · rw [cellAt_neg _ h, cellAt_neg _ h1]
      simp only [BiTape.moveRight]
      have : (-d - 1).toNat = (-(d + 1) - 1).toNat + 1 := by omega
      rw [this, stCell_cons_succ]
  · subst h
    simp only [cellAt_zero, BiTape.moveRight]
    rw [cellAt_pos _ (by omega)]
    simp [stCell_zero]
  · rw [cellAt_pos _ h, cellAt_pos _ (by omega)]
    simp only [BiTape.moveRight]
    have : (d + 1 - 1).toNat = (d - 1).toNat + 1 := by omega
    rw [this, stCell_succ]

lemma cellAt_moveLeft (t : BiTape S) (d : ℤ) : cellAt t.moveLeft d = cellAt t (d - 1) := by
  rcases lt_trichotomy d 0 with h | h | h
  · rw [cellAt_neg _ h, cellAt_neg _ (by omega)]
    simp only [BiTape.moveLeft]
    have : (-(d - 1) - 1).toNat = (-d - 1).toNat + 1 := by omega
    rw [this, stCell_succ]
  · subst h
    simp only [cellAt_zero, BiTape.moveLeft]
    rw [cellAt_neg _ (by omega)]
    simp [stCell_zero]
  · rcases eq_or_lt_of_le (by omega : 0 ≤ d - 1) with h1 | h1
    · have hd : d = 1 := by omega
      subst hd
      rw [cellAt_pos _ h]
      simp only [BiTape.moveLeft]
      norm_num
      rw [stCell_cons_zero]
    · rw [cellAt_pos _ h, cellAt_pos _ h1]
      simp only [BiTape.moveLeft]
      have : (d - 1).toNat = (d - 1 - 1).toNat + 1 := by omega
      rw [this, stCell_cons_succ]

@[simp]
lemma cellAt_optionMove_none (t : BiTape S) (d : ℤ) :
    cellAt (t.optionMove none) d = cellAt t d := rfl

lemma cellAt_optionMove_left (t : BiTape S) (d : ℤ) :
    cellAt (t.optionMove (some Turing.Dir.left)) d = cellAt t (d - 1) := cellAt_moveLeft t d

lemma cellAt_optionMove_right (t : BiTape S) (d : ℤ) :
    cellAt (t.optionMove (some Turing.Dir.right)) d = cellAt t (d + 1) := cellAt_moveRight t d

lemma cellAt_mk₁ (l : List S) (d : ℤ) :
    cellAt (BiTape.mk₁ l) d = if 0 ≤ d then l[d.toNat]? else none := by
  cases l with
  | nil =>
    simp only [BiTape.mk₁]
    rcases lt_trichotomy d 0 with h | h | h
    · rw [cellAt_neg _ h]; simp [h.not_ge, BiTape.nil]
    · subst h; simp [BiTape.nil]
    · rw [cellAt_pos _ h]; simp [BiTape.nil, h.le]
  | cons a t =>
    simp only [BiTape.mk₁]
    rcases lt_trichotomy d 0 with h | h | h
    · rw [cellAt_neg _ h]; simp [h.not_ge]
    · subst h; simp
    · rw [cellAt_pos _ h, if_pos h.le]
      simp only [stCell_mapSome]
      have : d.toNat = (d - 1).toNat + 1 := by omega
      rw [this]
      simp

/-- If the left part of the tape is empty, every cell to the left of the head is blank. -/
lemma cellAt_eq_none_of_left_nil {t : BiTape S} (h : t.left.toList = []) {d : ℤ} (hd : d < 0) :
    cellAt t d = none := by
  rw [cellAt_neg _ hd, stCell_eq_none_of_toList_nil h]

/-- Contrapositive: a non-blank cell to the left of the head witnesses a non-empty left part. -/
lemma left_toList_ne_nil {t : BiTape S} {d : ℤ} (hd : d < 0) (h : cellAt t d ≠ none) :
    t.left.toList ≠ [] := fun hnil => h (cellAt_eq_none_of_left_nil hnil hd)

end DiagonaLean.Normalize
