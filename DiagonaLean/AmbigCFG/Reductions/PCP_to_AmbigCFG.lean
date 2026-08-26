/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Tactic

import DiagonaLean.PCP.Basic
import DiagonaLean.AmbigCFG.Basic
import DiagonaLean.Synthetic.ReduceToPCP

@[expose] public section

/-! #  PCP ⪯ₘ AmbigCFG

Reduction from PCP to CFG ambiguity. Given a PCP instance `P`, the grammar `P.toGrammar` is
ambiguous iff `P` has a solution. The main result is `pcp_iff_ambigcfg`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
  Theorem 9.20.
-/

variable {α : Type} [DecidableEq α]

namespace DiagonaLean.PCP

/-- The terminal alphabet for a PCP instance `P`: original symbols `α` together with one index token
  `aᵢ` per tile. -/
abbrev PCPAlpha (P : Stack α) : Type := Sum α (Fin P.length)

/-- Nonterminals of the combined PCP grammar. `S` is the fresh start symbol; `A` generates top-
  word encodings; `B` generates bottom-word encodings. -/
inductive PCPNonterm | S | A | B
  deriving DecidableEq, Repr

open PCPNonterm in
instance : Fintype PCPNonterm where
  elems := {S, A, B}
  complete x := by cases x <;> simp

/-- Inject a word over `α` into terminal symbols of `PCPAlpha P`. -/
def liftWord {P : Stack α} (w : List α) : List (Symbol (PCPAlpha P) PCPNonterm) :=
  w.map (Symbol.terminal ∘ Sum.inl)

/-- The index terminal `aᵢ` for tile `i`. -/
abbrev idxSym {P : Stack α} (i : Fin P.length) : Symbol (PCPAlpha P) PCPNonterm :=
  Symbol.terminal (Sum.inr i)

/-- Recursive production `v → w · v · aᵢ`. -/
def recProd (v : PCPNonterm) {P : Stack α} (i : Fin P.length) (w : List α) :
    ContextFreeRule (PCPAlpha P) PCPNonterm where
  input  := v
  output := liftWord w ++ [Symbol.nonterminal v, idxSym i]

/-- Base production `v → w · aᵢ`. -/
def baseProd (v : PCPNonterm) {P : Stack α} (i : Fin P.length) (w : List α) :
    ContextFreeRule (PCPAlpha P) PCPNonterm where
  input  := v
  output := liftWord w ++ [idxSym i]

/-- For each tile `i`: `A → top(i) · A · aᵢ` and `A → top(i) · aᵢ`. -/
def rulesA (P : Stack α) : Finset (ContextFreeRule (PCPAlpha P) PCPNonterm) :=
  Finset.univ.biUnion fun i : Fin P.length =>
    {recProd PCPNonterm.A i P[i].top, baseProd PCPNonterm.A i P[i].top}

/-- For each tile `i`: `B → bot(i) · B · aᵢ` and `B → bot(i) · aᵢ`. -/
def rulesB (P : Stack α) : Finset (ContextFreeRule (PCPAlpha P) PCPNonterm) :=
  Finset.univ.biUnion fun i : Fin P.length =>
    {recProd PCPNonterm.B i P[i].bot, baseProd PCPNonterm.B i P[i].bot}

/-- Start productions: `S → A` and `S → B`. -/
def rulesS (P : Stack α) : Finset (ContextFreeRule (PCPAlpha P) PCPNonterm) :=
  { ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.A]⟩,
    ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.B]⟩ }

/-- The grammar whose language is `τ1`-encodings: initial nonterminal `A`, rules `rulesA P`. -/
def Stack.τ1.toGrammar (P : Stack α) : ContextFreeGrammar (PCPAlpha P) where
  NT      := PCPNonterm
  initial := PCPNonterm.A
  rules   := rulesA P

/-- The grammar whose language is `τ2`-encodings: initial nonterminal `B`, rules `rulesB P`. -/
def Stack.τ2.toGrammar (P : Stack α) : ContextFreeGrammar (PCPAlpha P) where
  NT      := PCPNonterm
  initial := PCPNonterm.B
  rules   := rulesB P

/-- The grammar `G(P)` for a PCP instance `P`.

`LA` consists of strings of the form `τ₁(A) ++ aᵢₘ … aᵢ₁`
and `LB` of strings of the form `τ₂(A) ++ aᵢₘ … aᵢ₁`
for a common reversed index sequence. A string lies in `LA ∩ LB`
iff the tiles `i₁, …, iₘ` form a PCP solution.
Such a string has two parse trees from `S` (one via `A`, one via `B`), so:

**`G(P).Ambiguous ↔ HasSolution P`** (proved separately) -/
def Stack.toGrammar (P : Stack α) : ContextFreeGrammar (PCPAlpha P) where
  NT      := PCPNonterm
  initial := PCPNonterm.S
  rules   := rulesS P ∪ rulesA P ∪ rulesB P

end DiagonaLean.PCP

namespace DiagonaLean.AmbigCFG.Reduction
open DiagonaLean.PCP DiagonaLean.AmbigCFG

variable {P : Stack α}

/-- The word encoded by a (possibly empty) index list `is` in the **top** grammar:
`encodeA [i₁, i₂, …, iₘ] = w_{i₁} w_{i₂} … w_{iₘ} aᵢₘ … aᵢ₂ aᵢ₁`,
i.e. top-words in forward order, index tokens in reverse order. -/
def encodeA (is : List (Fin P.length)) : List (PCPAlpha P) :=
  (τ1 (is.map (P[·]))).map Sum.inl ++ is.reverse.map Sum.inr

/-- Same encoding for the **bot** grammar:
`encodeB [i₁, i₂, …, iₘ] = x_{i₁} x_{i₂} … x_{iₘ} aᵢₘ … aᵢ₂ aᵢ₁`. -/
def encodeB (is : List (Fin P.length)) : List (PCPAlpha P) :=
  (τ2 (is.map (P[·]))).map Sum.inl ++ is.reverse.map Sum.inr

omit [DecidableEq α] in
/-- `encodeA` of the empty index list is empty. -/
@[simp]
theorem encodeA_nil (P : Stack α) : encodeA ([] : List (Fin P.length)) = [] := by simp [encodeA]

omit [DecidableEq α] in
/-- `encodeB` of the empty index list is empty. -/
@[simp]
theorem encodeB_nil (P : Stack α) : encodeB ([] : List (Fin P.length)) = [] := by simp [encodeB]

omit [DecidableEq α] in
/-- `encodeA (i :: is) = wᵢ · encodeA is · aᵢ`,
mirroring the recursive production `A → wᵢ A aᵢ`. -/
theorem encodeA_cons (i : Fin P.length) (is : List (Fin P.length)) :
    encodeA (i :: is) = P[i].top.map Sum.inl ++ encodeA is ++ [Sum.inr i] := by
  simp [encodeA, List.map_append, List.reverse_cons, List.append_assoc]

omit [DecidableEq α] in
/-- `encodeB (i :: is) = xᵢ · encodeB is · aᵢ`,
mirroring the recursive production `B → xᵢ B aᵢ`. -/
theorem encodeB_cons (i : Fin P.length) (is : List (Fin P.length)) :
    encodeB (i :: is) = P[i].bot.map Sum.inl ++ encodeB is ++ [Sum.inr i] := by
  simp [encodeB, List.map_append, List.reverse_cons, List.append_assoc]

omit [DecidableEq α] in
/-- `encodeA [i] = wᵢ · aᵢ`, the singleton case of `encodeA_cons`. -/
theorem encodeA_singleton (i : Fin P.length) :
    encodeA [i] = P[i].top.map Sum.inl ++ [Sum.inr i] := by
  simp [encodeA_cons]

omit [DecidableEq α] in
/-- `encodeB [i] = xᵢ · aᵢ`, the singleton case of `encodeB_cons`. -/
theorem encodeB_singleton (i : Fin P.length) :
    encodeB [i] = P[i].bot.map Sum.inl ++ [Sum.inr i] := by
  simp [encodeB_cons]

omit [DecidableEq α] in
/-- `encodeA is = encodeB is` iff `τ1` and `τ2` agree on the chosen sub-stack. -/
theorem encodeA_eq_encodeB_iff {P : Stack α} {is : List (Fin P.length)} :
    encodeA is = encodeB is ↔
    τ1 (is.map (P[·])) = τ2 (is.map (P[·])) := by
  simp only [encodeA, encodeB, List.append_left_inj]
  apply Function.Injective.eq_iff ?_
  apply Function.Injective.list_map ?_
  exact Sum.inl_injective

/-- Extract the index sequence from an encoded word: keep the right-injections
(index tokens) and reverse. -/
def idxOf (w : List (PCPAlpha P)) : List (Fin P.length) :=
  (w.filterMap Sum.getRight?).reverse

omit [DecidableEq α] in
/-- `idxOf` is a left inverse of `encodeA`. -/
theorem idxOf_encodeA (is : List (Fin P.length)) : idxOf (encodeA is) = is := by
  induction is <;> simp_all +decide [ idxOf, encodeA ]

omit [DecidableEq α] in
/-- `idxOf` is a left inverse of `encodeB`. -/
theorem idxOf_encodeB (is : List (Fin P.length)) : idxOf (encodeB is) = is := by
  unfold idxOf;
  induction is <;> simp_all +decide [ encodeB_cons, List.filterMap ]

omit [DecidableEq α] in
/-- `encodeA` is injective. -/
theorem encodeA_injective : Function.Injective (encodeA (P := P)) := by
  intro is js h
  have := congr_arg ( idxOf ( P := P ) ) h; simp +decide [ idxOf_encodeA ] at this; aesop

omit [DecidableEq α] in
/-- If a top-encoding equals a bot-encoding, the index lists coincide and
the chosen sub-stack is a PCP solution. -/
theorem encodeA_eq_encodeB_cross {is js : List (Fin P.length)}
    (h : encodeA is = encodeB js) :
    is = js ∧ τ1 (is.map (P[·])) = τ2 (is.map (P[·])) := by
  convert idxOf_encodeA is;
  grind +suggestions

/-- `baseProd PCPNonterm.A i P[i].top` belongs to `(Stack.toGrammar P).rules`. -/
private lemma baseA_mem (i : Fin P.length) :
    baseProd PCPNonterm.A i P[i].top ∈ (Stack.toGrammar P).rules := by
  simp only [Stack.toGrammar]
  apply Finset.mem_union.mpr; left
  apply Finset.mem_union.mpr; right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩

/-- `recProd PCPNonterm.A i P[i].top` belongs to `(Stack.toGrammar P).rules`. -/
private lemma recA_mem (i : Fin P.length) :
    recProd PCPNonterm.A i P[i].top ∈ (Stack.toGrammar P).rules := by
  simp only [Stack.toGrammar]
  apply Finset.mem_union.mpr; left
  apply Finset.mem_union.mpr; right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩

/-- `baseProd PCPNonterm.B i P[i].bot` belongs to `(Stack.toGrammar P).rules`. -/
private lemma baseB_mem (i : Fin P.length) :
    baseProd PCPNonterm.B i P[i].bot ∈ (Stack.toGrammar P).rules := by
  simp only [Stack.toGrammar]
  apply Finset.mem_union.mpr; right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩

/-- `recProd PCPNonterm.B i P[i].bot` belongs to `(Stack.toGrammar P).rules`. -/
private lemma recB_mem (i : Fin P.length) :
    recProd PCPNonterm.B i P[i].bot ∈ (Stack.toGrammar P).rules := by
  simp only [Stack.toGrammar]
  apply Finset.mem_union.mpr; right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩

/-- `S → A` belongs to `(Stack.toGrammar P).rules`. -/
private lemma SA_mem :
    (⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.A]⟩ :
      ContextFreeRule (PCPAlpha P) PCPNonterm) ∈ (Stack.toGrammar P).rules := by
  simp only [Stack.toGrammar]
  apply Finset.mem_union.mpr; left
  apply Finset.mem_union.mpr; left
  simp [rulesS]

/-- `S → B` belongs to `(Stack.toGrammar P).rules`. -/
private lemma SB_mem :
    (⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.B]⟩ :
      ContextFreeRule (PCPAlpha P) PCPNonterm) ∈ (Stack.toGrammar P).rules := by
  simp only [Stack.toGrammar]
  apply Finset.mem_union.mpr; left
  apply Finset.mem_union.mpr; left
  simp [rulesS]

/-- Every rule of the combined grammar is one of: `S → A`, `S → B`,
`recProd A i`, `baseProd A i`, `recProd B i`, or `baseProd B i`. -/
theorem rule_shape {r : ContextFreeRule (PCPAlpha P) PCPNonterm}
    (hr : r ∈ (Stack.toGrammar P).rules) :
    r = ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.A]⟩ ∨
    r = ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.B]⟩ ∨
    (∃ i, r = recProd PCPNonterm.A i P[i].top) ∨
    (∃ i, r = baseProd PCPNonterm.A i P[i].top) ∨
    (∃ i, r = recProd PCPNonterm.B i P[i].bot) ∨
    (∃ i, r = baseProd PCPNonterm.B i P[i].bot) := by
  have hr' : r ∈ rulesS P ∪ rulesA P ∪ rulesB P := hr
  simp only [rulesS, rulesA, rulesB,
             Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
             Finset.mem_biUnion, Finset.mem_univ, true_and] at hr'
  grind

/-- The all-terminal forest for a base production `v → w · aᵢ`. -/
def liftForestBase (i : Fin P.length) (w : List α) :
    (Stack.toGrammar P).Forest (liftWord w ++ [idxSym i]) :=
  match w with
  | [] => .consT (Sum.inr i) .nil
  | a :: rest => .consT (Sum.inl a) (liftForestBase i rest)

/-- The forest for a recursive production `v → w · v · aᵢ`, given a subtree at `v`. -/
def liftForestRec (v : PCPNonterm) (i : Fin P.length) (w : List α)
    (child : (Stack.toGrammar P).ParseTree v) :
    (Stack.toGrammar P).Forest (liftWord w ++ [Symbol.nonterminal v, idxSym i]) :=
  match w with
  | [] => .consN child (.consT (Sum.inr i) .nil)
  | a :: rest => .consT (Sum.inl a) (liftForestRec v i rest child)

/-- The yield of `liftForestBase i w` is `w.map Sum.inl ++ [Sum.inr i]`. -/
theorem liftForestBase_yield (i : Fin P.length) (w : List α) :
    (liftForestBase (P := P) i w).yield = w.map Sum.inl ++ [Sum.inr i] := by
  induction w <;> simp_all +decide [ liftForestBase, ContextFreeGrammar.Forest.yield ]
  expose_names
  exact List.reverse_inj.mp (congrArg List.reverse tail_ih)

/-- The yield of `liftForestRec v i w child` is `w.map Sum.inl ++ child.yield ++ [Sum.inr i]`. -/
theorem liftForestRec_yield (v : PCPNonterm) (i : Fin P.length) (w : List α)
    (child : (Stack.toGrammar P).ParseTree v) :
    (liftForestRec v i w child).yield = w.map Sum.inl ++ (child.yield ++ [Sum.inr i]) := by
  induction w <;> simp_all +decide [ liftForestRec, ContextFreeGrammar.Forest.yield ]
  expose_names
  exact List.reverse_inj.mp (congrArg List.reverse tail_ih)

/-- Canonical parse tree rooted at `A` for a nonempty index list. -/
def buildA : (is : List (Fin P.length)) → is ≠ [] → (Stack.toGrammar P).ParseTree PCPNonterm.A
  | [i], _ =>
      @.node _ (Stack.toGrammar P) (baseProd PCPNonterm.A i P[i].top) (baseA_mem i)
        (liftForestBase i P[i].top)
  | i :: j :: rest, _ =>
      @.node _ (Stack.toGrammar P) (recProd PCPNonterm.A i P[i].top) (recA_mem i)
        (liftForestRec PCPNonterm.A i P[i].top (buildA (j :: rest) (by simp)))

/-- Canonical parse tree rooted at `B` for a nonempty index list. -/
def buildB : (is : List (Fin P.length)) → is ≠ [] → (Stack.toGrammar P).ParseTree PCPNonterm.B
  | [i], _ =>
      @.node _ (Stack.toGrammar P) (baseProd PCPNonterm.B i P[i].bot) (baseB_mem i)
        (liftForestBase i P[i].bot)
  | i :: j :: rest, _ =>
      @.node _ (Stack.toGrammar P) (recProd PCPNonterm.B i P[i].bot) (recB_mem i)
        (liftForestRec PCPNonterm.B i P[i].bot (buildB (j :: rest) (by simp)))

/-- The yield of `buildA is h` is `encodeA is`. -/
theorem buildA_yield : ∀ (is : List (Fin P.length)) (h : is ≠ []),
    (buildA is h).yield = encodeA is := by
  intro is h
  induction' n : is.length using Nat.strong_induction_on with n ih generalizing is
  rcases is with ( _ | ⟨ i, _ | ⟨ j, is ⟩ ⟩ ) <;> simp_all +decide [ encodeA_cons ] ;
  · contradiction;
  · convert liftForestBase_yield i P[i].top using 1; exact List.toList_toArray;
    exact (List.append_right_inj (List.map Sum.inl P[↑i].top)).mpr rfl
  · convert liftForestRec_yield PCPNonterm.A i P[i].top (
      buildA ( j :: is ) ( by simp ) ) using 1; exact List.toList_toArray; grind +suggestions

/-- The yield of `buildB is h` is `encodeB is`. -/
theorem buildB_yield : ∀ (is : List (Fin P.length)) (h : is ≠ []),
    (buildB is h).yield = encodeB is := by
  intro is;
  induction' is with i is ih;
  · tauto;
  · cases is <;> simp_all +decide [ encodeB_cons ];
    · convert liftForestBase_yield i P[i].bot using 1; exact List.toList_toArray;
      exact (List.append_right_inj (List.map Sum.inl P[↑i].bot)).mpr rfl
    · convert liftForestRec_yield PCPNonterm.B i P[i].bot (
        buildB ( ‹_› :: ‹_› ) ( by simp ) ) using 1; exact List.toList_toArray
      grind

/-- The unique forest over an empty symbol list is `.nil`. -/
theorem forest_nil_inv (f : (Stack.toGrammar P).Forest []) :
    f = .nil := by
  cases f; rfl

/-- Any forest headed by a terminal `t` is `.consT t rest` for some `rest`. -/
theorem forest_consT_inv {t : PCPAlpha P}
    {ss : List (Symbol (PCPAlpha P) PCPNonterm)}
    (f : (Stack.toGrammar P).Forest (Symbol.terminal t :: ss)) :
    ∃ rest, f = .consT t rest := by
  cases f with
  | consT t rest => exact ⟨rest, rfl⟩

/-- Any forest headed by a nonterminal `n` is `.consN child rest` for some `child` and `rest`. -/
theorem forest_consN_inv {n : PCPNonterm}
    {ss : List (Symbol (PCPAlpha P) PCPNonterm)}
    (f : (Stack.toGrammar P).Forest (Symbol.nonterminal n :: ss)) :
    ∃ (child : (Stack.toGrammar P).ParseTree n), ∃ rest, f = .consN child rest := by
  cases f with
  | consN child rest => exact ⟨child, rest, rfl⟩

/-- Any forest matching the shape of a base production is `liftForestBase i w`. -/
theorem forest_base_eq (i : Fin P.length) (w : List α)
    (f : (Stack.toGrammar P).Forest (liftWord w ++ [idxSym i])) :
    f = liftForestBase i w := by
  revert f;
  induction' w with a w ih;
  · intro f
    obtain ⟨ rest, hf ⟩ := forest_consT_inv f
    have hrest : rest = .nil := forest_nil_inv rest
    simp [hrest] at hf; exact hf;
  · intro f
    obtain ⟨rest, hrest⟩ := forest_consT_inv f;
    exact hrest.trans ( congr_arg _ ( ih rest ) )

/-- Any forest matching the shape of a recursive production is `liftForestRec v i w child`
for some subtree `child`. -/
theorem forest_rec_eq (v : PCPNonterm) (i : Fin P.length) (w : List α)
    (f : (Stack.toGrammar P).Forest (liftWord w ++ [Symbol.nonterminal v, idxSym i])) :
    ∃ child, f = liftForestRec v i w child := by
  induction w;
  · obtain ⟨ child, rest, h ⟩ := forest_consN_inv f;
    obtain ⟨ rest, h ⟩ := forest_consT_inv rest;
    exact ⟨ child, by cases forest_nil_inv rest; aesop ⟩;
  · obtain ⟨ rest, hrest ⟩ := forest_consT_inv f;
    obtain ⟨ child, hchild ⟩ := ‹∀ ( f : P.toGrammar.Forest
      ( liftWord _ ++ [ Symbol.nonterminal v, idxSym i ] ) ),
        ∃ child, f = liftForestRec v i _ child› rest;
        use child; aesop;

/-- One-step inversion of a parse tree rooted at `A`: it uses either a base or
recursive production for some tile `i`. -/
theorem ptA_inv {n : PCPNonterm} (t : (Stack.toGrammar P).ParseTree n)
    (hn : n = PCPNonterm.A) :
    (∃ i, HEq t (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
      (baseProd PCPNonterm.A i P[i].top)
        (baseA_mem i) (liftForestBase i P[i].top))) ∨
    (∃ i, ∃ child : (Stack.toGrammar P).ParseTree PCPNonterm.A,
        HEq t (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
          (recProd PCPNonterm.A i P[i].top)
            (recA_mem i) (liftForestRec PCPNonterm.A i P[i].top child))) := by
  obtain ⟨ r, hr, c ⟩ := t;
  rcases rule_shape hr with ( rfl | rfl | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ ) <;>
    norm_num at hn;
  all_goals simp_all +decide [ recProd, baseProd ];
  · obtain ⟨ child, hchild ⟩ := forest_rec_eq PCPNonterm.A i P[i].top c;
    use Or.inr ⟨ i, child, by aesop ⟩ ;
  · exact Or.inl ⟨ i, by congr; exact forest_base_eq i P[i].top c ⟩

/-- One-step inversion of a parse tree rooted at `B`: it uses either a base or
recursive production for some tile `i`. -/
theorem ptB_inv {n : PCPNonterm} (t : (Stack.toGrammar P).ParseTree n)
    (hn : n = PCPNonterm.B) :
    (∃ i, HEq t (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
      (baseProd PCPNonterm.B i P[i].bot)
        (baseB_mem i) (liftForestBase i P[i].bot))) ∨
    (∃ i, ∃ child : (Stack.toGrammar P).ParseTree PCPNonterm.B,
        HEq t (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
          (recProd PCPNonterm.B i P[i].bot)
            (recB_mem i) (liftForestRec PCPNonterm.B i P[i].bot child))) := by
  obtain ⟨ r, hr, c ⟩ := t;
  rcases rule_shape hr with ( rfl | rfl | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ ) <;>
    norm_num at hn;
  all_goals cases hn;
  · obtain ⟨ child, hchild ⟩ := forest_rec_eq PCPNonterm.B i P[i].bot c;
    use Or.inr ⟨ i, child, by aesop ⟩ ;
  · exact Or.inl ⟨ i, by congr; exact forest_base_eq i P[i].bot c ⟩

/-- Inversion of a parse tree rooted at `S`: it uses `S → A` or `S → B`. -/
theorem ptS_inv {n : PCPNonterm} (t : (Stack.toGrammar P).ParseTree n)
    (hn : n = PCPNonterm.S) :
    (∃ child : (Stack.toGrammar P).ParseTree PCPNonterm.A,
        HEq t (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
          ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.A]⟩ SA_mem
          (.consN child .nil))) ∨
    (∃ child : (Stack.toGrammar P).ParseTree PCPNonterm.B,
        HEq t (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
          ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.B]⟩ SB_mem
          (.consN child .nil))) := by
  rcases t with ⟨ r, hr, c ⟩ ;
  rcases rule_shape hr with ( rfl | rfl | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ ) <;>
    simp +decide at hn ⊢;
  all_goals cases hn;
  · obtain ⟨ child, rest, h ⟩ := forest_consN_inv c;
    use Or.inl ⟨ child, by cases forest_nil_inv rest; aesop ⟩ ;
  · obtain ⟨ child, rest, h ⟩ := forest_consN_inv c;
    use Or.inr ⟨ child, by cases forest_nil_inv rest; aesop ⟩ ;

/-- Every `A`-rooted parse tree is `buildA is h` for some nonempty index list `is`. -/
theorem ptA_char {n : PCPNonterm} (t : (Stack.toGrammar P).ParseTree n)
    (hn : n = PCPNonterm.A) :
    ∃ (is : List (Fin P.length)) (h : is ≠ []), HEq t (buildA is h) := by
  revert t;
  induction' n with n ih;
  · cases hn;
  · intro t;
    induction' n : t.yield.length using Nat.strong_induction_on with n ih generalizing t;
    rcases ptA_inv t rfl with ( ⟨ i, hi ⟩ | ⟨ i, child, hi ⟩ );
    · use [i]; exact ⟨ by simp +decide, hi ⟩;
    · have h_child : child.yield.length < t.yield.length := by
        have h_child : t.yield = P[i].top.map Sum.inl ++ (child.yield ++ [Sum.inr i]) := by
          convert liftForestRec_yield PCPNonterm.A i P[i].top child using 1;
          convert congr_arg ( fun x : P.toGrammar.ParseTree PCPNonterm.A => x.yield )
            ( eq_of_heq hi ) using 1;
          exact List.toList_toArray
        simp +arith +decide [ h_child ];
      obtain ⟨ is, h, hi ⟩ := ih _ ( by linarith ) child rfl;
      use i :: is;
      cases is <;> simp_all +decide [ buildA ];
      contradiction; expose_names; grind
  · cases hn

/-- Every `B`-rooted parse tree is `buildB is h` for some nonempty index list `is`. -/
theorem ptB_char {n : PCPNonterm} (t : (Stack.toGrammar P).ParseTree n)
    (hn : n = PCPNonterm.B) :
    ∃ (is : List (Fin P.length)) (h : is ≠ []), HEq t (buildB is h) := by
  induction' n with n ih;
  · cases hn;
  · cases hn;
  · have h_ind : ∀ (n : ℕ) (t : (Stack.toGrammar P).ParseTree PCPNonterm.B),
        t.yield.length = n → ∃ is : List (Fin P.length), ∃ h : is ≠ [], t ≍ buildB is h := by
      intro n
      induction' n using Nat.strong_induction_on with n ih
      intro t ht
      rcases ptB_inv t rfl with ( ⟨ i, hi ⟩ | ⟨ i, child, hi ⟩ );
      · use [i]; exact ⟨ by simp +decide, hi ⟩;
      · have h_child : child.yield.length < n := by
          have h_child : t.yield = P[i].bot.map Sum.inl ++ (child.yield ++ [Sum.inr i]) := by
            convert liftForestRec_yield PCPNonterm.B i P[i].bot child using 1;
            convert congr_arg ( fun x : P.toGrammar.ParseTree PCPNonterm.B => x.yield )
              ( eq_of_heq hi ) using 1;
            exact List.toList_toArray
          simp +arith +decide [ h_child ] at ht ⊢ ; linarith;
        obtain ⟨ is, h, h_child_eq ⟩ := ih _ h_child child rfl;
        rcases is with ( _ | ⟨ j, is ⟩ ) <;> simp_all +decide;
        · contradiction;
        · exact ⟨ i :: j :: is, by simp +decide, eq_of_heq hi ⟩;
    exact h_ind _ _ rfl

/-- `A`-rooted trees with equal yields are equal: the `A`-grammar is unambiguous. -/
theorem ptA_yield_inj (t₁ t₂ : (Stack.toGrammar P).ParseTree PCPNonterm.A)
    (hy : t₁.yield = t₂.yield) : t₁ = t₂ := by
  obtain ⟨is₁, h₁, he₁⟩ := ptA_char t₁ rfl
  obtain ⟨is₂, h₂, he₂⟩ := ptA_char t₂ rfl
  have e₁ := eq_of_heq he₁; have e₂ := eq_of_heq he₂
  rw [e₁, e₂] at hy ⊢
  rw [buildA_yield, buildA_yield] at hy
  have : is₁ = is₂ := encodeA_injective hy
  subst this; rfl

/-- `B`-rooted trees with equal yields are equal: the `B`-grammar is unambiguous. -/
theorem ptB_yield_inj (t₁ t₂ : (Stack.toGrammar P).ParseTree PCPNonterm.B)
    (hy : t₁.yield = t₂.yield) : t₁ = t₂ := by
  obtain ⟨is₁, h₁, he₁⟩ := ptB_char t₁ rfl
  obtain ⟨is₂, h₂, he₂⟩ := ptB_char t₂ rfl
  have e₁ := eq_of_heq he₁; have e₂ := eq_of_heq he₂
  rw [e₁, e₂] at hy ⊢
  rw [buildB_yield, buildB_yield] at hy
  have hb : encodeB is₁ = encodeB is₂ := hy
  have : is₁ = is₂ := by
    have := congrArg (idxOf (P := P)) hb
    rwa [idxOf_encodeB, idxOf_encodeB] at this
  subst this; rfl

/-- The yield of an `S → A` node equals the yield of its `A`-child. -/
theorem yield_SA (child : (Stack.toGrammar P).ParseTree PCPNonterm.A) :
    (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
      ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.A]⟩ SA_mem
      (.consN child .nil)).yield = child.yield := by
  simp +decide [ ContextFreeGrammar.ParseTree.yield, ContextFreeGrammar.Forest.yield ]

/-- The yield of an `S → B` node equals the yield of its `B`-child. -/
theorem yield_SB (child : (Stack.toGrammar P).ParseTree PCPNonterm.B) :
    (@ContextFreeGrammar.ParseTree.node _ (Stack.toGrammar P)
      ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.B]⟩ SB_mem
      (.consN child .nil)).yield = child.yield := by
  simp +decide [ ContextFreeGrammar.ParseTree.yield, ContextFreeGrammar.Forest.yield ]

omit [DecidableEq α] in
/-- Any sub-stack of `P` is `is.map (P[·])` for some index list `is`. -/
theorem exists_indexList (L : Stack α) (hsub : ∀ t ∈ L, t ∈ P) :
    ∃ is : List (Fin P.length), is.map (fun i => P[i]) = L := by
  induction' L with t L ih;
  · exact ⟨ [ ], rfl ⟩;
  · obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp ( hsub t ( by simp +decide ) );
    exact Exists.elim ( ih fun t ht => hsub t ( List.mem_cons_of_mem _ ht ) )
      fun is his => ⟨ i :: is, by aesop ⟩

/-- If `P` has a solution then `toGrammar P` is ambiguous. -/
theorem ambiguous_if_pcp (h : PCP.DecisionProblem P) : (Stack.toGrammar P).Ambiguous := by
  obtain ⟨ L, hLne, hLsub, hLeq ⟩ := h;
  obtain ⟨ is, hmap ⟩ := exists_indexList L hLsub;
  refine' ⟨ _, _, _, _ ⟩;
  exact @ContextFreeGrammar.ParseTree.node _ ( Stack.toGrammar P ) ⟨ PCPNonterm.S,
    [ Symbol.nonterminal PCPNonterm.A ] ⟩ SA_mem ( .consN ( buildA is ( by grind ) ) .nil )
  exact @ContextFreeGrammar.ParseTree.node _ ( Stack.toGrammar P ) ⟨ PCPNonterm.S,
    [ Symbol.nonterminal PCPNonterm.B ] ⟩ SB_mem ( .consN ( buildB is ( by grind ) ) .nil )
  exact (by all_goals generalize_proofs at *; grind)
  exact (by
    all_goals generalize_proofs at *;
    erw [yield_SA, yield_SB, buildA_yield, buildB_yield]
    exact encodeA_eq_encodeB_iff.mpr ( by aesop ))

/-- If `toGrammar P` is ambiguous then `P` has a solution. -/
theorem pcp_if_ambiguous (h : (Stack.toGrammar P).Ambiguous) : PCP.DecisionProblem P := by
  obtain ⟨t1, t2, hne, hyield⟩ := h;
  rcases ptS_inv t1 rfl with ( ⟨cA1, heq1⟩ | ⟨cB1, heq1⟩ );
  rcases ptS_inv t2 rfl with ( ⟨cA2, heq2⟩ | ⟨cB2, heq2⟩ );
  · refine False.elim (hne ?_)
    rw [eq_of_heq heq1, eq_of_heq heq2] at hyield ⊢
    erw [yield_SA, yield_SA] at hyield
    rw [ptA_yield_inj cA1 cA2 hyield]
  · have h_yield_eq : cA1.yield = cB2.yield := by
      erw [ eq_of_heq heq1, eq_of_heq heq2, yield_SA, yield_SB ] at hyield ; exact hyield;
    obtain ⟨is1, his1, hcA1⟩ := ptA_char cA1 rfl
    obtain ⟨is2, his2, hcB2⟩ := ptB_char cB2 rfl
    have h_encode_eq : encodeA is1 = encodeB is2 := by
      rw [ ← buildA_yield is1 his1, ← buildB_yield is2 his2, ← eq_of_heq hcA1,
            ← eq_of_heq hcB2, h_yield_eq ];
    obtain ⟨h_is1, h_τ⟩ := encodeA_eq_encodeB_cross h_encode_eq;
    exact ⟨ List.map ( fun x => P[x] ) is1, by aesop ⟩;
  · rcases ptS_inv t2 rfl with ( ⟨ cA2, heq2 ⟩ | ⟨ cB2, heq2 ⟩ ) <;> simp_all +decide;
    · cases heq1; cases heq2
      erw [ yield_SB, yield_SA ] at hyield;
      obtain ⟨is1, h1, he1⟩ := ptB_char cB1 rfl
      obtain ⟨is2, h2, he2⟩ := ptA_char cA2 rfl
      have e1 := eq_of_heq he1; have e2 := eq_of_heq he2
      rw [e1, e2] at hyield
      rw [buildB_yield, buildA_yield] at hyield
      have := encodeA_eq_encodeB_cross hyield.symm
      use is2.map (fun i => P[i]);
      simp_all +decide [ List.map_eq_nil_iff ]; grind;
    · exact False.elim <| hne <| by
        cases heq1; cases heq2
        erw [ yield_SB, yield_SB ] at hyield; exact ptB_yield_inj cB1 cB2 hyield ▸ rfl;

/-- `toGrammar P` is ambiguous iff `P` has a solution. -/
theorem pcp_iff_ambigcfg (P : Stack α) :
    PCP.DecisionProblem P ↔ (P.toGrammar).Ambiguous :=
  ⟨ambiguous_if_pcp, pcp_if_ambiguous⟩

open DiagonaLean.Synthetic.Notation

/-- Ambiguity of the family of context-free grammars `P.toGrammar` (indexed by
`P : Stack α`) is undecidable. Reduced from PCP over the same alphabet `α` by the
identity function on stacks, with `ambiguous_if_pcp`/`pcp_if_ambiguous` supplying the
two directions of the correctness equivalence. -/
theorem ambigcfg_undecidable [Nontrivial α] :
    Undecidable (fun (P : Stack α) => (P.toGrammar).Ambiguous) := by
  reduceToPCP over_type α
    with_red_function (fun P => P)
    using_lemmas ambiguous_if_pcp pcp_if_ambiguous

end DiagonaLean.AmbigCFG.Reduction
