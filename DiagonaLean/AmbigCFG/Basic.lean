/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

/-! # Ambiguity of CFGs

Central notions/types and predicates for the CFG ambiguity decision problem.

Formalizes parse trees (`ParseTree`) and derivation forests (`Forest`) for context-free grammars.
Defines the terminal `yield` of a parse tree and `DecisionProblem`, the property of a grammar
being ambiguous (having multiple distinct parse trees for the same string).

This is one of the standard problems shown undecidable by reduction from PCP
(see [HopcroftMotwaniUllman2006] Theorem 9.20).

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace ContextFreeGrammar

universe u variable {T : Type u}

mutual
  /-- A parse tree for the grammar `G` rooted at the nonterminal `n`. -/
  inductive ParseTree (G : ContextFreeGrammar T) : G.NT → Type u
    | node (r : ContextFreeRule T G.NT) (hr : r ∈ G.rules) (children : Forest G r.output) :
        ParseTree G r.input

  /-- A sequence of subtrees corresponding to the symbol list `ss`. Terminals are stored
    directly. -/
  inductive Forest (G : ContextFreeGrammar T) : List (Symbol T G.NT) → Type u
    | nil : Forest G []
    | consT (t : T) (rest : Forest G ss) : Forest G (Symbol.terminal t :: ss)
    | consN {n : G.NT} (tree : ParseTree G n) (rest : Forest G ss) :
        Forest G (Symbol.nonterminal n :: ss)
end

mutual
  /-- The terminal word read sequentially off the leaves of the parse tree. -/
  def ParseTree.yield {G : ContextFreeGrammar T} {n : G.NT} : G.ParseTree n → List T
    | .node _ _ children => children.yield

  /-- The sequentially concatenated yield of a forest of subtrees. -/
  def Forest.yield {G : ContextFreeGrammar T} {ss : List (Symbol T G.NT)} : G.Forest ss → List T
    | .nil           => []
    | .consT t rest  => t :: rest.yield
    | .consN tr rest => tr.yield ++ rest.yield
end

/-- A grammar is ambiguous if a terminal word has at least two distinct parse trees generated from
  the start symbol. -/
def DecisionProblem (G : ContextFreeGrammar T) : Prop :=
  ∃ (t1 t2 : G.ParseTree G.initial), t1 ≠ t2 ∧ t1.yield = t2.yield

end ContextFreeGrammar

namespace DiagonaLean.AmbigCFG

/-- The decision problem of whether a given context-free grammar is ambiguous. -/
abbrev DecisionProblem : ContextFreeGrammar T → Prop := ContextFreeGrammar.DecisionProblem

end DiagonaLean.AmbigCFG
