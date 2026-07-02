/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

namespace ContextFreeGrammar

universe u variable {T : Type u}

mutual
  /-- A parse tree for `g` rooted at nonterminal `n`. -/
  inductive ParseTree (G : ContextFreeGrammar T) : G.NT → Type u
    | node (r : ContextFreeRule T G.NT) (hr : r ∈ G.rules) (children : Forest G r.output) :
        ParseTree G r.input

  /-- One subtree per symbol in `ss`; terminals are stored directly. -/
  inductive Forest (G : ContextFreeGrammar T) : List (Symbol T G.NT) → Type u
    | nil : Forest G []
    | consT (t : T) (rest : Forest G ss) : Forest G (Symbol.terminal t :: ss)
    | consN {n : G.NT} (tree : ParseTree G n) (rest : Forest G ss) :
        Forest G (Symbol.nonterminal n :: ss)
end

mutual
  /-- Terminal word read off the leaves of a parse tree. -/
  def ParseTree.yield {G : ContextFreeGrammar T} {n : G.NT} : G.ParseTree n → List T
    | .node _ _ children => children.yield

  /-- Concatenated yield of a forest. -/
  def Forest.yield {G : ContextFreeGrammar T} {ss : List (Symbol T G.NT)} : G.Forest ss → List T
    | .nil           => []
    | .consT t rest  => t :: rest.yield
    | .consN tr rest => tr.yield ++ rest.yield
end

/-- A grammar is ambiguous if some terminal word has two distinct parse trees rooted at the
initial nonterminal. -/
def Ambiguous (G : ContextFreeGrammar T) : Prop :=
  ∃ (t1 t2 : G.ParseTree G.initial), t1 ≠ t2 ∧ t1.yield = t2.yield

end ContextFreeGrammar

namespace DiagonaLean.AmbigCFG
open ContextFreeGrammar

abbrev AmbigCFG : ContextFreeGrammar T → Prop := Ambiguous

end DiagonaLean.AmbigCFG
