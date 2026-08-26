/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.MPCP.Basic

@[expose] public section

/-! # Halt ⪯ₘ MPCP

Reduction from the halting problem to MPCP following the Hopcroft–Ullman construction. Solutions to
`MHasSolution (startTile tm w) (haltTiles tm)` encode halting computation histories of `tm` on `w`.
The main result is `halt_iff_mpcp`, subject to `NoBlankWrites` and `NoLeftBoundary`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.MPCP DiagonaLean.Halt

/-- The alphabet of the reduced MPCP instance, extending the tape alphabet with TM state labels, a
  halt marker, and a configuration separator. -/
inductive Alpha (Q : Type) (S : Type) where
  /-- `tape` lifts a tape symbol of the original TM. -/
  | tape  : Option S → Alpha Q S
  /-- `state` lifts a TM state (used to mark the head position in a configuration encoding). -/
  | state : Q → Alpha Q S
  /-- `halt` marks the halted TM (cslib's halting state is `none`, which has no tag; we introduce
    `halt` as the encoding's marker). -/
  | halt  : Alpha Q S
  /-- `sep` is the `#` configuration separator. -/
  | sep   : Alpha Q S
  deriving DecidableEq

@[inherit_doc Alpha.tape]  prefix:max "↟ₜ" => Alpha.tape
@[inherit_doc Alpha.state] prefix:max "↟ₛ" => Alpha.state
@[inherit_doc Alpha.sep]   notation   "#"  => Alpha.sep
@[inherit_doc Alpha.halt]  notation   "h⊥" => Alpha.halt

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Lift a list of tape symbols to the extended alphabet. -/
def liftTape (tm : SingleTapeTM Symbol) (l : List (Option Symbol)) :
    List (Alpha tm.State Symbol) :=
  l.map Alpha.tape

/-- `liftTape` of the empty list is empty. -/
@[simp]
lemma liftTape_nil (tm : SingleTapeTM Symbol) :
    liftTape tm ([] : List (Option Symbol)) = [] := rfl

/-- `liftTape` of a cons list prepends the lifted head symbol. -/
@[simp]
lemma liftTape_cons (tm : SingleTapeTM Symbol) (a : Option Symbol)
    (l : List (Option Symbol)) :
    liftTape tm (a :: l) = ↟ₜa :: liftTape tm l := rfl

/-- `liftTape` distributes over list concatenation. -/
@[simp]
lemma liftTape_append (tm : SingleTapeTM Symbol) (l1 l2 : List (Option Symbol)) :
    liftTape tm (l1 ++ l2) = liftTape tm l1 ++ liftTape tm l2 := by
  simp [liftTape, List.map_append]

/-- Flatten a `BiTape` to a list: `left.reverse ++ [head] ++ right`. -/
def biTapeToList (t : BiTape Symbol) : List (Option Symbol) :=
  t.left.toList.reverse ++ t.head :: t.right.toList

/-- Encode a running configuration `⟨some q, t⟩` as `left.reverse ++ [↟ₛq, ↟ₜhead] ++ right`,
  placing the state marker immediately before the head symbol. -/
def encodeRunningCfg (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    List (Alpha tm.State Symbol) :=
  liftTape tm t.left.toList.reverse ++ ↟ₛq :: liftTape tm (t.head :: t.right.toList)

/-- Encode a halted configuration `⟨none, t⟩` using `h⊥` in place of a state symbol. -/
def encodeHaltedCfg (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    List (Alpha tm.State Symbol) :=
  liftTape tm t.left.toList.reverse ++ h⊥ :: liftTape tm (t.head :: t.right.toList)

/- TODO: see if these encodings can be replaced by those from Halt.Encoding -/

/-- Encode an arbitrary configuration. -/
def encodeCfg (tm : SingleTapeTM Symbol) : tm.Cfg → List (Alpha tm.State Symbol)
  | ⟨some q, t⟩ => encodeRunningCfg tm q t
  | ⟨none,   t⟩ => encodeHaltedCfg tm t

/-- Wrap a configuration encoding in `#…#` separators. -/
def block (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    List (Alpha tm.State Symbol) :=
  # :: encodeCfg tm cfg ++ [#]

/-- The `#…#`-wrapped encoding of the initial configuration on input `w`. -/
def initBlock (tm : SingleTapeTM Symbol) (w : List Symbol) :
    List (Alpha tm.State Symbol) :=
  block tm (SingleTapeTM.initCfg tm w)

/-- `encodeCfg` unfolds to `encodeRunningCfg` on running configurations. -/
@[simp]
lemma encodeCfg_running (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    encodeCfg tm { state := some q, BiTape := t } = encodeRunningCfg tm q t := rfl

/-- `encodeCfg` unfolds to `encodeHaltedCfg` on halted configurations. -/
@[simp]
lemma encodeCfg_halted (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    encodeCfg tm { state := none, BiTape := t } = encodeHaltedCfg tm t := rfl

/-- The start tile: `top = [#]`, `bot = # :: encodeCfg(initCfg) ++ [#]`. Forces every MPCP solution
  to begin here, seeding the bottom with the initial configuration and establishing the simulation
  lookahead. -/
def startTile (tm : SingleTapeTM Symbol) (w : List Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [#]
  bot := # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#]

/-- Copy tile for tape symbol `a`: `top = bot = [↟ₜa]`. Advances an unchanged tape symbol from one
  configuration to the next. -/
def copyTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜa]
  bot := [↟ₜa]

/-- Separator-copy tile: `top = bot = [#]`. Copies the configuration separator. -/
def sepTile (tm : SingleTapeTM Symbol) : Tile (Alpha tm.State Symbol) where
  top := [#]
  bot := [#]

/-- Encode a possibly-halting next state: `↟ₛq'` if continuing to `q'`, `h⊥` if halting. -/
def stateMarker (tm : SingleTapeTM Symbol) :
    Option tm.State → Alpha tm.State Symbol
  | some q' => ↟ₛq'
  | none    => h⊥

/-- Transition tile for a no-move step `q a → qNew w`:
  `top = [↟ₛq, ↟ₜa]`, `bot = [stateMarker qNew, ↟ₜw]`. -/
def noMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜw]

/-- Transition tile for a right-move step in the interior:
  `top = [↟ₛq, ↟ₜa]`, `bot = [↟ₜw, stateMarker qNew]`. -/
def rightMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [↟ₜw, stateMarker tm qNew]

/-- Transition tile for a right-move step at the right boundary. Packages the closing `#` and an
  explicit blank for the new head: `top = [↟ₛq, ↟ₜa, #]`,
  `bot = [↟ₜw, stateMarker qNew, ↟ₜnone, #]`. -/
def rightMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa, #]
  bot := [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #]

/-- Transition tile for a left-move step in the interior, with `b` the symbol immediately to the
  left of the head: `top = [↟ₜb, ↟ₛq, ↟ₜa]`, `bot = [stateMarker qNew, ↟ₜb, ↟ₜw]`. -/
def leftMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜb, ↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜb, ↟ₜw]

/-- Transition tile for a left-move step at the left boundary. Inserts an explicit blank as the new
  head: `top = [↟ₛq, ↟ₜa]`, `bot = [stateMarker qNew, ↟ₜnone, ↟ₜw]`. -/
def leftMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw]

/-- Absorb tile for the symbol immediately to the left of `h⊥`: `top = [↟ₜa, h⊥]`, `bot = [h⊥]`. -/
def absorbLeftTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜa, h⊥]
  bot := [h⊥]

/-- Absorb tile for the symbol immediately to the right of `h⊥`: `top = [h⊥, ↟ₜa]`, `bot = [h⊥]`. -/
def absorbRightTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [h⊥, ↟ₜa]
  bot := [h⊥]

/-- The closing tile: `top = [h⊥, #, #]`, `bot = [#]`. Equalises top and bot after all tape symbols
  around `h⊥` have been absorbed. -/
def finalTile (tm : SingleTapeTM Symbol) : Tile (Alpha tm.State Symbol) where
  top := [h⊥, #, #]
  bot := [#]

/-- The top word of `copyTile tm a` is `[↟ₜa]`. -/
@[simp]
lemma copyTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
  (copyTile tm a).top = [↟ₜa] := rfl

/-- The bottom word of `copyTile tm a` is `[↟ₜa]`. -/
@[simp]
lemma copyTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
  (copyTile tm a).bot = [↟ₜa] := rfl

/-- The top word of `sepTile tm` is `[#]`. -/
@[simp]
lemma sepTile_top (tm : SingleTapeTM Symbol) : (sepTile tm).top = [#] := rfl

/-- The bottom word of `sepTile tm` is `[#]`. -/
@[simp]
lemma sepTile_bot (tm : SingleTapeTM Symbol) : (sepTile tm).bot = [#] := rfl

/-- `stateMarker tm (some q')` equals `↟ₛq'`. -/
@[simp]
lemma stateMarker_some (tm : SingleTapeTM Symbol) (q' : tm.State) :
  stateMarker tm (some q') = ↟ₛq' := rfl

/-- `stateMarker tm none` equals `h⊥`. -/
@[simp]
lemma stateMarker_none (tm : SingleTapeTM Symbol) :
  stateMarker tm (none : Option tm.State) = h⊥ := rfl

/-- The top word of `finalTile tm` is `[h⊥, #, #]`. -/
@[simp]
lemma finalTile_top (tm : SingleTapeTM Symbol) :
  (finalTile tm).top = [h⊥, #, #] := rfl

/-- The bottom word of `finalTile tm` is `[#]`. -/
@[simp]
lemma finalTile_bot (tm : SingleTapeTM Symbol) :
  (finalTile tm).bot = [#] := rfl

-- All copy tiles, one per tape symbol (including blank).
def enumerate (α : Type) [Fintype α] [Encodable α] : List α :=
  (List.range ((Finset.univ.image (Encodable.encode (α := α))).sup id + 1)).filterMap Encodable.decode

@[simp]
theorem mem_enumerate {α : Type} [Fintype α] [Encodable α] (a : α) : a ∈ enumerate α := by
  apply List.mem_filterMap.mpr
  refine ⟨Encodable.encode a, ?_, Encodable.encodek a⟩
  apply List.mem_range.mpr
  have h : Encodable.encode a ∈ Finset.image Encodable.encode Finset.univ :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hle : Encodable.encode a ≤ (Finset.image Encodable.encode (Finset.univ : Finset α)).sup id := by simp [Finset.le_sup]
  omega

def copyTiles (tm : SingleTapeTM Symbol) [Encodable Symbol]:
    List (Tile (Alpha tm.State Symbol)) :=
  (enumerate (Option Symbol)).map (copyTile tm)


--def copyTiles {Symbol : Type} [DecidableRel ((· ≤ ·): Option Symbol → Option Symbol → Prop)] [Inhabited Symbol] [Fintype Symbol] [LinearOrder Symbol]
--    (tm : SingleTapeTM Symbol) :
--    List (Tile (Alpha tm.State Symbol)) :=
--  (Finset.univ : Finset (Option Symbol)).sort (· ≤ ·) |>.map (copyTile tm)


/-- The left and right absorb tiles for tape symbol `a`. -/
def absorbTilesFor (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  [absorbLeftTile tm a, absorbRightTile tm a]

/-- All halt-absorb tiles, two per tape symbol. -/
def absorbTiles (tm : SingleTapeTM Symbol) [Encodable Symbol]:
    List (Tile (Alpha tm.State Symbol)) :=
  (enumerate (Option Symbol)).flatMap (absorbTilesFor tm)

/-- The transition tiles for a single `(q, a)` input pair, dispatching on the movement direction.
  Right-move produces two tiles (interior and boundary); left-move produces one tile per possible
  left-neighbour symbol. -/
def transitionTilesFor (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) [Encodable Symbol] : List (Tile (Alpha tm.State Symbol)) :=
  match tm.tr q a with
  | (⟨w, none⟩, qNew) =>
      [noMoveTile tm q a qNew w]
  | (⟨w, some Turing.Dir.right⟩, qNew) =>
      [rightMoveTile tm q a qNew w, rightMoveBoundaryTile tm q a qNew w]
  | (⟨w, some Turing.Dir.left⟩, qNew) =>
      (enumerate (Option Symbol)).map
        (fun b => leftMoveTile tm q a qNew w b)

/-- All transition tiles, ranging over every `(q, a)` input pair. -/
def transitionTiles (tm : SingleTapeTM Symbol)  [Encodable (Symbol)] [Encodable (tm.State)]:
    List (Tile (Alpha tm.State Symbol)):=
  (enumerate (tm.State × Option Symbol)).flatMap
    (fun qa => transitionTilesFor tm qa.1 qa.2)

/-- The full MPCP tile set for the reduction, excluding the start tile. Consists of copy tiles, the
  separator tile, all transition tiles, all absorb tiles, and the final tile. -/
def haltTiles (tm : SingleTapeTM Symbol) [Encodable Symbol] [Encodable tm.State] :
    Stack (Alpha tm.State Symbol) :=
  (copyTiles tm) ++
  [sepTile tm] ++
  transitionTiles tm ++
  absorbTiles tm ++
  [finalTile tm]

/-- The reduction `Halt ⪯ₘ MPCP` as a function: maps `(tm, w)` to the MPCP instance
  `(startTile tm w, haltTiles tm)`. -/
def haltToMpcp (tm : SingleTapeTM Symbol) (w : List Symbol) [Encodable tm.State] [Encodable Symbol]:
    Tile (Alpha tm.State Symbol) × Stack (Alpha tm.State Symbol) :=
  (startTile tm w, haltTiles tm)

/-- The copy tile for `a` belongs to `haltTiles tm`. -/
lemma copyTile_mem_haltTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) [Encodable tm.State] [Encodable Symbol]:
    copyTile tm a ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_; refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_; refine List.mem_append_left _ ?_
  refine List.mem_toArray.mp ?_
  simp[copyTile, copyTiles]


/-- The separator tile belongs to `haltTiles tm`. -/
lemma sepTile_mem_haltTiles (tm : SingleTapeTM Symbol) [Encodable Symbol] [Encodable tm.State] :
    sepTile tm ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_; refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The final tile belongs to `haltTiles tm`. -/
lemma finalTile_mem_haltTiles (tm : SingleTapeTM Symbol) [Encodable Symbol] [Encodable tm.State]:
    finalTile tm ∈ haltTiles tm := by
  refine List.mem_append_right _ ?_
  exact List.mem_singleton.mpr rfl

/-- The left absorb tile for `a` belongs to `haltTiles tm`. -/
lemma absorbLeftTile_mem_haltTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) [Encodable Symbol] [Encodable tm.State]:
    absorbLeftTile tm a ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_; refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ?_
  use a
  simp[absorbLeftTile, absorbTilesFor]

/-- The right absorb tile for `a` belongs to `haltTiles tm`. -/
lemma absorbRightTile_mem_haltTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) [Encodable Symbol] [Encodable tm.State]:
    absorbRightTile tm a ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_; refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ?_
  use a
  simp[absorbRightTile, absorbTilesFor]

/-- Every tile produced by `transitionTilesFor tm q a` belongs to `transitionTiles tm`. -/
lemma transitionTilesFor_subset_transitionTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (t : Tile (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (ht : t ∈ transitionTilesFor tm q a) :
    t ∈ transitionTiles tm := by
      unfold transitionTiles
      simp
      use q, a

/-- Every transition tile belongs to `haltTiles tm`. -/
lemma transitionTile_mem_haltTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (t : Tile (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (ht : t ∈ transitionTilesFor tm q a) :
    t ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_; refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  exact transitionTilesFor_subset_transitionTiles tm q a t ht

/-- `τ1` of a sequence of copy tiles equals the lifted tape list. -/
@[simp]
lemma τ1_map_copyTile (tm : SingleTapeTM Symbol) (syms : List (Option Symbol)) :
    τ1 (syms.map (copyTile tm)) = liftTape tm syms := by
  induction syms with
  | nil => rfl
  | cons a syms ih => simp [τ1_cons, ih, liftTape]

/-- `τ2` of a sequence of copy tiles equals the lifted tape list. -/
@[simp]
lemma τ2_map_copyTile (tm : SingleTapeTM Symbol) (syms : List (Option Symbol)) :
    τ2 (syms.map (copyTile tm)) = liftTape tm syms := by
  induction syms with
  | nil => rfl
  | cons a syms ih => simp [τ2_cons, ih, liftTape]

/-- Every tile in a sequence of copy tiles belongs to `haltTiles tm`. -/
lemma map_copyTile_subset_haltTiles (tm : SingleTapeTM Symbol)
    (syms : List (Option Symbol)) (t : Tile (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (ht : t ∈ syms.map (copyTile tm)) :
    t ∈ haltTiles tm := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
  exact copyTile_mem_haltTiles tm a

/-- The top word of `startTile tm w` is `[#]`. -/
@[simp]
lemma startTile_top (tm : SingleTapeTM Symbol) (w : List Symbol) :
  (startTile tm w).top = [#] := rfl

/-- The bottom word of `startTile tm w` is `# :: encodeCfg(initCfg) ++ [#]`. -/
@[simp]
lemma startTile_bot (tm : SingleTapeTM Symbol) (w : List Symbol) :
  (startTile tm w).bot =
    # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] := rfl

/-- `block tm cfg` unfolds to `# :: encodeCfg tm cfg ++ [#]`. -/
@[simp]
lemma block_eq (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
  block tm cfg = # :: encodeCfg tm cfg ++ [#] := rfl

/-- Tile sequence simulating a single no-move TM step. -/
def stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [noMoveTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

/-- The top word of `noMoveTile tm q a qNew w` is `[↟ₛq, ↟ₜa]`. -/
@[simp]
lemma noMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
  (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (noMoveTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

/-- The bottom word of `noMoveTile tm q a qNew w` is `[stateMarker tm qNew, ↟ₜw]`. -/
@[simp]
lemma noMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
  (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (noMoveTile tm q a qNew w).bot = [stateMarker tm qNew, ↟ₜw] := rfl

/-- `τ1` of `stepTilesNoMove` reproduces the current configuration block. -/
lemma τ1_stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ1 (stepTilesNoMove tm q qNew t w) = encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesNoMove, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, noMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  simp [List.append_assoc]

/-- `τ2` of `stepTilesNoMove` produces the next configuration block. -/
lemma τ2_stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ2 (stepTilesNoMove tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [stateMarker tm qNew] ++
      liftTape tm (w :: t.right.toList) ++
      [#] := by
  simp only [stepTilesNoMove, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, noMoveTile_bot, sepTile_bot,
             List.append_nil, liftTape_cons]
  simp [List.append_assoc]

/-- Every tile in `stepTilesNoMove` belongs to `haltTiles tm`. -/
lemma stepTilesNoMove_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, none⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (htile : tile ∈ stepTilesNoMove tm q qNew t w) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesNoMove, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · refine transitionTile_mem_haltTiles tm q a _ ?_
    simp only [transitionTilesFor]; rw [htr]; subst hhead
    exact List.mem_cons_self
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

/-- Tile sequence simulating a single right-move TM step in the interior. -/
def stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [rightMoveTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

/-- The top word of `rightMoveTile tm q a qNew w` is `[↟ₛq, ↟ₜa]`. -/
@[simp]
lemma rightMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
  (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (rightMoveTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

/-- The bottom word of `rightMoveTile tm q a qNew w` is `[↟ₜw, stateMarker tm qNew]`. -/
@[simp]
lemma rightMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
  (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (rightMoveTile tm q a qNew w).bot = [↟ₜw, stateMarker tm qNew] := rfl

/-- `τ1` of `stepTilesRightInterior` reproduces the current configuration block. -/
lemma τ1_stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ1 (stepTilesRightInterior tm q qNew t w) = encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesRightInterior, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, rightMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  simp [List.append_assoc]

/-- `τ2` of `stepTilesRightInterior` in explicit list form. -/
lemma τ2_stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ2 (stepTilesRightInterior tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesRightInterior, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, rightMoveTile_bot, sepTile_bot, List.append_nil]

/-- Every tile in `stepTilesRightInterior` belongs to `haltTiles tm`. -/
lemma stepTilesRightInterior_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Turing.Dir.right⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesRightInterior tm q qNew t w) [Encodable Symbol] [Encodable tm.State]:
    tile ∈ haltTiles tm := by
  simp only [stepTilesRightInterior, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · refine transitionTile_mem_haltTiles tm q a _ ?_
    simp only [transitionTilesFor]; rw [htr]; subst hhead
    exact List.mem_cons_self
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

omit [Inhabited Symbol] [Fintype Symbol] in
/-- In the non-degenerate case, `StackTape.cons` does not strip blanks. -/
lemma cons_toList_of_nondeg (w : Option Symbol) (xs : StackTape Symbol)
    (h : w ≠ none ∨ xs.toList ≠ []) :
    (StackTape.cons w xs).toList = w :: xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with
  | nil => cases w with
    | none => rcases h with h | h <;> exact absurd rfl h
    | some s => rfl
  | cons hd tl' => cases w with | none => rfl | some _ => rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- For a non-empty `StackTape`, `head :: tail.toList = toList`. -/
lemma head_cons_tail_toList (xs : StackTape Symbol) (h : xs.toList ≠ []) :
    xs.head :: xs.tail.toList = xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with | nil => exact absurd rfl h | cons a rest => rfl

/-- Lifted form of `head_cons_tail_toList`. -/
lemma liftTape_head_cons_tail_toList (tm : SingleTapeTM Symbol)
    (xs : StackTape Symbol) (h : xs.toList ≠ []) :
    ↟ₜxs.head :: liftTape tm xs.tail.toList = liftTape tm xs.toList := by
  rw [show (↟ₜxs.head : Alpha tm.State Symbol) :: liftTape tm xs.tail.toList
       = liftTape tm (xs.head :: xs.tail.toList) from rfl,
      head_cons_tail_toList _ h]

/-- The encoding of the configuration after a non-degenerate interior right-move step. -/
lemma encodeCfg_after_right_move_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_ne : t.right.toList ≠ []) :
    encodeCfg tm ⟨qNew, (t.write w).moveRight⟩ =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew] ++
      liftTape tm t.right.toList := by
  have h_left : ((t.write w).moveRight).left.toList = w :: t.left.toList :=
    cons_toList_of_nondeg w t.left h_nondeg
  have h_head : ((t.write w).moveRight).head = t.right.head := rfl
  have h_right : ((t.write w).moveRight).right.toList = t.right.tail.toList := rfl
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_none]
    rw [liftTape_head_cons_tail_toList _ _ h_right_ne]; simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_some]
    rw [liftTape_head_cons_tail_toList _ _ h_right_ne]; simp [List.append_assoc]

/-- In the non-degenerate interior right-move case, `τ2 = encodeCfg(post-step) ++ [#]`. -/
lemma τ2_stepTilesRightInterior_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ []) (h_right_ne : t.right.toList ≠ []) :
    τ2 (stepTilesRightInterior tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).moveRight⟩ ++ [#] := by
  rw [τ2_stepTilesRightInterior,
      encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The `head` of a `StackTape` whose `toList` is empty is `none`. -/
lemma head_of_toList_eq_nil (xs : StackTape Symbol) (h : xs.toList = []) :
    xs.head = none := by
  obtain ⟨tl, hLast⟩ := xs; simp only at h; subst h; rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The `tail` of an empty `StackTape` is also empty. -/
lemma tail_toList_of_toList_eq_nil (xs : StackTape Symbol) (h : xs.toList = []) :
    xs.tail.toList = [] := by
  obtain ⟨tl, hLast⟩ := xs; simp only at h; subst h; rfl

/-- Tile sequence simulating a right-move step at the right boundary. -/
def stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [rightMoveBoundaryTile tm q t.head qNew w]

/-- The top word of `rightMoveBoundaryTile tm q a qNew w` is `[↟ₛq, ↟ₜa, #]`. -/
@[simp]
lemma rightMoveBoundaryTile_top (tm : SingleTapeTM Symbol)
  (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (rightMoveBoundaryTile tm q a qNew w).top = [↟ₛq, ↟ₜa, #] := rfl

/-- The bottom word of `rightMoveBoundaryTile tm q a qNew w` is
  `[↟ₜw, stateMarker tm qNew, ↟ₜnone, #]`. -/
@[simp]
lemma rightMoveBoundaryTile_bot (tm : SingleTapeTM Symbol)
  (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (rightMoveBoundaryTile tm q a qNew w).bot =
    [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #] := rfl

/-- `τ1` of `stepTilesRightBoundary` reproduces the current configuration block. -/
lemma τ1_stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_right_empty : t.right.toList = []) :
    τ1 (stepTilesRightBoundary tm q qNew t w) = encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesRightBoundary, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, rightMoveBoundaryTile_top,
             List.append_nil, encodeRunningCfg, h_right_empty,
             liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- `τ2` of `stepTilesRightBoundary` in explicit list form. -/
lemma τ2_stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ2 (stepTilesRightBoundary tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #] := by
  simp only [stepTilesRightBoundary, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, rightMoveBoundaryTile_bot, List.append_nil]

/-- Every tile in `stepTilesRightBoundary` belongs to `haltTiles tm`. -/
lemma stepTilesRightBoundary_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Turing.Dir.right⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesRightBoundary tm q qNew t w) [Encodable Symbol] [Encodable tm.State] :
    tile ∈ haltTiles tm := by
  simp only [stepTilesRightBoundary, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with hl | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · refine transitionTile_mem_haltTiles tm q a _ ?_
    simp only [transitionTilesFor]; rw [htr]; subst hhead
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The encoding of the configuration after a non-degenerate right-boundary move. -/
lemma encodeCfg_after_right_move_boundary_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_empty : t.right.toList = []) :
    encodeCfg tm ⟨qNew, (t.write w).moveRight⟩ =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol)] := by
  have h_left : ((t.write w).moveRight).left.toList = w :: t.left.toList :=
    cons_toList_of_nondeg w t.left h_nondeg
  have h_head : ((t.write w).moveRight).head = none :=
    head_of_toList_eq_nil _ h_right_empty
  have h_right : ((t.write w).moveRight).right.toList = [] :=
    tail_toList_of_toList_eq_nil _ h_right_empty
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_none]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_some]
    simp [List.append_assoc]

/-- In the non-degenerate right-boundary case, `τ2 = encodeCfg(post-step) ++ [#]`. -/
lemma τ2_stepTilesRightBoundary_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ []) (h_right_empty : t.right.toList = []) :
    τ2 (stepTilesRightBoundary tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).moveRight⟩ ++ [#] := by
  rw [τ2_stepTilesRightBoundary,
      encodeCfg_after_right_move_boundary_eq tm qNew t w h_nondeg h_right_empty]
  simp [List.append_assoc]

/-- `leftMoveTile` for symbol `b` belongs to `transitionTilesFor q a` for left moves. -/
lemma leftMoveTile_mem_transitionTilesFor (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (w : Option Symbol)
    (qNew : Option tm.State) (b : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Turing.Dir.left⟩, qNew)) [Encodable Symbol] [Encodable tm.State]:
    leftMoveTile tm q a qNew w b ∈ transitionTilesFor tm q a := by
  simp only [transitionTilesFor]; rw [htr]
  simp


/-- Tile sequence simulating a left-move step in the interior. -/
def stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.tail.toList.reverse.map (copyTile tm)) ++
  [leftMoveTile tm q t.head qNew w t.left.head] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

/-- The top word of `leftMoveTile tm q a qNew w b` is `[↟ₜb, ↟ₛq, ↟ₜa]`. -/
@[simp]
lemma leftMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
  (a : Option Symbol) (qNew : Option tm.State) (w b : Option Symbol) :
  (leftMoveTile tm q a qNew w b).top = [↟ₜb, ↟ₛq, ↟ₜa] := rfl

/-- The bottom word of `leftMoveTile tm q a qNew w b` is `[stateMarker tm qNew, ↟ₜb, ↟ₜw]`. -/
@[simp]
lemma leftMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
  (a : Option Symbol) (qNew : Option tm.State) (w b : Option Symbol) :
  (leftMoveTile tm q a qNew w b).bot = [stateMarker tm qNew, ↟ₜb, ↟ₜw] := rfl

/-- `τ1` of `stepTilesLeftInterior` reproduces the current configuration block. -/
lemma τ1_stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_left_ne : t.left.toList ≠ []) :
    τ1 (stepTilesLeftInterior tm q qNew t w) = encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesLeftInterior, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, leftMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  have h_split : t.left.toList.reverse = t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]
    simp [List.reverse_cons]
  rw [h_split, liftTape_append, liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- `τ2` of `stepTilesLeftInterior` in explicit list form. -/
lemma τ2_stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ2 (stepTilesLeftInterior tm q qNew t w) =
      liftTape tm t.left.tail.toList.reverse ++
      [stateMarker tm qNew, ↟ₜt.left.head, ↟ₜw] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesLeftInterior, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, leftMoveTile_bot, sepTile_bot, List.append_nil]

/-- Every tile in `stepTilesLeftInterior` belongs to `haltTiles tm`. -/
lemma stepTilesLeftInterior_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Turing.Dir.left⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesLeftInterior tm q qNew t w)  [Encodable Symbol] [Encodable tm.State]:
    tile ∈ haltTiles tm := by
  simp only [stepTilesLeftInterior, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · refine transitionTile_mem_haltTiles tm q a _ ?_
    subst hhead
    exact leftMoveTile_mem_transitionTilesFor tm q t.head w qNew t.left.head htr
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

/-- The encoding of the configuration after a non-degenerate interior left-move step. -/
lemma encodeCfg_after_left_move_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) :
    encodeCfg tm ⟨qNew, (t.write w).moveLeft⟩ =
      liftTape tm t.left.tail.toList.reverse ++
      [stateMarker tm qNew, ↟ₜt.left.head, ↟ₜw] ++
      liftTape tm t.right.toList := by
  have h_left :
      ((t.write w).moveLeft).left.toList = t.left.tail.toList := rfl
  have h_head : ((t.write w).moveLeft).head = t.left.head := rfl
  have h_right :
      ((t.write w).moveLeft).right.toList = w :: t.right.toList := by
    show (StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.right h_nondeg
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               liftTape_cons, stateMarker_none]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               liftTape_cons, stateMarker_some]
    simp [List.append_assoc]

/-- In the non-degenerate interior left-move case, `τ2 = encodeCfg(post-step) ++ [#]`. -/
lemma τ2_stepTilesLeftInterior_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) :
    τ2 (stepTilesLeftInterior tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).moveLeft⟩ ++ [#] := by
  rw [τ2_stepTilesLeftInterior,
      encodeCfg_after_left_move_eq tm qNew t w h_nondeg]

/-- Tile sequence simulating a left-move step at the left boundary. -/
def stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  [leftMoveBoundaryTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

/-- The top word of `leftMoveBoundaryTile tm q a qNew w` is `[↟ₛq, ↟ₜa]`. -/
@[simp]
lemma leftMoveBoundaryTile_top (tm : SingleTapeTM Symbol)
  (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (leftMoveBoundaryTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

/-- The bottom word of `leftMoveBoundaryTile tm q a qNew w` is
  `[stateMarker tm qNew, ↟ₜnone, ↟ₜw]`. -/
@[simp]
lemma leftMoveBoundaryTile_bot (tm : SingleTapeTM Symbol)
  (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
  (leftMoveBoundaryTile tm q a qNew w).bot =
    [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] := rfl

/-- `τ1` of `stepTilesLeftBoundary` reproduces the current configuration block. -/
lemma τ1_stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_left_empty : t.left.toList = []) :
    τ1 (stepTilesLeftBoundary tm q qNew t w) = encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesLeftBoundary, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, leftMoveBoundaryTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, h_left_empty,
             liftTape_cons, liftTape_nil, List.reverse_nil]
  simp

/-- `τ2` of `stepTilesLeftBoundary` in explicit list form. -/
lemma τ2_stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    τ2 (stepTilesLeftBoundary tm q qNew t w) =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesLeftBoundary, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, leftMoveBoundaryTile_bot, sepTile_bot, List.append_nil]

/-- The encoding of the configuration after a non-degenerate left-boundary move. -/
lemma encodeCfg_after_left_move_boundary_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (h_left_empty : t.left.toList = []) :
    encodeCfg tm ⟨qNew, (t.write w).moveLeft⟩ =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] ++
      liftTape tm t.right.toList := by
  have h_left : ((t.write w).moveLeft).left.toList = [] :=
    tail_toList_of_toList_eq_nil _ h_left_empty
  have h_head : ((t.write w).moveLeft).head = none :=
    head_of_toList_eq_nil _ h_left_empty
  have h_right : ((t.write w).moveLeft).right.toList = w :: t.right.toList :=
    cons_toList_of_nondeg w t.right h_nondeg
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_nil, liftTape_cons, liftTape_nil,
               stateMarker_none, List.nil_append, List.cons_append]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_nil, liftTape_cons, liftTape_nil,
               stateMarker_some, List.nil_append, List.cons_append]

/-- In the non-degenerate left-boundary case, `τ2 = encodeCfg(post-step) ++ [#]`. -/
lemma τ2_stepTilesLeftBoundary_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) (h_left_empty : t.left.toList = []) :
    τ2 (stepTilesLeftBoundary tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).moveLeft⟩ ++ [#] := by
  rw [τ2_stepTilesLeftBoundary,
      encodeCfg_after_left_move_boundary_eq tm qNew t w h_nondeg h_left_empty]

/-- The list-parameterised halted encoding: `liftTape left.reverse ++ [h⊥] ++ liftTape right`. -/
def encodeHaltList (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol)) : List (Alpha tm.State Symbol) :=
  liftTape tm left.reverse ++ [h⊥] ++ liftTape tm right

/-- `encodeHaltedCfg tm t` equals `encodeHaltList tm t.left.toList (t.head :: t.right.toList)`. -/
lemma encodeHaltedCfg_eq_encodeHaltList (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    encodeHaltedCfg tm t =
      encodeHaltList tm t.left.toList (t.head :: t.right.toList) := by
  simp [encodeHaltedCfg, encodeHaltList, List.append_assoc]

/-- The top word of `absorbLeftTile tm a` is `[↟ₜa, h⊥]`. -/
@[simp]
lemma absorbLeftTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
  (absorbLeftTile tm a).top = [↟ₜa, h⊥] := rfl

/-- The bottom word of `absorbLeftTile tm a` is `[h⊥]`. -/
@[simp]
lemma absorbLeftTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
  (absorbLeftTile tm a).bot = [h⊥] := rfl

/-- The top word of `absorbRightTile tm a` is `[h⊥, ↟ₜa]`. -/
@[simp]
lemma absorbRightTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
  (absorbRightTile tm a).top = [h⊥, ↟ₜa] := rfl

/-- The bottom word of `absorbRightTile tm a` is `[h⊥]`. -/
@[simp]
lemma absorbRightTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
  (absorbRightTile tm a).bot = [h⊥] := rfl

/-- Tile sequence for one absorb-left iteration: removes the innermost left symbol `l` from
  `encodeHaltList (l :: rest) right`. -/
def stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    List (Tile (Alpha tm.State Symbol)) :=
  rest.reverse.map (copyTile tm) ++
  [absorbLeftTile tm l] ++
  right.map (copyTile tm) ++
  [sepTile tm]

/-- Tile sequence for one absorb-right iteration: removes the leftmost right symbol `r` from
  `encodeHaltList left (r :: rest)`. -/
def stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol) (rest : List (Option Symbol)) :
    List (Tile (Alpha tm.State Symbol)) :=
  left.reverse.map (copyTile tm) ++
  [absorbRightTile tm r] ++
  rest.map (copyTile tm) ++
  [sepTile tm]

/-- `τ1` of `stepTilesAbsorbLeft` reproduces `encodeHaltList (l :: rest) right ++ [#]`. -/
lemma τ1_stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    τ1 (stepTilesAbsorbLeft tm l rest right) =
      encodeHaltList tm (l :: rest) right ++ [#] := by
  simp only [stepTilesAbsorbLeft, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, absorbLeftTile_top, sepTile_top,
             List.append_nil, encodeHaltList,
             List.reverse_cons, liftTape_append, liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- `τ2` of `stepTilesAbsorbLeft` produces `encodeHaltList rest right ++ [#]`. -/
lemma τ2_stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    τ2 (stepTilesAbsorbLeft tm l rest right) =
      encodeHaltList tm rest right ++ [#] := by
  simp only [stepTilesAbsorbLeft, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, absorbLeftTile_bot, sepTile_bot,
             List.append_nil, encodeHaltList]

/-- `τ1` of `stepTilesAbsorbRight` reproduces `encodeHaltList left (r :: rest) ++ [#]`. -/
lemma τ1_stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol) (rest : List (Option Symbol)) :
    τ1 (stepTilesAbsorbRight tm left r rest) =
      encodeHaltList tm left (r :: rest) ++ [#] := by
  simp only [stepTilesAbsorbRight, τ1_append, τ1_cons, τ1_nil,
             τ1_map_copyTile, absorbRightTile_top, sepTile_top,
             List.append_nil, encodeHaltList, liftTape_cons]
  simp [List.append_assoc]

/-- `τ2` of `stepTilesAbsorbRight` produces `encodeHaltList left rest ++ [#]`. -/
lemma τ2_stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol) (rest : List (Option Symbol)) :
    τ2 (stepTilesAbsorbRight tm left r rest) =
      encodeHaltList tm left rest ++ [#] := by
  simp only [stepTilesAbsorbRight, τ2_append, τ2_cons, τ2_nil,
             τ2_map_copyTile, absorbRightTile_bot, sepTile_bot,
             List.append_nil, encodeHaltList]

/-- Every tile in `stepTilesAbsorbLeft` belongs to `haltTiles tm`. -/
lemma stepTilesAbsorbLeft_subset_haltTiles (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAbsorbLeft tm l rest right) [Encodable Symbol] [Encodable tm.State]:
    tile ∈ haltTiles tm := by
  simp only [stepTilesAbsorbLeft, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · exact absorbLeftTile_mem_haltTiles tm l
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

/-- Every tile in `stepTilesAbsorbRight` belongs to `haltTiles tm`. -/
lemma stepTilesAbsorbRight_subset_haltTiles (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol) (rest : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAbsorbRight tm left r rest) [Encodable Symbol] [Encodable tm.State] :
    tile ∈ haltTiles tm := by
  simp only [stepTilesAbsorbRight, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · exact absorbRightTile_mem_haltTiles tm r
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

/-- The tile sequence that absorbs all remaining tape symbols around `h⊥` and closes the match with
  `finalTile`. -/
def absorbAndFinish (tm : SingleTapeTM Symbol) :
    List (Option Symbol) → List (Option Symbol) → Stack (Alpha tm.State Symbol)
  | [],        []        => [finalTile tm]
  | [],        r :: rest => stepTilesAbsorbRight tm [] r rest ++
                              absorbAndFinish tm [] rest
  | l :: rest, right    => stepTilesAbsorbLeft tm l rest right ++
                              absorbAndFinish tm rest right

/-- The matching invariant for `absorbAndFinish`: `τ1 = encodeHaltList left right ++ [#] ++ τ2`. -/
lemma absorbAndFinish_matching (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol)) :
    τ1 (absorbAndFinish tm left right) =
      encodeHaltList tm left right ++ [#] ++
        τ2 (absorbAndFinish tm left right) := by
  induction left, right using absorbAndFinish.induct with
  | case1 => simp [absorbAndFinish, finalTile, encodeHaltList, liftTape]
  | case2 r rest ih =>
    simp only [absorbAndFinish, τ1_append, τ2_append,
               τ1_stepTilesAbsorbRight, τ2_stepTilesAbsorbRight, ih,
               List.append_assoc]
  | case3 l rest right ih =>
    simp only [absorbAndFinish, τ1_append, τ2_append,
               τ1_stepTilesAbsorbLeft, τ2_stepTilesAbsorbLeft, ih,
               List.append_assoc]

/-- Every tile in `absorbAndFinish` belongs to `haltTiles tm`. -/
lemma absorbAndFinish_subset_haltTiles (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ absorbAndFinish tm left right) [Encodable Symbol] [Encodable tm.State]:
    tile ∈ haltTiles tm := by
  induction left, right using absorbAndFinish.induct with
  | case1 =>
    simp only [absorbAndFinish, List.mem_singleton] at htile
    rw [htile]; exact finalTile_mem_haltTiles tm
  | case2 r rest ih =>
    simp only [absorbAndFinish, List.mem_append] at htile
    rcases htile with hL | hR
    · exact stepTilesAbsorbRight_subset_haltTiles tm [] r rest tile hL
    · exact ih hR
  | case3 l rest right ih =>
    simp only [absorbAndFinish, List.mem_append] at htile
    rcases htile with hL | hR
    · exact stepTilesAbsorbLeft_subset_haltTiles tm l rest right tile hL
    · exact ih hR

/-- `tm` is blank-write free: the transition function never writes the blank symbol. -/
def NoBlankWrites (tm : SingleTapeTM Symbol) : Prop :=
  ∀ q : tm.State, ∀ a : Option Symbol, ((tm.tr q a).1).symbol ≠ none

/-- `tm` satisfies the no-left-boundary condition on input `w`: no reachable configuration invokes a
  left-move at the left tape boundary. -/
def NoLeftBoundary (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∀ (cfg : tm.Cfg), Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) cfg →
    ∀ (q : tm.State) (t : BiTape Symbol),
      cfg = ⟨some q, t⟩ → t.left.toList = [] →
      (tm.tr q t.head).1.movement ≠ some Turing.Dir.left

/-- The configuration reached by a single TM step from `⟨some q, t⟩`. -/
def stepResult (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    tm.Cfg :=
  ⟨(tm.tr q t.head).2,
    (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement⟩

/-- A running configuration steps to `stepResult`. -/
@[simp]
lemma tm_step_running (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    some (stepResult tm q t) = tm.step ⟨some q, t⟩ := by
  simp only [SingleTapeTM.step, stepResult]

/-- Dispatch the simulation tile sequence for one TM step. -/
def stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol)
    (w : Option Symbol) (mov : Option Turing.Dir) (qNew : Option tm.State) :
    Stack (Alpha tm.State Symbol) :=
  match mov with
  | none                    => stepTilesNoMove tm q qNew t w
  | some Turing.Dir.right   =>
      match t.right.toList with
      | []     => stepTilesRightBoundary tm q qNew t w
      | _ :: _ => stepTilesRightInterior tm q qNew t w
  | some Turing.Dir.left    =>
      match t.left.toList with
      | []     => stepTilesLeftBoundary tm q qNew t w
      | _ :: _ => stepTilesLeftInterior tm q qNew t w

/-- The simulation tile sequence for one running TM step. -/
def stepTiles (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    Stack (Alpha tm.State Symbol) :=
  stepTilesAux tm q t (tm.tr q t.head).1.symbol
    (tm.tr q t.head).1.movement (tm.tr q t.head).2

/-- `τ1` of `stepTilesAux` reproduces the current configuration block. -/
lemma τ1_stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) (w : Option Symbol) (mov : Option Turing.Dir)
    (qNew : Option tm.State) :
    τ1 (stepTilesAux tm q t w mov qNew) = encodeRunningCfg tm q t ++ [#] := by
  unfold stepTilesAux
  cases mov with
  | none => exact τ1_stepTilesNoMove tm q qNew t w
  | some dir => cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil => exact τ1_stepTilesRightBoundary tm q qNew t w h_right
      | cons _ _ => exact τ1_stepTilesRightInterior tm q qNew t w
    | left =>
      cases h_left : t.left.toList with
      | nil => exact τ1_stepTilesLeftBoundary tm q qNew t w h_left
      | cons _ _ =>
        refine τ1_stepTilesLeftInterior tm q qNew t w ?_
        rw [h_left]; exact List.cons_ne_nil _ _

/-- Every tile in `stepTilesAux` belongs to `haltTiles tm`, given no left-boundary. -/
lemma stepTilesAux_subset_haltTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (t : BiTape Symbol) (w : Option Symbol)
    (mov : Option Turing.Dir) (qNew : Option tm.State)
    (htr : tm.tr q a = (⟨w, mov⟩, qNew)) (hhead : t.head = a)
    (h_no_lb : mov = some Turing.Dir.left → t.left.toList ≠ [])
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAux tm q t w mov qNew) [Encodable Symbol] [Encodable tm.State]:
    tile ∈ haltTiles tm := by
  unfold stepTilesAux at htile
  cases mov with
  | none => exact stepTilesNoMove_subset_haltTiles tm q a qNew t w htr hhead tile htile
  | some dir => cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil =>
        rw [h_right] at htile
        exact stepTilesRightBoundary_subset_haltTiles tm q a qNew t w htr hhead tile htile
      | cons _ _ =>
        rw [h_right] at htile
        exact stepTilesRightInterior_subset_haltTiles tm q a qNew t w htr hhead tile htile
    | left =>
      cases h_left : t.left.toList with
      | nil => exact absurd h_left (h_no_lb rfl)
      | cons _ _ =>
        rw [h_left] at htile
        exact stepTilesLeftInterior_subset_haltTiles tm q a qNew t w htr hhead tile htile

/-- `τ2` of `stepTilesAux` equals `encodeCfg(post-step) ++ [#]`, given `w ≠ none`. -/
lemma τ2_stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) (w : Option Symbol) (mov : Option Turing.Dir)
    (qNew : Option tm.State) (h_w_ne : w ≠ none) :
    τ2 (stepTilesAux tm q t w mov qNew) =
      encodeCfg tm ⟨qNew, (t.write w).optionMove mov⟩ ++ [#] := by
  unfold stepTilesAux
  cases mov with
  | none =>
    rw [τ2_stepTilesNoMove]
    show _ = encodeCfg tm ⟨qNew, t.write w⟩ ++ [#]
    cases qNew with
    | none =>
      simp only [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
                 stateMarker_none, liftTape_cons, List.append_assoc,
                 List.cons_append, List.nil_append]
    | some q' =>
      simp only [encodeCfg_running, encodeRunningCfg, BiTape.write,
                 stateMarker_some, liftTape_cons, List.append_assoc,
                 List.cons_append, List.nil_append]
  | some dir => cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil => exact τ2_stepTilesRightBoundary_eq_encodeCfg tm q qNew t w (Or.inl h_w_ne) h_right
      | cons _ _ =>
        refine τ2_stepTilesRightInterior_eq_encodeCfg tm q qNew t w (Or.inl h_w_ne) ?_
        rw [h_right]; exact List.cons_ne_nil _ _
    | left =>
      cases h_left : t.left.toList with
      | nil => exact τ2_stepTilesLeftBoundary_eq_encodeCfg tm q qNew t w (Or.inl h_w_ne) h_left
      | cons _ _ => exact τ2_stepTilesLeftInterior_eq_encodeCfg tm q qNew t w (Or.inl h_w_ne)

/-- `τ1` of `stepTiles` reproduces the current configuration block. -/
lemma τ1_stepTiles (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    τ1 (stepTiles tm q t) = encodeRunningCfg tm q t ++ [#] := by
  unfold stepTiles; exact τ1_stepTilesAux tm q t _ _ _

/-- Every tile in `stepTiles` belongs to `haltTiles tm`, given no left-boundary. -/
lemma stepTiles_subset_haltTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol)
    (h_no_lb : (tm.tr q t.head).1.movement = some Turing.Dir.left → t.left.toList ≠ [])
    (tile : Tile (Alpha tm.State Symbol))  [Encodable Symbol] [Encodable tm.State] (htile : tile ∈ stepTiles tm q t) :
    tile ∈ haltTiles tm := by
  unfold stepTiles at htile
  have htr : tm.tr q t.head =
      (⟨(tm.tr q t.head).1.symbol, (tm.tr q t.head).1.movement⟩, (tm.tr q t.head).2) := by
    rcases tm.tr q t.head with ⟨⟨_, _⟩, _⟩; rfl
  exact stepTilesAux_subset_haltTiles tm q t.head t _ _ _ htr rfl h_no_lb tile htile

/-- `τ2` of `stepTiles` equals `encodeCfg(post-step) ++ [#]`, given `NoBlankWrites`. -/
lemma τ2_stepTiles (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (q : tm.State) (t : BiTape Symbol) :
    τ2 (stepTiles tm q t) = encodeCfg tm (stepResult tm q t) ++ [#] := by
  unfold stepTiles stepResult
  exact τ2_stepTilesAux tm q t _ _ _ (h_nbw q t.head)

/-- Constructs a tile stack from a halting trace. -/
lemma forward_aux (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (w : List Symbol) (h_nlb : NoLeftBoundary tm w) (target_tape : BiTape Symbol) [Encodable Symbol] [Encodable tm.State]:
    ∀ (cfg : tm.Cfg) (n : ℕ),
      Relation.ReflTransGen tm.TransitionRelation (SingleTapeTM.initCfg tm w) cfg →
      Relation.RelatesInSteps tm.TransitionRelation cfg ⟨none, target_tape⟩ n →
      ∃ A : Stack (Alpha tm.State Symbol),
        (∀ tile ∈ A, tile ∈ haltTiles tm) ∧
        τ1 A = encodeCfg tm cfg ++ [#] ++ τ2 A := by
  intro cfg n h_reach h_chain
  induction n generalizing cfg with
  | zero =>
    have hzero : cfg = ⟨none, target_tape⟩ := h_chain.zero; subst hzero
    refine ⟨absorbAndFinish tm target_tape.left.toList
              (target_tape.head :: target_tape.right.toList), ?_, ?_⟩
    · intro tile htile; exact absorbAndFinish_subset_haltTiles tm _ _ tile htile
    · rw [show encodeCfg tm (⟨none, target_tape⟩ : tm.Cfg) =
            encodeHaltedCfg tm target_tape from rfl, encodeHaltedCfg_eq_encodeHaltList]
      exact absorbAndFinish_matching tm _ _
  | succ n ih =>
    obtain ⟨cfg', h_step, h_rest⟩ := h_chain.succ'
    cases hcfg : cfg with
    | mk state tape => cases state with
      | none =>
        rw [hcfg] at h_step
        unfold SingleTapeTM.TransitionRelation at h_step
        simp [SingleTapeTM.step] at h_step
      | some q =>
        rw [hcfg] at h_step
        unfold SingleTapeTM.TransitionRelation at h_step
        rw [← tm_step_running] at h_step
        have h_cfg' : cfg' = stepResult tm q tape := (Option.some.inj h_step).symm; subst h_cfg'
        have h_no_lb : (tm.tr q tape.head).1.movement = some Turing.Dir.left →
            tape.left.toList ≠ [] := by
          intro h_mov h_empty
          have := h_nlb cfg (by simpa [hcfg] using h_reach) q tape hcfg h_empty
          exact this h_mov
        have h_reach' : Relation.ReflTransGen tm.TransitionRelation
            (SingleTapeTM.initCfg tm w) (stepResult tm q tape) := by
          refine h_reach.tail ?_
          show tm.step cfg = some (stepResult tm q tape)
          rw [hcfg]; exact tm_step_running tm q tape
        obtain ⟨A', hA'_mem, hA'_match⟩ := ih (stepResult tm q tape) h_reach' h_rest
        refine ⟨stepTiles tm q tape ++ A', ?_, ?_⟩
        · intro tile htile
          rw [List.mem_append] at htile
          rcases htile with hL | hR
          · exact stepTiles_subset_haltTiles tm q tape h_no_lb tile hL
          · exact hA'_mem tile hR
        · rw [τ1_append, τ2_append, τ1_stepTiles, τ2_stepTiles tm h_nbw, hA'_match]
          rw [encodeCfg_running]

/-- If `tm` halts on `w`, then the reduced MPCP instance has a solution. -/
theorem mHasSolution_if_halt (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w) (h : Halts tm w) [Encodable Symbol] [Encodable tm.State]:
    MPCP.DecisionProblem (startTile tm w) (haltTiles tm) := by
  obtain ⟨target_tape, h_chain⟩ := h
  obtain ⟨n, h_chain_n⟩ := h_chain.relatesInSteps
  obtain ⟨A, hA_mem, hA_match⟩ :=
    forward_aux tm h_nbw w h_nlb target_tape
      (SingleTapeTM.initCfg tm w) n Relation.ReflTransGen.refl h_chain_n
  refine ⟨A, ?_, ?_⟩
  · intro tile htile; exact List.mem_cons_of_mem _ (hA_mem tile htile)
  · show (startTile tm w).top ++ τ1 A = (startTile tm w).bot ++ τ2 A
    rw [startTile_top, startTile_bot, hA_match]
    show [#] ++ (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ τ2 A) =
         (# :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#]) ++ τ2 A
    simp [List.append_assoc]

/-- Every tile in `haltTiles tm` is one of: copy, separator, no-move transition, right-move
  transition (interior or boundary), left-move transition, left or right absorb tile, or the final
  tile. Also exposes the TM-transition equation for each transition tile. -/
private lemma mem_haltTiles_top (tm : SingleTapeTM Symbol)
    (t : Tile (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State] (ht : t ∈ haltTiles tm) :
    (∃ a : Option Symbol, t = copyTile tm a) ∨
    t = sepTile tm ∨
    (∃ (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol),
        tm.tr q a = (⟨w, none⟩, qNew) ∧ t = noMoveTile tm q a qNew w) ∨
    (∃ (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol),
        tm.tr q a = (⟨w, some Turing.Dir.right⟩, qNew) ∧
          (t = rightMoveTile tm q a qNew w ∨ t = rightMoveBoundaryTile tm q a qNew w)) ∨
    (∃ (q : tm.State) (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol),
        tm.tr q a = (⟨w, some Turing.Dir.left⟩, qNew) ∧
          ∃ b : Option Symbol, t = leftMoveTile tm q a qNew w b) ∨
    (∃ a : Option Symbol, t = absorbLeftTile tm a) ∨
    (∃ a : Option Symbol, t = absorbRightTile tm a) ∨
    t = finalTile tm := by
  simp only [haltTiles, List.mem_append, List.mem_singleton] at ht
  rcases ht with ((((ht | rfl) | ht) | ht) | rfl)
  · simp only [copyTiles, List.mem_map] at ht
    obtain ⟨a, _, rfl⟩ := ht; exact Or.inl ⟨a, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · simp only [transitionTiles, List.mem_flatMap] at ht
    obtain ⟨⟨q, a⟩, _, ht⟩ := ht
    rcases h_tr : tm.tr q a with ⟨⟨w, dir⟩, qNew⟩
    cases dir with
    | none =>
      simp only [transitionTilesFor] at ht; rw [h_tr] at ht
      simp only [List.mem_singleton] at ht; subst ht
      exact Or.inr (Or.inr (Or.inl ⟨q, a, qNew, w, h_tr, rfl⟩))
    | some d => cases d with
      | right =>
        simp only [transitionTilesFor] at ht; rw [h_tr] at ht
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, a, qNew, w, h_tr, Or.inl rfl⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, a, qNew, w, h_tr, Or.inr rfl⟩)))
      | left =>
        simp only [transitionTilesFor] at ht; rw [h_tr] at ht
        simp only [List.mem_map] at ht; obtain ⟨b, _, rfl⟩ := ht
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, a, qNew, w, h_tr, b, rfl⟩))))
  · simp only [absorbTiles, List.mem_flatMap, absorbTilesFor,
               List.mem_cons, List.mem_nil_iff, or_false] at ht
    obtain ⟨a, _, (rfl | rfl)⟩ := ht
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-- The `liftTape tm L` prefix of `τ1 A` forces `A` to begin with copy tiles for `L`, provided the
  following character is not `h⊥` and not `↟ₛq`. -/
private lemma copy_prefix_forced (tm : SingleTapeTM Symbol) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
      (tail : List (Alpha tm.State Symbol)),
      (∀ t ∈ A, t ∈ haltTiles tm) →
      τ1 A = liftTape tm L ++ tail →
      (∀ x : List (Alpha tm.State Symbol), tail ≠ h⊥ :: x) →
      (∀ (q : tm.State) (x : List (Alpha tm.State Symbol)), tail ≠ ↟ₛq :: x) →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ t ∈ A', t ∈ haltTiles tm) ∧
          τ1 A' = tail ∧
          τ2 A = liftTape tm L ++ τ2 A' := by
  intro L; induction L with
  | nil =>
    intro A tail h_mem h_eq hx hy hz q
    use A
    simp[hy]
    exact hx
  | cons a L ih =>
    intro A tail h_mem h_eq h_not_halt h_not_state hx q
    cases A with
    | nil => simp [τ1, liftTape] at h_not_state
    ---simp[liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_mem : t ∈ haltTiles tm := by
       simp at h_not_halt
       simp[h_not_halt]
      have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm := by
        simp at h_not_halt
        exact h_not_halt.2
      rw [τ1_cons, liftTape_cons, List.cons_append] at h_not_state
      rcases mem_haltTiles_top tm t h_t_mem with
          ⟨a', rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨q', _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_not_state
        injection h_not_state with h_head h_tail; injection h_head with h_a; subst h_a
        obtain ⟨A', hA, hA_mem, hA_τ1, hA_τ2⟩ :=
          ih A_rest h_eq h_rest_mem h_tail hx q
        exact ⟨A', by simp [List.map_cons, hA], hA_mem, hA_τ1,
               by simp [τ2_cons, copyTile_bot, hA_τ2, liftTape_cons]⟩
      · simp at h_not_state
      · simp at h_not_state
      · simp at h_not_state
      · simp at h_not_state
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_not_state
        injection h_not_state with _ h_rest1
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest1
          exact (q q' _ h_rest1.symm).elim
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest1
          injection h_rest1 with h_h; cases h_h
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_not_state
        injection h_not_state with _ h_rest
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest
          exact (hx _ h_rest.symm).elim
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest
          injection h_rest with h_h; cases h_h
      · simp at h_not_state
      · simp at h_not_state

/-- When `τ1 A` begins `liftTape tm L ++ ↟ₛq :: ↟ₜa :: rest` and the transition is not a left-move,
  the copy prefix extends all the way to `↟ₛq`. -/
private lemma copy_prefix_forced_state_lead (tm : SingleTapeTM Symbol) [Encodable Symbol] [Encodable tm.State]
    (q : tm.State) (a : Option Symbol)
    (h_not_left : ∀ (qNew : Option tm.State) (w : Option Symbol) ,
        tm.tr q a ≠ (⟨w, some Turing.Dir.left⟩, qNew)) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (rest : List (Alpha tm.State Symbol)),
      (∀ s ∈ A, s ∈ haltTiles tm) →
      τ1 A = liftTape tm L ++ ↟ₛq :: ↟ₜa :: rest →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ s ∈ A', s ∈ haltTiles tm) ∧
          τ1 A' = ↟ₛq :: ↟ₜa :: rest ∧
          τ2 A = liftTape tm L ++ τ2 A' := by
  intro L; induction L with
  | nil =>
    intro A rest h_mem h_eq
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a' L ih =>
    intro A rest h_mem h_eq
    cases A with
    | nil => simp [liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
      have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [τ1_cons, liftTape_cons, List.cons_append] at h_eq
      rcases mem_haltTiles_top tm t h_t_mem with
          ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨q', a'', _, _, h_tr, b, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_head h_tail; injection h_head with h_a; subst h_a
        obtain ⟨A', hA, hA_mem, hA_τ1, hA_τ2⟩ := ih A_rest rest h_rest_mem h_tail
        exact ⟨A', by simp [List.map_cons, hA], hA_mem, hA_τ1,
               by simp [τ2_cons, copyTile_bot, hA_τ2, liftTape_cons]⟩
      · simp at h_eq
      · simp at h_eq
      · simp at h_eq
      · simp at h_eq
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_rest1
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest1
          injection h_rest1 with h_q_eq h_rest2; injection h_q_eq with h_q_eq'; subst h_q_eq'
          injection h_rest2 with h_a_eq _; injection h_a_eq with h_a_eq'; subst h_a_eq'
          exact (h_not_left _ _ h_tr).elim
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest1
          injection h_rest1 with h_h; cases h_h
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_rest
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest
          injection h_rest with h_h; cases h_h
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest
          injection h_rest with h_h; cases h_h
      · simp at h_eq
      · simp at h_eq

/-- When `τ1 A` begins with `↟ₛq :: ↟ₜa :: rest`, the head tile of `A` is a transition tile for
  `(q, a)`. -/
private lemma transition_forced (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (rest : List (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ t ∈ A, t ∈ haltTiles tm)
    (h_eq : τ1 A = ↟ₛq :: ↟ₜa :: rest) :
    ∃ (tile : Tile (Alpha tm.State Symbol)) (A' : Stack (Alpha tm.State Symbol)),
      A = tile :: A' ∧ tile ∈ transitionTilesFor tm q a ∧ (∀ s ∈ A', s ∈ haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
    have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    refine ⟨t, A_rest, rfl, ?_, h_rest_mem⟩
    rw [τ1_cons] at h_eq
    rcases mem_haltTiles_top tm t h_t_mem with
        ⟨_, rfl⟩ | rfl | ⟨q', a', qNew, w, h_tr, rfl⟩ | ⟨q', a', qNew, w, h_tr, rfl | rfl⟩
      | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
    · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h
    · simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h
    · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h h_rest; injection h_h with h_q'; subst h_q'
      injection h_rest with h_a _; injection h_a with h_a'; subst h_a'
      simp only [transitionTilesFor]; rw [h_tr]; exact List.mem_singleton.mpr rfl
    · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h h_rest; injection h_h with h_q'; subst h_q'
      injection h_rest with h_a _; injection h_a with h_a'; subst h_a'
      simp only [transitionTilesFor]; rw [h_tr]; exact List.mem_cons_self
    · simp only [rightMoveBoundaryTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h h_rest; injection h_h with h_q'; subst h_q'
      injection h_rest with h_a _; injection h_a with h_a'; subst h_a'
      simp only [transitionTilesFor]; rw [h_tr]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h
    · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h
    · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h
    · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h

/-- When `τ1 A` begins with `#`, the head tile of `A` is `sepTile tm`. -/
private lemma sep_forced (tm : SingleTapeTM Symbol)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : τ1 A = # :: rest) :
    ∃ A' : Stack (Alpha tm.State Symbol),
      A = sepTile tm :: A' ∧
      τ1 A' = rest ∧
      (∀ s ∈ A', s ∈ haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
    have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    rw [τ1_cons] at h_eq
    rcases mem_haltTiles_top tm t h_t_mem with
        ⟨_, rfl⟩
      | rfl
      | ⟨_, _, _, _, _, rfl⟩
      | ⟨_, _, _, _, _, rfl | rfl⟩
      | ⟨_, _, _, _, _, _, rfl⟩
      | ⟨_, rfl⟩
      | ⟨_, rfl⟩
      | rfl
    · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with _ h_tail
      exact ⟨A_rest, rfl, h_tail, h_rest_mem⟩
    · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [rightMoveBoundaryTile_top, List.cons_append,
                 List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h

/-- If `τ1 A` begins `↟ₛq :: # :: rest`, no tile of `haltTiles` can be the head of `A`. Used to
  discharge the alternative `rightMoveTile` path in the right-boundary step lemma. -/
private lemma no_tile_for_state_sharp (tm : SingleTapeTM Symbol) (q : tm.State)
    (rest : List (Alpha tm.State Symbol)) (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm) (h_eq : τ1 A = ↟ₛq :: # :: rest) : False := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
    rw [τ1_cons] at h_eq
    rcases mem_haltTiles_top tm t h_t_mem with
        ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
      | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
    all_goals simp at h_eq

/-- Given `A ⊆ haltTiles tm` and the no-move matching invariant, peel the canonical no-move step
  block and advance to the post-step invariant. -/
private lemma starts_with_stepTilesNoMove (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol) (qNew : Option tm.State) (w : Option Symbol) [Encodable Symbol] [Encodable tm.State]
    (htr : tm.tr q t.head = (⟨w, none⟩, qNew))
    (A : Stack (Alpha tm.State Symbol)) (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesNoMove tm q qNew t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        τ1 A' = encodeCfg tm ⟨qNew, t.write w⟩ ++ [#] ++ τ2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Turing.Dir.left⟩, qN) := by
    intro qN w' h; rw [htr] at h; injection h with h1 _; injection h1 with _ h_dir; cases h_dir
  have h_eq' : τ1 A = liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++ τ2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_state_lead tm q t.head h_not_left t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++ τ2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced tm q t.head (liftTape tm t.right.toList ++ [#] ++ τ2 A) A1 hA_mem hA_τ1
  have h_tile_eq : tile = noMoveTile tm q t.head qNew w := by
    simp only [transitionTilesFor] at h_tile_in; rw [htr] at h_tile_in
    exact List.mem_singleton.mp h_tile_in
  subst h_tile_eq
  have hA2_τ1 : τ1 A2 = liftTape tm t.right.toList ++ [#] ++ τ2 A := by
    have key := hA_τ1; rw [hA1_decomp, τ1_cons, noMoveTile_top] at key; simpa using key
  obtain ⟨A3, hA2, hA3_mem, hA3_τ1, hA3_τ2⟩ :=
    copy_prefix_forced tm t.right.toList A2 ([#] ++ τ2 A) hA2_mem
      (by simpa [List.append_assoc] using hA2_τ1)
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  obtain ⟨A4, hA3_decomp, hA4_τ1, hA4_mem⟩ :=
    sep_forced tm (τ2 A) A3 hA3_mem (by simpa using hA3_τ1)
  refine ⟨A4, ?_, hA4_mem, ?_⟩
  · rw [hA, hA1_decomp, hA2, hA3_decomp]
    simp only [stepTilesNoMove, List.append_assoc, List.cons_append, List.nil_append]
  · rw [hA4_τ1, hA_τ2, hA1_decomp, τ2_cons, noMoveTile_bot, hA3_τ2,
        hA3_decomp, τ2_cons, sepTile_bot]
    cases qNew with
    | none => simp [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
                    stateMarker_none, liftTape_cons, List.append_assoc]
    | some q' => simp [encodeCfg_running, encodeRunningCfg, BiTape.write,
                       stateMarker_some, liftTape_cons, List.append_assoc]

/-- Given `A ⊆ haltTiles tm` and the right-interior matching invariant, peel the canonical
  right-interior step block and advance to the post-step invariant. -/
private lemma starts_with_stepTilesRightInterior (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol) (qNew : Option tm.State) (w : Option Symbol) [Encodable Symbol] [Encodable tm.State]
    (htr : tm.tr q t.head = (⟨w, some Turing.Dir.right⟩, qNew))
    (h_right_ne : t.right.toList ≠ []) (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (A : Stack (Alpha tm.State Symbol)) (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesRightInterior tm q qNew t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        τ1 A' = encodeCfg tm ⟨qNew, (t.write w).moveRight⟩ ++ [#] ++ τ2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Turing.Dir.left⟩, qN) := by
    intro qN w' h; rw [htr] at h; injection h with h1 _
    injection h1 with _ h_dir; injection h_dir with h_dir2; cases h_dir2
  have h_eq' : τ1 A = liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++ τ2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_state_lead tm q t.head h_not_left t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++ τ2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced tm q t.head (liftTape tm t.right.toList ++ [#] ++ τ2 A) A1 hA_mem hA_τ1
  simp only [transitionTilesFor] at h_tile_in; rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · have hA2_τ1 : τ1 A2 = liftTape tm t.right.toList ++ [#] ++ τ2 A := by
      have key := hA_τ1; rw [hA1_decomp, τ1_cons, rightMoveTile_top] at key; simpa using key
    obtain ⟨A3, hA2, hA3_mem, hA3_τ1, hA3_τ2⟩ :=
      copy_prefix_forced tm t.right.toList A2 ([#] ++ τ2 A) hA2_mem
        (by simpa [List.append_assoc] using hA2_τ1)
        (by intro x h; injection h with h1 _; cases h1)
        (by intro q' x h; injection h with h1 _; cases h1)
    obtain ⟨A4, hA3_decomp, hA4_τ1, hA4_mem⟩ :=
      sep_forced tm (τ2 A) A3 hA3_mem (by simpa using hA3_τ1)
    refine ⟨A4, ?_, hA4_mem, ?_⟩
    · rw [hA, hA1_decomp, hA2, hA3_decomp]
      simp only [stepTilesRightInterior, List.append_assoc, List.cons_append, List.nil_append]
    · rw [hA4_τ1, hA_τ2, hA1_decomp, τ2_cons, rightMoveTile_bot, hA3_τ2, hA3_decomp,
          τ2_cons, sepTile_bot, encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]
      simp [List.append_assoc]
  · exfalso
    have key := hA_τ1; rw [hA1_decomp, τ1_cons, rightMoveBoundaryTile_top] at key
    cases h_rt : t.right.toList with
    | nil => exact h_right_ne h_rt
    | cons c cs =>
      rw [h_rt] at key
      simp only [liftTape_cons, List.cons_append, List.nil_append] at key
      injection key with _ key; injection key with _ key; injection key with h_third _; cases h_third

/-- Given `A ⊆ haltTiles tm` and the right-boundary matching invariant (with `qNew = some _`), peel
  the canonical right-boundary step block. The alternative `rightMoveTile` decomposition is ruled
  out by `no_tile_for_state_sharp`. -/
private lemma starts_with_stepTilesRightBoundary (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol) (qNew_q : tm.State) (w : Option Symbol) [Encodable Symbol] [Encodable tm.State]
    (htr : tm.tr q t.head = (⟨w, some Turing.Dir.right⟩, some qNew_q))
    (h_right_empty : t.right.toList = []) (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (A : Stack (Alpha tm.State Symbol)) (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesRightBoundary tm q (some qNew_q) t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        τ1 A' = encodeCfg tm ⟨some qNew_q, (t.write w).moveRight⟩ ++ [#] ++ τ2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Turing.Dir.left⟩, qN) := by
    intro qN w' h; rw [htr] at h; injection h with h1 _
    injection h1 with _ h_dir; injection h_dir with h_dir2; cases h_dir2
  have h_eq' : τ1 A = liftTape tm t.left.toList.reverse ++
      ↟ₛq :: ↟ₜt.head :: ([#] ++ τ2 A) := by
    simpa [encodeRunningCfg, h_right_empty, liftTape_nil, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_state_lead tm q t.head h_not_left t.left.toList.reverse A
      ([#] ++ τ2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced tm q t.head ([#] ++ τ2 A) A1 hA_mem hA_τ1
  simp only [transitionTilesFor] at h_tile_in; rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · exfalso
    have hA2_τ1 : τ1 A2 = [#] ++ τ2 A := by
      have key := hA_τ1; rw [hA1_decomp, τ1_cons, rightMoveTile_top] at key; simpa using key
    obtain ⟨A3, hA2_decomp, hA3_τ1, hA3_mem⟩ :=
      sep_forced tm (τ2 A) A2 hA2_mem (by simpa using hA2_τ1)
    have hA3_τ1_full : τ1 A3 = liftTape tm t.left.toList.reverse ++
        [↟ₜw, ↟ₛqNew_q, #] ++ τ2 A3 := by
      rw [hA3_τ1, hA_τ2, hA1_decomp, hA2_decomp]
      simp [τ2_cons, rightMoveTile_bot, sepTile_bot, stateMarker_some, List.append_assoc]
    obtain ⟨A4, _, hA4_mem, hA4_τ1, _⟩ :=
      copy_prefix_forced tm t.left.toList.reverse A3
        ([↟ₜw, ↟ₛqNew_q, #] ++ τ2 A3) hA3_mem
        (by simpa [List.append_assoc] using hA3_τ1_full)
        (by intro x h; injection h with h1 _; cases h1)
        (by intro q' x h; injection h with h1 _; cases h1)
    cases A4 with
    | nil => simp at hA4_τ1
    | cons t4 A4_rest =>
      have h_t4_mem : t4 ∈ haltTiles tm := hA4_mem t4 (List.mem_cons_self ..)
      have h_t4_rest_mem : ∀ s ∈ A4_rest, s ∈ haltTiles tm :=
        fun s hs => hA4_mem s (List.mem_cons_of_mem t4 hs)
      rw [τ1_cons] at hA4_τ1
      rcases mem_haltTiles_top tm t4 h_t4_mem with
          ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at hA4_τ1
        injection hA4_τ1 with _ h_rest
        exact no_tile_for_state_sharp tm qNew_q (τ2 A3) A4_rest h_t4_rest_mem h_rest
      · simp at hA4_τ1
      · simp at hA4_τ1
      · simp at hA4_τ1
      · simp at hA4_τ1
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at hA4_τ1
        injection hA4_τ1 with _ h; injection h with _ h2; injection h2 with h3 _; cases h3
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at hA4_τ1
        injection hA4_τ1 with _ h; injection h with h2 _; cases h2
      · simp at hA4_τ1
      · simp at hA4_τ1
  · have hA2_τ1 : τ1 A2 = τ2 A := by
      have key := hA_τ1; rw [hA1_decomp, τ1_cons, rightMoveBoundaryTile_top] at key; simpa using key
    refine ⟨A2, ?_, hA2_mem, ?_⟩
    · rw [hA, hA1_decomp]
      simp only [stepTilesRightBoundary, List.append_assoc, List.cons_append, List.nil_append]
    · rw [hA2_τ1, hA_τ2, hA1_decomp, τ2_cons, rightMoveBoundaryTile_bot, stateMarker_some,
          encodeCfg_after_right_move_boundary_eq tm (some qNew_q) t w h_nondeg h_right_empty]
      simp [List.append_assoc]

/-- Given `A ⊆ haltTiles tm` and the left-interior matching invariant, peel the canonical
  left-interior step block and advance to the post-step invariant. -/
private lemma starts_with_stepTilesLeftInterior (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol) (qNew : Option tm.State) (w : Option Symbol) [Encodable Symbol] [Encodable tm.State]
    (htr : tm.tr q t.head = (⟨w, some Turing.Dir.left⟩, qNew))
    (h_left_ne : t.left.toList ≠ []) (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (A : Stack (Alpha tm.State Symbol)) (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesLeftInterior tm q qNew t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        τ1 A' = encodeCfg tm ⟨qNew, (t.write w).moveLeft⟩ ++ [#] ++ τ2 A' := by
  have h_split : t.left.toList.reverse = t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]; simp [List.reverse_cons]
  have h_eq' : τ1 A = liftTape tm t.left.tail.toList.reverse ++
      ↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++ τ2 A) := by
    rw [h_eq, encodeRunningCfg, h_split, liftTape_append, liftTape_cons, liftTape_nil, liftTape_cons]
    simp [List.append_assoc]
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced tm t.left.tail.toList.reverse A
      (↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head :: (liftTape tm t.right.toList ++ [#] ++ τ2 A))
      h_mem h_eq'
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  cases A1 with
  | nil => simp at hA_τ1
  | cons t1 A1_rest =>
    have h_t1_mem : t1 ∈ haltTiles tm := hA_mem t1 (List.mem_cons_self ..)
    have h_a1_rest_mem : ∀ s ∈ A1_rest, s ∈ haltTiles tm :=
      fun s hs => hA_mem s (List.mem_cons_of_mem t1 hs)
    rw [τ1_cons] at hA_τ1
    rcases mem_haltTiles_top tm t1 h_t1_mem with
        ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
      | ⟨q', a', qNew', w', h_tr', b', rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
    · simp only [copyTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h_head h_tail; injection h_head with h_a; subst h_a
      obtain ⟨tile', _, hA1_rest_decomp, h_tile_in, _⟩ :=
        transition_forced tm q t.head (liftTape tm t.right.toList ++ [#] ++ τ2 A) A1_rest
          h_a1_rest_mem (by simpa using h_tail)
      simp only [transitionTilesFor] at h_tile_in; rw [htr] at h_tile_in
      simp only [List.mem_map] at h_tile_in; obtain ⟨_, _, rfl⟩ := h_tile_in
      have key := h_tail; rw [hA1_rest_decomp, τ1_cons, leftMoveTile_top] at key
      simp only [List.cons_append, List.nil_append] at key
      injection key with h_h _; cases h_h
    · simp only [sepTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h
    · simp only [noMoveTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h
    · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h
    · simp only [rightMoveBoundaryTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h
    · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h_b h_rest1; injection h_b with h_b'; subst h_b'
      injection h_rest1 with h_q h_rest2; injection h_q with h_q'; subst h_q'
      injection h_rest2 with h_a h_rest3; injection h_a with h_a'; subst h_a'
      have h_tr_eq := h_tr'.symm.trans htr
      injection h_tr_eq with h_w_eq h_qNew_eq; injection h_w_eq with h_w'; subst w'; subst qNew'
      obtain ⟨A2, hA1_rest_decomp, hA2_mem, hA2_τ1, hA2_τ2⟩ :=
        copy_prefix_forced tm t.right.toList A1_rest ([#] ++ τ2 A) h_a1_rest_mem
          (by simpa [List.append_assoc] using h_rest3)
          (by intro x h; injection h with h1 _; cases h1)
          (by intro q' x h; injection h with h1 _; cases h1)
      obtain ⟨A3, hA2_decomp, hA3_τ1, hA3_mem⟩ :=
        sep_forced tm (τ2 A) A2 hA2_mem (by simpa using hA2_τ1)
      refine ⟨A3, ?_, hA3_mem, ?_⟩
      · rw [hA, hA1_rest_decomp, hA2_decomp]
        simp only [stepTilesLeftInterior, List.append_assoc, List.cons_append, List.nil_append]
      · rw [hA3_τ1, hA_τ2, τ2_cons, leftMoveTile_bot, hA2_τ2, hA2_decomp, τ2_cons, sepTile_bot,
            encodeCfg_after_left_move_eq tm qNew t w h_nondeg]
        simp [List.append_assoc]
    · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with _ h; injection h with h2 _; cases h2
    · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h
    · simp only [finalTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h

/-- The queue encoding: concatenate `encodeCfg tm c ++ [#]` for each `c` in the list. -/
private def queueEncoding (tm : SingleTapeTM Symbol) :
    List tm.Cfg → List (Alpha tm.State Symbol)
  | []        => []
  | c :: rest => encodeCfg tm c ++ [#] ++ queueEncoding tm rest

/-- `queueEncoding tm []` is empty. -/
@[simp]
private lemma queueEncoding_nil (tm : SingleTapeTM Symbol) :
  queueEncoding tm [] = [] := rfl

/-- `queueEncoding tm (c :: rest)` prepends `encodeCfg tm c ++ [#]`. -/
@[simp]
private lemma queueEncoding_cons (tm : SingleTapeTM Symbol)
  (c : tm.Cfg) (rest : List tm.Cfg) :
  queueEncoding tm (c :: rest) = encodeCfg tm c ++ [#] ++ queueEncoding tm rest := rfl

/-- `queueEncoding` distributes over snoc with one element. -/
private lemma queueEncoding_append_single (tm : SingleTapeTM Symbol)
    (cfgs : List tm.Cfg) (c : tm.Cfg) :
    queueEncoding tm (cfgs ++ [c]) = queueEncoding tm cfgs ++ encodeCfg tm c ++ [#] := by
  induction cfgs with
  | nil => simp [queueEncoding]
  | cons _ _ ih => simp [queueEncoding, ih, List.append_assoc]

/-- `queueEncoding` distributes over snoc with two elements. -/
private lemma queueEncoding_append_pair (tm : SingleTapeTM Symbol)
    (cfgs : List tm.Cfg) (c1 c2 : tm.Cfg) :
    queueEncoding tm (cfgs ++ [c1, c2]) =
      queueEncoding tm cfgs ++ encodeCfg tm c1 ++ [#] ++ encodeCfg tm c2 ++ [#] := by
  induction cfgs with
  | nil => simp [queueEncoding]
  | cons _ _ ih => simp [queueEncoding, ih, List.append_assoc]

/-- Weak variant of `copy_prefix_forced`. Identical to the strong version except `A`'s tiles may be
  drawn from `startTile :: haltTiles tm`; the `startTile.top = [#]` case is ruled out by character
  mismatch with `liftTape tm (a :: L)`'s leading `↟ₜa`. -/
private lemma copy_prefix_forced_weak (tm : SingleTapeTM Symbol)
    (w_in : List Symbol) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (tail : List (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State],
      (∀ t ∈ A, t ∈ startTile tm w_in :: haltTiles tm) →
      τ1 A = liftTape tm L ++ tail →
      (∀ x : List (Alpha tm.State Symbol), tail ≠ h⊥ :: x) →
      (∀ (q : tm.State) (x : List (Alpha tm.State Symbol)),
          tail ≠ ↟ₛq :: x) →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ t ∈ A', t ∈ startTile tm w_in :: haltTiles tm) ∧
          τ1 A' = tail ∧
          τ2 A = liftTape tm L ++ τ2 A' := by
  intro L
  induction L with
  | nil =>
    intro A tail _ _ h_mem h_eq _ _
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a L ih =>
    intro A tail _ _ h_mem h_eq h_not_halt h_not_state
    cases A with
    | nil => simp_all [liftTape_cons]
    | cons t A_rest =>
      have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
        h_mem t (List.mem_cons_self ..)
      have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [τ1_cons, liftTape_cons, List.cons_append] at h_eq
      rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
      · simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · rcases mem_haltTiles_top tm t h_t_lu with
            ⟨a', rfl⟩
          | rfl
          | ⟨_, _, _, _, _, rfl⟩
          | ⟨_, _, _, _, _, rfl | rfl⟩
          | ⟨q', _, _, _, _, _, rfl⟩
          | ⟨_, rfl⟩
          | ⟨_, rfl⟩
          | rfl
        · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with h_head h_tail
          injection h_head with h_a
          subst h_a
          obtain ⟨A', hA, hA_mem, hA_τ1, hA_τ2⟩ :=
            ih A_rest tail h_rest_in h_tail h_not_halt h_not_state
          refine ⟨A', ?_, hA_mem, hA_τ1, ?_⟩
          · simp [List.map_cons, hA]
          · simp [τ2_cons, copyTile_bot, hA_τ2, liftTape_cons]
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest
            exact (h_not_state q' _ h_rest.symm).elim
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest
            injection h_rest with h_h
            cases h_h
        · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest
            exact (h_not_halt _ h_rest.symm).elim
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest
            injection h_rest with h_h
            cases h_h
        · simp at h_eq
        · simp at h_eq

/-- Weak variant of `copy_prefix_forced_state_lead`. -/
private lemma copy_prefix_forced_state_lead_weak (tm : SingleTapeTM Symbol)
    (w_in : List Symbol) (q : tm.State) (a : Option Symbol) [Encodable Symbol] [Encodable tm.State]
    (h_not_left : ∀ (qNew : Option tm.State) (w : Option Symbol),
        tm.tr q a ≠ (⟨w, some Turing.Dir.left⟩, qNew)) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (rest : List (Alpha tm.State Symbol)),
      (∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm) →
      τ1 A = liftTape tm L ++ ↟ₛq :: ↟ₜa :: rest →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
          τ1 A' = ↟ₛq :: ↟ₜa :: rest ∧
          τ2 A = liftTape tm L ++ τ2 A' := by
  intro L; induction L with
  | nil =>
    intro A rest h_mem h_eq
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a' L ih =>
    intro A rest h_mem h_eq
    cases A with
    | nil => simp [liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_in : t ∈ startTile tm w_in :: haltTiles tm := h_mem t (List.mem_cons_self ..)
      have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [τ1_cons, liftTape_cons, List.cons_append] at h_eq
      rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
      · simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h
      · rcases mem_haltTiles_top tm t h_t_lu with
            ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
          | ⟨q', a'', _, _, h_tr, b, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
        · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with h_head h_tail; injection h_head with h_a; subst h_a
          obtain ⟨A', hA, hA_mem, hA_τ1, hA_τ2⟩ := ih A_rest rest h_rest_in h_tail
          exact ⟨A', by simp [List.map_cons, hA], hA_mem, hA_τ1,
                 by simp [τ2_cons, copyTile_bot, hA_τ2, liftTape_cons]⟩
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest1
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest1
            injection h_rest1 with h_q_eq h_rest2; injection h_q_eq with h_q_eq'; subst h_q_eq'
            injection h_rest2 with h_a_eq _; injection h_a_eq with h_a_eq'; subst h_a_eq'
            exact (h_not_left _ _ h_tr).elim
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest1
            injection h_rest1 with h_h; cases h_h
        · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest
            injection h_rest with h_h; cases h_h
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest
            injection h_rest with h_h; cases h_h
        · simp at h_eq
        · simp at h_eq

/-- Weak variant of `transition_forced`. -/
private lemma transition_forced_weak (tm : SingleTapeTM Symbol) (w_in : List Symbol)
    (q : tm.State) (a : Option Symbol) (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ t ∈ A, t ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : τ1 A = ↟ₛq :: ↟ₜa :: rest) :
    ∃ (tile : Tile (Alpha tm.State Symbol)) (A' : Stack (Alpha tm.State Symbol)),
      A = tile :: A' ∧ tile ∈ transitionTilesFor tm q a ∧
      (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_in : t ∈ startTile tm w_in :: haltTiles tm := h_mem t (List.mem_cons_self ..)
    have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    refine ⟨t, A_rest, rfl, ?_, h_rest_in⟩
    rw [τ1_cons] at h_eq
    rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
    · simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _; cases h_h
    · rcases mem_haltTiles_top tm t h_t_lu with
          ⟨_, rfl⟩ | rfl | ⟨q', a', qNew, w, h_tr, rfl⟩ | ⟨q', a', qNew, w, h_tr, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h
      · simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h h_rest; injection h_h with h_q'; subst h_q'
        injection h_rest with h_a _; injection h_a with h_a'; subst h_a'
        simp only [transitionTilesFor]; rw [h_tr]; exact List.mem_singleton.mpr rfl
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h h_rest; injection h_h with h_q'; subst h_q'
        injection h_rest with h_a _; injection h_a with h_a'; subst h_a'
        simp only [transitionTilesFor]; rw [h_tr]; exact List.mem_cons_self
      · simp only [rightMoveBoundaryTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h h_rest; injection h_h with h_q'; subst h_q'
        injection h_rest with h_a _; injection h_a with h_a'; subst h_a'
        simp only [transitionTilesFor]; rw [h_tr]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h
      · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h
      · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _; cases h_h

/-- Weak variant of `sep_forced`: returns a disjunction distinguishing `sepTile` (contributing `[#]`
  to `τ2`) from `startTile` (contributing the full init encoding). -/
private lemma sep_forced_weak (tm : SingleTapeTM Symbol) (w_in : List Symbol)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : τ1 A = # :: rest) :
    ∃ A' : Stack (Alpha tm.State Symbol),
      ((A = sepTile tm :: A' ∧
        τ2 A = # :: τ2 A') ∨
       (A = startTile tm w_in :: A' ∧
        τ2 A = # :: encodeCfg tm (SingleTapeTM.initCfg tm w_in) ++ [#] ++ τ2 A')) ∧
      τ1 A' = rest ∧
      (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
      h_mem t (List.mem_cons_self ..)
    have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    rw [τ1_cons] at h_eq
    rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
    · simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with _ h_tail
      refine ⟨A_rest, Or.inr ⟨rfl, ?_⟩, h_tail, h_rest_in⟩
      simp [τ2_cons, startTile_bot, List.append_assoc]
    · rcases mem_haltTiles_top tm t h_t_lu with
          ⟨_, rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_tail
        refine ⟨A_rest, Or.inl ⟨rfl, ?_⟩, h_tail, h_rest_in⟩
        simp [τ2_cons, sepTile_bot]
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [rightMoveBoundaryTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h

/-- `τ1 A` never contains `↟ₛq :: # :: …` as a sublist, for any `A ⊆ startTile :: haltTiles tm`.
  Used to discharge the alternative `rightMoveTile` path in the boundary step lemma. -/
private lemma τ1_no_state_marker_then_sharp
    (tm : SingleTapeTM Symbol) (w_in : List Symbol) (q : tm.State) [Encodable Symbol] [Encodable tm.State]:
    ∀ (A : Stack (Alpha tm.State Symbol)) (l1 l2 : List (Alpha tm.State Symbol)),
      (∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm) →
      τ1 A = l1 ++ ↟ₛq :: # :: l2 → False := by
  intro A; induction A with
  | nil => intro l1 l2 _ h; rw [τ1_nil] at h; cases l1 <;> simp at h
  | cons t A_rest ih =>
    intro l1 l2 h_mem h_eq
    have h_t_in : t ∈ startTile tm w_in :: haltTiles tm := h_mem t (List.mem_cons_self ..)
    have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    rw [τ1_cons] at h_eq
    rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
    · simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
      cases l1 with
      | nil => injection h_eq with h _; cases h
      | cons _ l1' =>
        simp only [List.cons_append] at h_eq; injection h_eq with _ h_tail
        exact ih l1' l2 h_rest_in h_tail
    · rcases mem_haltTiles_top tm t h_t_lu with
          ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          simp only [List.cons_append] at h_eq; injection h_eq with _ h_tail
          exact ih l1' l2 h_rest_in h_tail
      · simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          simp only [List.cons_append] at h_eq; injection h_eq with _ h_tail
          exact ih l1' l2 h_rest_in h_tail
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with _ h2; injection h2 with h _; cases h
        | cons _ l1' => cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq; injection h_eq with _ h2
            injection h2 with _ h_tail; exact ih l1'' l2 h_rest_in h_tail
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with _ h2; injection h2 with h _; cases h
        | cons _ l1' => cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq; injection h_eq with _ h2
            injection h2 with _ h_tail; exact ih l1'' l2 h_rest_in h_tail
      · simp only [rightMoveBoundaryTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with _ h2; injection h2 with h _; cases h
        | cons _ l1' => cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' => cases l1'' with
            | nil =>
              injection h_eq with _ h2; injection h2 with _ h3
              injection h3 with h _; cases h
            | cons _ l1''' =>
              simp only [List.cons_append] at h_eq; injection h_eq with _ h2
              injection h2 with _ h3; injection h3 with _ h_tail
              exact ih l1''' l2 h_rest_in h_tail
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' => cases l1' with
          | nil =>
            injection h_eq with _ h2; injection h2 with _ h3
            injection h3 with h _; cases h
          | cons _ l1'' => cases l1'' with
            | nil =>
              injection h_eq with _ h2; injection h2 with _ h3
              injection h3 with h _; cases h
            | cons _ l1''' =>
              simp only [List.cons_append] at h_eq; injection h_eq with _ h2
              injection h2 with _ h3; injection h3 with _ h_tail
              exact ih l1''' l2 h_rest_in h_tail
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' => cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq; injection h_eq with _ h2
            injection h2 with _ h_tail; exact ih l1'' l2 h_rest_in h_tail
      · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' => cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq; injection h_eq with _ h2
            injection h2 with _ h_tail; exact ih l1'' l2 h_rest_in h_tail
      · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' => cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' => cases l1'' with
            | nil =>
              injection h_eq with _ h2; injection h2 with _ h3
              injection h3 with h _; cases h
            | cons _ l1''' =>
              simp only [List.cons_append] at h_eq; injection h_eq with _ h2
              injection h2 with _ h3; injection h3 with _ h_tail
              exact ih l1''' l2 h_rest_in h_tail

/-- Extras-aware no-move step lemma: given `A ⊆ startTile :: haltTiles tm` and the queue-extended
  matching invariant, returns a shorter residual whose invariant has the queue augmented by
  `stepResult` (or `stepResult` and `initCfg` if `startTile` appeared). -/
private lemma starts_with_stepTilesNoMove_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol) [Encodable Symbol] [Encodable tm.State]
    (htr : tm.tr q t.head = (⟨w, none⟩, qNew))
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        ((τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, t.write w⟩]) ++ τ2 A') ∨
         (τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, t.write w⟩,
              SingleTapeTM.initCfg tm w_in]) ++ τ2 A')) := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Turing.Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    cases h_dir
  have h_eq' : τ1 A =
      liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
        (liftTape tm t.right.toList ++ [#] ++
          queueEncoding tm rest_cfgs ++ τ2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_state_lead_weak tm w_in q t.head h_not_left
      t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced_weak tm w_in q t.head
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A) A1 hA_mem hA_τ1
  have h_tile_eq : tile = noMoveTile tm q t.head qNew w := by
    simp only [transitionTilesFor] at h_tile_in
    rw [htr] at h_tile_in
    exact List.mem_singleton.mp h_tile_in
  subst h_tile_eq
  have hA2_τ1 : τ1 A2 = liftTape tm t.right.toList ++ [#] ++
      queueEncoding tm rest_cfgs ++ τ2 A := by
    have key := hA_τ1
    rw [hA1_decomp, τ1_cons, noMoveTile_top] at key
    simpa using key
  obtain ⟨A3, hA2, hA3_mem, hA3_τ1, hA3_τ2⟩ :=
    copy_prefix_forced_weak tm w_in t.right.toList A2
      ([#] ++ queueEncoding tm rest_cfgs ++ τ2 A) hA2_mem
      (by simpa [List.append_assoc] using hA2_τ1)
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  obtain ⟨A4, hA3_decomp_disj, hA4_τ1, hA4_mem⟩ :=
    sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ τ2 A) A3
      hA3_mem (by simpa using hA3_τ1)
  refine ⟨A4, ?_, hA4_mem, ?_⟩
  · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
    all_goals
      rw [hA, hA1_decomp, hA2, hA3_decomp]
      simp [List.length_append, List.length_map, List.length_reverse]
      omega
  · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
    · left
      rw [hA4_τ1, hA_τ2, hA1_decomp, τ2_cons, noMoveTile_bot, hA3_τ2,
          hA3_decomp, τ2_cons, sepTile_bot, queueEncoding_append_single]
      cases qNew with
      | none =>
        simp [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
              stateMarker_none, liftTape_cons, List.append_assoc]
      | some q' =>
        simp [encodeCfg_running, encodeRunningCfg, BiTape.write,
              stateMarker_some, liftTape_cons, List.append_assoc]
    · right
      rw [hA4_τ1, hA_τ2, hA1_decomp, τ2_cons, noMoveTile_bot, hA3_τ2,
          hA3_decomp, τ2_cons, startTile_bot, queueEncoding_append_pair]
      cases qNew with
      | none =>
        simp [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
              stateMarker_none, liftTape_cons, List.append_assoc]
      | some q' =>
        simp [encodeCfg_running, encodeRunningCfg, BiTape.write,
              stateMarker_some, liftTape_cons, List.append_assoc]

/-- Extras-aware right-boundary step lemma. The alternative `rightMoveTile` path is discharged by
  `τ1_no_state_marker_then_sharp`. -/
private lemma starts_with_stepTilesRightBoundary_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew_q : tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Turing.Dir.right⟩, some qNew_q))
    (h_right_empty : t.right.toList = [])
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨some qNew_q, (t.write w).moveRight⟩]) ++ τ2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Turing.Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    injection h_dir with h_dir2
    cases h_dir2
  have h_eq' : τ1 A = liftTape tm t.left.toList.reverse ++
      ↟ₛq :: ↟ₜt.head :: ([#] ++ queueEncoding tm rest_cfgs ++ τ2 A) := by
    simpa [encodeRunningCfg, h_right_empty, liftTape_nil,
           List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_state_lead_weak tm w_in q t.head h_not_left
      t.left.toList.reverse A
      ([#] ++ queueEncoding tm rest_cfgs ++ τ2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced_weak tm w_in q t.head
      ([#] ++ queueEncoding tm rest_cfgs ++ τ2 A) A1 hA_mem hA_τ1
  simp only [transitionTilesFor] at h_tile_in
  rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · exfalso
    have hA2_τ1 : τ1 A2 = [#] ++ queueEncoding tm rest_cfgs ++ τ2 A := by
      have key := hA_τ1
      rw [hA1_decomp, τ1_cons, rightMoveTile_top] at key
      simpa using key
    obtain ⟨A3, hA2_decomp_disj, hA3_τ1, hA3_mem⟩ :=
      sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ τ2 A) A2
        hA2_mem (by simpa using hA2_τ1)
    rcases hA2_decomp_disj with ⟨hA2_decomp, _⟩ | ⟨hA2_decomp, _⟩
    · have hA3_τ1_full :
          τ1 A3 = (queueEncoding tm rest_cfgs ++
              liftTape tm t.left.toList.reverse ++ [↟ₜw]) ++
            ↟ₛqNew_q :: # :: τ2 A3 := by
        rw [hA3_τ1, hA_τ2, hA1_decomp, τ2_cons, rightMoveTile_bot,
            hA2_decomp, τ2_cons, sepTile_bot, stateMarker_some]
        simp [List.append_assoc]
      exact τ1_no_state_marker_then_sharp tm w_in qNew_q A3 _ (τ2 A3)
        hA3_mem hA3_τ1_full
    · have hA3_τ1_full :
          τ1 A3 = (queueEncoding tm rest_cfgs ++
              liftTape tm t.left.toList.reverse ++ [↟ₜw]) ++
            ↟ₛqNew_q :: # ::
              (encodeCfg tm (SingleTapeTM.initCfg tm w_in) ++
                [#] ++ τ2 A3) := by
        rw [hA3_τ1, hA_τ2, hA1_decomp, τ2_cons, rightMoveTile_bot,
            hA2_decomp, τ2_cons, startTile_bot, stateMarker_some]
        simp [List.append_assoc]
      exact τ1_no_state_marker_then_sharp tm w_in qNew_q A3 _ _
        hA3_mem hA3_τ1_full
  · have hA2_τ1 : τ1 A2 = queueEncoding tm rest_cfgs ++ τ2 A := by
      have key := hA_τ1
      rw [hA1_decomp, τ1_cons, rightMoveBoundaryTile_top] at key
      simpa using key
    refine ⟨A2, ?_, hA2_mem, ?_⟩
    · rw [hA, hA1_decomp]
      simp [List.length_append, List.length_map, List.length_reverse]
      omega
    · rw [hA2_τ1, hA_τ2, hA1_decomp, τ2_cons,
          rightMoveBoundaryTile_bot, stateMarker_some,
          queueEncoding_append_single,
          encodeCfg_after_right_move_boundary_eq tm (some qNew_q) t w
            h_nondeg h_right_empty]
      simp [List.append_assoc]

/-- Main backward strong-induction lemma for `A ⊆ haltTiles tm`. Produces a halting trace from a
  stack satisfying the matching invariant. -/
private lemma backward_aux (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w_in : List Symbol)
    (h_nlb : NoLeftBoundary tm w_in) [Encodable Symbol] [Encodable tm.State] :
    ∀ (n : ℕ) (A : Stack (Alpha tm.State Symbol)) (cfg : tm.Cfg),
      A.length ≤ n →
      Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) cfg →
      (∀ s ∈ A, s ∈ haltTiles tm) →
      τ1 A = encodeCfg tm cfg ++ [#] ++ τ2 A →
      ∃ tape : BiTape Symbol,
        Relation.ReflTransGen tm.TransitionRelation cfg
            ⟨none, tape⟩ := by
  intro n
  induction n with
  | zero =>
    intro A cfg hLen _ _ hMatch
    have hA_nil : A = [] := by
      cases A with
      | nil => rfl
      | cons _ _ => simp at hLen
    subst hA_nil
    exfalso
    simp only [τ1_nil, τ2_nil, List.append_nil] at hMatch
    have h_len_zero : (encodeCfg tm cfg ++ [#]).length = 0 := by
      have := congrArg List.length hMatch
      simpa using this.symm
    simp [List.length_append] at h_len_zero
  | succ n ih =>
    intro A cfg hLen hReach hMem hMatch
    cases hcfg : cfg with
    | mk state tape =>
      cases state with
      | none =>
        exact ⟨tape, Relation.ReflTransGen.refl⟩
      | some q =>
        rcases h_tr : tm.tr q tape.head with ⟨⟨w', mov⟩, qNew⟩
        have hMatch' : τ1 A = encodeRunningCfg tm q tape ++ [#] ++ τ2 A := by
          rw [hcfg] at hMatch; exact hMatch
        have h_w_ne : w' ≠ none := by
          have := h_nbw q tape.head; rw [h_tr] at this; exact this
        have h_reach' : Relation.ReflTransGen tm.TransitionRelation
            (SingleTapeTM.initCfg tm w_in) (stepResult tm q tape) := by
          refine hReach.tail ?_
          show tm.step cfg = some (stepResult tm q tape)
          rw [hcfg]; exact tm_step_running tm q tape
        cases mov with
        | none =>
          obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
            starts_with_stepTilesNoMove tm q tape qNew w' h_tr A hMem hMatch'
          have hA'_len : A'.length ≤ n := by
            have h_split : A.length =
                (stepTilesNoMove tm q qNew tape w').length + A'.length := by
              rw [hA']; simp
            have h_step_pos :
                0 < (stepTilesNoMove tm q qNew tape w').length := by
              simp [stepTilesNoMove]
            omega
          have h_stepRes : stepResult tm q tape = ⟨qNew, tape.write w'⟩ := by
            simp [stepResult, h_tr, BiTape.optionMove]
          have hA'_match' :
              τ1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ τ2 A' := by
            rw [h_stepRes]; exact hA'_match
          obtain ⟨tape_h, h_h⟩ :=
            ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
          exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩
        | some dir =>
          cases dir with
          | right =>
            cases h_right : tape.right.toList with
            | nil =>
              cases qNew with
              | none =>
                refine ⟨(tape.write w').moveRight, ?_⟩
                refine Relation.ReflTransGen.single ?_
                show tm.step ⟨some q, tape⟩ = some _
                rw [← tm_step_running]
                congr 1
                simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
              | some qNew_q =>
                obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
                  starts_with_stepTilesRightBoundary tm q tape qNew_q w' h_tr
                    h_right (Or.inl h_w_ne) A hMem hMatch'
                have hA'_len : A'.length ≤ n := by
                  have h_split : A.length =
                      (stepTilesRightBoundary tm q (some qNew_q) tape w').length +
                        A'.length := by rw [hA']; simp
                  have h_step_pos :
                      0 < (stepTilesRightBoundary tm q (some qNew_q) tape w').length := by
                    simp [stepTilesRightBoundary]
                  omega
                have h_stepRes :
                    stepResult tm q tape = ⟨some qNew_q, (tape.write w').moveRight⟩ := by
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                have hA'_match' :
                    τ1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ τ2 A' := by
                  rw [h_stepRes]; exact hA'_match
                obtain ⟨tape_h, h_h⟩ :=
                  ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
                exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩
            | cons _ _ =>
              have h_right_ne : tape.right.toList ≠ [] := by
                rw [h_right]; exact List.cons_ne_nil _ _
              obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
                starts_with_stepTilesRightInterior tm q tape qNew w' h_tr
                  h_right_ne (Or.inl h_w_ne) A hMem hMatch'
              have hA'_len : A'.length ≤ n := by
                have h_split : A.length =
                    (stepTilesRightInterior tm q qNew tape w').length + A'.length := by
                  rw [hA']; simp
                have h_step_pos :
                    0 < (stepTilesRightInterior tm q qNew tape w').length := by
                  simp [stepTilesRightInterior]
                omega
              have h_stepRes :
                  stepResult tm q tape = ⟨qNew, (tape.write w').moveRight⟩ := by
                simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
              have hA'_match' :
                  τ1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ τ2 A' := by
                rw [h_stepRes]; exact hA'_match
              obtain ⟨tape_h, h_h⟩ :=
                ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
              exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩
          | left =>
            cases h_left : tape.left.toList with
            | nil =>
              exfalso
              have h_no_lb := h_nlb cfg hReach q tape hcfg h_left
              apply h_no_lb
              rw [h_tr]
            | cons _ _ =>
              have h_left_ne : tape.left.toList ≠ [] := by
                rw [h_left]; exact List.cons_ne_nil _ _
              obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
                starts_with_stepTilesLeftInterior tm q tape qNew w' h_tr
                  h_left_ne (Or.inl h_w_ne) A hMem hMatch'
              have hA'_len : A'.length ≤ n := by
                have h_split : A.length =
                    (stepTilesLeftInterior tm q qNew tape w').length + A'.length := by
                  rw [hA']; simp
                have h_step_pos :
                    0 < (stepTilesLeftInterior tm q qNew tape w').length := by
                  simp [stepTilesLeftInterior]
                omega
              have h_stepRes :
                  stepResult tm q tape = ⟨qNew, (tape.write w').moveLeft⟩ := by
                simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
              have hA'_match' :
                  τ1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ τ2 A' := by
                rw [h_stepRes]; exact hA'_match
              obtain ⟨tape_h, h_h⟩ :=
                ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
              exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩

/-- Given a valid stack of tiles whose top projection encodes a Turing machine configuration before
  an interior right-moving transition (i.e., the right tape is not empty), there exists a strictly
  shorter valid stack whose top projection encodes the configuration after the transition (and
  optionally the initial configuration) appended to the configuration queue. -/
private lemma starts_with_stepTilesRightInterior_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Turing.Dir.right⟩, qNew))
    (h_right_ne : t.right.toList ≠ [])
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        ((τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).moveRight⟩]) ++ τ2 A') ∨
         (τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).moveRight⟩,
              SingleTapeTM.initCfg tm w_in]) ++ τ2 A')) := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Turing.Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    injection h_dir with h_dir2
    cases h_dir2
  have h_eq' : τ1 A = liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_state_lead_weak tm w_in q t.head h_not_left
      t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced_weak tm w_in q t.head
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A) A1 hA_mem hA_τ1
  simp only [transitionTilesFor] at h_tile_in
  rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · have hA2_τ1 : τ1 A2 = liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A := by
      have key := hA_τ1
      rw [hA1_decomp, τ1_cons, rightMoveTile_top] at key
      simpa using key
    obtain ⟨A3, hA2, hA3_mem, hA3_τ1, hA3_τ2⟩ :=
      copy_prefix_forced_weak tm w_in t.right.toList A2
        ([#] ++ queueEncoding tm rest_cfgs ++ τ2 A) hA2_mem
        (by simpa [List.append_assoc] using hA2_τ1)
        (by intro x h; injection h with h1 _; cases h1)
        (by intro q' x h; injection h with h1 _; cases h1)
    obtain ⟨A4, hA3_decomp_disj, hA4_τ1, hA4_mem⟩ :=
      sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ τ2 A) A3
        hA3_mem (by simpa using hA3_τ1)
    refine ⟨A4, ?_, hA4_mem, ?_⟩
    · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
      all_goals
        rw [hA, hA1_decomp, hA2, hA3_decomp]
        simp [List.length_append, List.length_map, List.length_reverse]
        omega
    · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
      · left
        rw [hA4_τ1, hA_τ2, hA1_decomp, τ2_cons, rightMoveTile_bot,
            hA3_τ2, hA3_decomp, τ2_cons, sepTile_bot,
            queueEncoding_append_single,
            encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]
        simp [List.append_assoc]
      · right
        rw [hA4_τ1, hA_τ2, hA1_decomp, τ2_cons, rightMoveTile_bot,
            hA3_τ2, hA3_decomp, τ2_cons, startTile_bot,
            queueEncoding_append_pair,
            encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]
        simp [List.append_assoc]
  · exfalso
    have key := hA_τ1
    rw [hA1_decomp, τ1_cons, rightMoveBoundaryTile_top] at key
    cases h_rt : t.right.toList with
    | nil => exact h_right_ne h_rt
    | cons c cs =>
      rw [h_rt] at key
      simp only [liftTape_cons, List.cons_append, List.nil_append] at key
      injection key with _ key
      injection key with _ key
      injection key with h_third _
      cases h_third

/-- Given a valid stack of tiles whose top projection encodes a Turing machine configuration before
  an interior left-moving transition (i.e., the left tape is not empty), there exists a strictly
  shorter valid stack whose top projection encodes the configuration after the transition (and
  optionally the initial configuration) appended to the configuration queue. -/
private lemma starts_with_stepTilesLeftInterior_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Turing.Dir.left⟩, qNew))
    (h_left_ne : t.left.toList ≠ [])
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol)) [Encodable Symbol] [Encodable tm.State]
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : τ1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ τ2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        ((τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).moveLeft⟩]) ++ τ2 A') ∨
         (τ1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).moveLeft⟩,
              SingleTapeTM.initCfg tm w_in]) ++ τ2 A')) := by
  have h_split : t.left.toList.reverse =
      t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]
    simp [List.reverse_cons]
  have h_eq' : τ1 A = liftTape tm t.left.tail.toList.reverse ++
      ↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ τ2 A) := by
    rw [h_eq, encodeRunningCfg, h_split,
        liftTape_append, liftTape_cons, liftTape_nil, liftTape_cons]
    simp [List.append_assoc]
  obtain ⟨A1, hA, hA_mem, hA_τ1, hA_τ2⟩ :=
    copy_prefix_forced_weak tm w_in t.left.tail.toList.reverse A
      (↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
        (liftTape tm t.right.toList ++ [#] ++
          queueEncoding tm rest_cfgs ++ τ2 A))
      h_mem h_eq'
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  cases A1 with
  | nil => simp at hA_τ1
  | cons t1 A1_rest =>
    have h_t1_in : t1 ∈ startTile tm w_in :: haltTiles tm :=
      hA_mem t1 (List.mem_cons_self ..)
    have h_a1_rest_in : ∀ s ∈ A1_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => hA_mem s (List.mem_cons_of_mem t1 hs)
    rw [τ1_cons] at hA_τ1
    rcases List.mem_cons.mp h_t1_in with rfl | h_t1_lu
    · simp only [startTile_top, List.cons_append, List.nil_append] at hA_τ1
      injection hA_τ1 with h _; cases h
    · rcases mem_haltTiles_top tm t1 h_t1_lu with
          ⟨_, rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨q', a', qNew', w', h_tr', b', rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at hA_τ1
        injection hA_τ1 with h_head h_tail
        injection h_head with h_a; subst h_a
        obtain ⟨tile', _, hA1_rest_decomp, h_tile_in, _⟩ :=
          transition_forced_weak tm w_in q t.head
            (liftTape tm t.right.toList ++ [#] ++
              queueEncoding tm rest_cfgs ++ τ2 A) A1_rest
            h_a1_rest_in (by simpa using h_tail)
        simp only [transitionTilesFor] at h_tile_in
        rw [htr] at h_tile_in
        simp only [List.mem_map] at h_tile_in
        obtain ⟨_, _, rfl⟩ := h_tile_in
        have key := h_tail
        rw [hA1_rest_decomp, τ1_cons, leftMoveTile_top] at key
        simp only [List.cons_append, List.nil_append] at key
        injection key with h_h _
        cases h_h
      · simp only [sepTile_top, List.cons_append, List.nil_append] at hA_τ1
        injection hA_τ1 with h _; cases h
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at hA_τ1
        injection hA_τ1 with h _; cases h
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at hA_τ1
        injection hA_τ1 with h _; cases h
      · simp only [rightMoveBoundaryTile_top, List.cons_append,
                   List.nil_append] at hA_τ1
        injection hA_τ1 with h _; cases h
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at hA_τ1
        injection hA_τ1 with h_b h_rest1
        injection h_b with h_b'
        subst h_b'
        injection h_rest1 with h_q h_rest2
        injection h_q with h_q'
        subst h_q'
        injection h_rest2 with h_a h_rest3
        injection h_a with h_a'
        subst h_a'
        have h_tr_eq := h_tr'.symm.trans htr
        injection h_tr_eq with h_w_eq h_qNew_eq
        injection h_w_eq with h_w'
        subst w'
        subst qNew'
        obtain ⟨A2, hA1_rest_decomp, hA2_mem, hA2_τ1, hA2_τ2⟩ :=
          copy_prefix_forced_weak tm w_in t.right.toList A1_rest
            ([#] ++ queueEncoding tm rest_cfgs ++ τ2 A) h_a1_rest_in
            (by simpa [List.append_assoc] using h_rest3)
            (by intro x h; injection h with h1 _; cases h1)
            (by intro q' x h; injection h with h1 _; cases h1)
        obtain ⟨A3, hA2_decomp_disj, hA3_τ1, hA3_mem⟩ :=
          sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ τ2 A) A2
            hA2_mem (by simpa using hA2_τ1)
        refine ⟨A3, ?_, hA3_mem, ?_⟩
        · rcases hA2_decomp_disj with ⟨hA2_decomp, _⟩ | ⟨hA2_decomp, _⟩
          all_goals
            rw [hA, hA1_rest_decomp, hA2_decomp]
            simp [List.length_append, List.length_map, List.length_reverse,
                  List.length_cons]
            omega
        · rcases hA2_decomp_disj with ⟨hA2_decomp, _⟩ | ⟨hA2_decomp, _⟩
          · left
            rw [hA3_τ1, hA_τ2, τ2_cons, leftMoveTile_bot,
                hA2_τ2, hA2_decomp, τ2_cons, sepTile_bot,
                queueEncoding_append_single,
                encodeCfg_after_left_move_eq tm qNew t w h_nondeg]
            simp [List.append_assoc]
          · right
            rw [hA3_τ1, hA_τ2, τ2_cons, leftMoveTile_bot,
                hA2_τ2, hA2_decomp, τ2_cons, startTile_bot,
                queueEncoding_append_pair,
                encodeCfg_after_left_move_eq tm qNew t w h_nondeg]
            simp [List.append_assoc]
      · simp only [absorbLeftTile_top, List.cons_append,
                   List.nil_append] at hA_τ1
        injection hA_τ1 with _ h
        injection h with h2 _
        cases h2
      · simp only [absorbRightTile_top, List.cons_append,
                   List.nil_append] at hA_τ1
        injection hA_τ1 with h _; cases h
      · simp only [finalTile_top, List.cons_append, List.nil_append] at hA_τ1
        injection hA_τ1 with h _; cases h

/-- Queue-based backward induction for `A ⊆ startTile :: haltTiles tm`. Threads a chain-tracked cfg
  queue through the matching invariant. -/
private lemma backward_aux_weak (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w_in : List Symbol)
    (h_nlb : NoLeftBoundary tm w_in) [Encodable Symbol] [Encodable tm.State]:
    ∀ (n : ℕ) (A : Stack (Alpha tm.State Symbol))
       (queue : List tm.Cfg)
       (_chains : ∀ c ∈ queue, Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) c),
      A.length ≤ n →
      queue ≠ [] →
      (∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm) →
      τ1 A = queueEncoding tm queue ++ τ2 A →
      ∃ tape : BiTape Symbol,
        Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) ⟨none, tape⟩ := by
  intro n
  induction n with
  | zero =>
    intro A queue _chains hLen hQ_ne _ hMatch
    exfalso
    have hA_nil : A = [] := by
      cases A with | nil => rfl | cons _ _ => simp at hLen
    subst hA_nil
    simp only [τ1_nil, τ2_nil, List.append_nil] at hMatch
    cases queue with
    | nil => exact hQ_ne rfl
    | cons head rest =>
      simp [queueEncoding] at hMatch
  | succ n ih =>
    intro A queue chains hLen hQ_ne h_mem hMatch
    cases queue with
    | nil => exact (hQ_ne rfl).elim
    | cons cfg rest_cfgs =>
      have hMatch' : τ1 A = encodeCfg tm cfg ++ [#] ++
                       queueEncoding tm rest_cfgs ++ τ2 A := by
        rw [hMatch, queueEncoding_cons, List.append_assoc]
      have chain_cfg : Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) cfg :=
        chains cfg (List.mem_cons_self ..)
      have rest_chains :
          ∀ c ∈ rest_cfgs,
            Relation.ReflTransGen tm.TransitionRelation
              (SingleTapeTM.initCfg tm w_in) c :=
        fun c hc => chains c (List.mem_cons_of_mem cfg hc)
      cases hcfg : cfg with
      | mk state tape =>
        cases state with
        | none =>
          refine ⟨tape, ?_⟩
          rw [← hcfg]; exact chain_cfg
        | some q =>
          rcases h_tr : tm.tr q tape.head with ⟨⟨w', mov⟩, qNew⟩
          have h_w_ne : w' ≠ none := by
            have := h_nbw q tape.head; rw [h_tr] at this; exact this
          have hMatch'' : τ1 A = encodeRunningCfg tm q tape ++ [#] ++
                            queueEncoding tm rest_cfgs ++ τ2 A := by
            rw [hcfg] at hMatch'; exact hMatch'
          have h_step_cfg : tm.step cfg = some (stepResult tm q tape) := by
            rw [hcfg]; exact tm_step_running tm q tape
          have new_chain_step : Relation.ReflTransGen tm.TransitionRelation
              (SingleTapeTM.initCfg tm w_in) (stepResult tm q tape) :=
            chain_cfg.tail h_step_cfg
          cases mov with
          | none =>
            obtain ⟨A', hLen', hMem', hτ1Disj⟩ :=
              starts_with_stepTilesNoMove_weak_ext tm w_in q tape qNew w' h_tr
                rest_cfgs A h_mem hMatch''
            have hA'_len : A'.length ≤ n := by omega
            have h_stepRes : stepResult tm q tape = ⟨qNew, tape.write w'⟩ := by
              simp [stepResult, h_tr, BiTape.optionMove]
            have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                (SingleTapeTM.initCfg tm w_in) ⟨qNew, tape.write w'⟩ := by
              rw [← h_stepRes]; exact new_chain_step
            rcases hτ1Disj with hSep | hStart
            · refine ih A' (rest_cfgs ++ [⟨qNew, tape.write w'⟩]) ?_ hA'_len
                ?_ hMem' hSep
              · intro c hc
                rcases List.mem_append.mp hc with hr | hr
                · exact rest_chains c hr
                · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
              · intro h_empty
                have := congrArg List.length h_empty
                simp [List.length_append] at this
            · refine ih A' (rest_cfgs ++ [⟨qNew, tape.write w'⟩,
                SingleTapeTM.initCfg tm w_in]) ?_ hA'_len ?_ hMem' hStart
              · intro c hc
                rcases List.mem_append.mp hc with hr | hr
                · exact rest_chains c hr
                · rcases List.mem_cons.mp hr with rfl | hr2
                  · exact new_chain'
                  · rw [List.mem_singleton] at hr2; subst hr2
                    exact Relation.ReflTransGen.refl
              · intro h_empty
                have := congrArg List.length h_empty
                simp [List.length_append] at this
          | some dir =>
            cases dir with
            | right =>
              cases h_right : tape.right.toList with
              | nil =>
                cases qNew with
                | none =>
                  refine ⟨(tape.write w').moveRight, ?_⟩
                  refine chain_cfg.tail ?_
                  show tm.step cfg = some _
                  rw [hcfg, ← tm_step_running]
                  congr 1
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                | some qNew_q =>
                  obtain ⟨A', hLen', hMem', hτ1⟩ :=
                    starts_with_stepTilesRightBoundary_weak_ext tm w_in q tape
                      qNew_q w' h_tr h_right (Or.inl h_w_ne) rest_cfgs A h_mem hMatch''
                  have hA'_len : A'.length ≤ n := by omega
                  have h_stepRes :
                      stepResult tm q tape =
                        ⟨some qNew_q, (tape.write w').moveRight⟩ := by
                    simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                  have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                      (SingleTapeTM.initCfg tm w_in)
                      ⟨some qNew_q, (tape.write w').moveRight⟩ := by
                    rw [← h_stepRes]; exact new_chain_step
                  refine ih A' (rest_cfgs ++ [⟨some qNew_q,
                    (tape.write w').moveRight⟩]) ?_ hA'_len ?_ hMem' hτ1
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
              | cons _ _ =>
                have h_right_ne : tape.right.toList ≠ [] := by
                  rw [h_right]; exact List.cons_ne_nil _ _
                obtain ⟨A', hLen', hMem', hτ1Disj⟩ :=
                  starts_with_stepTilesRightInterior_weak_ext tm w_in q tape
                    qNew w' h_tr h_right_ne (Or.inl h_w_ne) rest_cfgs A h_mem hMatch''
                have hA'_len : A'.length ≤ n := by omega
                have h_stepRes :
                    stepResult tm q tape = ⟨qNew, (tape.write w').moveRight⟩ := by
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                    (SingleTapeTM.initCfg tm w_in)
                    ⟨qNew, (tape.write w').moveRight⟩ := by
                  rw [← h_stepRes]; exact new_chain_step
                rcases hτ1Disj with hSep | hStart
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').moveRight⟩])
                    ?_ hA'_len ?_ hMem' hSep
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').moveRight⟩,
                    SingleTapeTM.initCfg tm w_in]) ?_ hA'_len ?_ hMem' hStart
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rcases List.mem_cons.mp hr with rfl | hr2
                      · exact new_chain'
                      · rw [List.mem_singleton] at hr2; subst hr2
                        exact Relation.ReflTransGen.refl
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
            | left =>
              cases h_left : tape.left.toList with
              | nil =>
                exfalso
                have h_no_lb := h_nlb cfg chain_cfg q tape hcfg h_left
                apply h_no_lb
                rw [h_tr]
              | cons _ _ =>
                have h_left_ne : tape.left.toList ≠ [] := by
                  rw [h_left]; exact List.cons_ne_nil _ _
                obtain ⟨A', hLen', hMem', hτ1Disj⟩ :=
                  starts_with_stepTilesLeftInterior_weak_ext tm w_in q tape
                    qNew w' h_tr h_left_ne (Or.inl h_w_ne) rest_cfgs A h_mem hMatch''
                have hA'_len : A'.length ≤ n := by omega
                have h_stepRes :
                    stepResult tm q tape = ⟨qNew, (tape.write w').moveLeft⟩ := by
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                    (SingleTapeTM.initCfg tm w_in)
                    ⟨qNew, (tape.write w').moveLeft⟩ := by
                  rw [← h_stepRes]; exact new_chain_step
                rcases hτ1Disj with hSep | hStart
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').moveLeft⟩])
                    ?_ hA'_len ?_ hMem' hSep
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').moveLeft⟩,
                    SingleTapeTM.initCfg tm w_in]) ?_ hA'_len ?_ hMem' hStart
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rcases List.mem_cons.mp hr with rfl | hr2
                      · exact new_chain'
                      · rw [List.mem_singleton] at hr2; subst hr2
                        exact Relation.ReflTransGen.refl
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this

/-- From an MPCP solution, we may recover `Halts tm w`. -/
theorem halt_if_mHasSolution (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol) (h_nlb : NoLeftBoundary tm w) [Encodable Symbol] [Encodable tm.State]
    (h : MPCP.DecisionProblem (startTile tm w) (haltTiles tm)) :
    Halts tm w := by
  obtain ⟨A, h_mem, h_match⟩ := h
  have h_match_cfg :
      τ1 A = encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ τ2 A := by
    have h_step : # :: τ1 A =
        # :: (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ τ2 A) := by
      have h_lhs : (startTile tm w).top ++ τ1 A = # :: τ1 A := by simp [startTile_top]
      have h_rhs : (startTile tm w).bot ++ τ2 A =
          # :: (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ τ2 A) := by
        simp [startTile_bot, List.append_assoc]
      rw [h_lhs, h_rhs] at h_match; exact h_match
    exact (List.cons.injEq _ _ _ _ |>.mp h_step).2
  by_cases h_strong : ∀ s ∈ A, s ∈ haltTiles tm
  · obtain ⟨tape, h_trace⟩ :=
      backward_aux tm h_nbw w h_nlb A.length A (SingleTapeTM.initCfg tm w)
        (le_refl _) Relation.ReflTransGen.refl h_strong h_match_cfg
    exact ⟨tape, h_trace⟩
  · have h_match_queue :
        τ1 A = queueEncoding tm [SingleTapeTM.initCfg tm w] ++ τ2 A := by
      rw [h_match_cfg]; simp [queueEncoding, List.append_assoc]
    exact backward_aux_weak tm h_nbw w h_nlb A.length A
      [SingleTapeTM.initCfg tm w]
      (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact Relation.ReflTransGen.refl)
      (le_refl _) (List.cons_ne_nil _ _) h_mem h_match_queue

/-- Halt reduces many-one to MPCP: `tm` halts on `w` iff the reduced MPCP instance has a solution,
subject to `NoBlankWrites tm` and `NoLeftBoundary tm w`. -/

theorem halt_iff_mpcp (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol) (h_nlb : NoLeftBoundary tm w) [Encodable Symbol] [Encodable tm.State]:
    Halts tm w ↔ MPCP.DecisionProblem (startTile tm w) (haltTiles tm) :=
    by
    apply Iff.intro
    · intro h
      apply mHasSolution_if_halt
      exact h_nbw
      exact h_nlb
      exact h
    · intro hd
      apply halt_if_mHasSolution
      exact h_nbw
      exact h_nlb
      exact hd

end DiagonaLean.MPCP.Reduction
