/-
  Proof Sketch:
  Follow the Hopcroft proof closely, and simply just ask them for a function that converts the NTM to a TM.
-/

import DiagonaLean.Rice.Basic
import DiagonaLean.Synthetic.ReductionChain
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Halt.Encoding

import Cslib.Computability.Machines.Turing.SingleTape.NonDeterministic

open DiagonaLean.Rice DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.ReductionChain DiagonaLean.Halt.Encoding DiagonaLean.Halt Cslib.Turing Cslib.Automata
open Cslib.Computability.Turing.SingleTape

namespace DiagonaLean.Rice.Constructive

/-! ## Part 1: The honest NTM for NonEmptyLanguage

The NTM works in two phases on input `w` (an encoded TM `M_w`):

1. **Guessing phase** (`.guessing`): Nondeterministically guess a witness string `x`
   by repeatedly choosing to either write another guessed symbol and stay in `.guessing`,
   or stop guessing and transition to `.simulating`.

2. **Simulation phase** (`.simulating`): Simulate the universal TM on `(M_w, x)`.
   If the simulation reaches an accepting state, accept.

The nondeterminism is *real* — from `.guessing` there are genuinely two outgoing
transitions on every symbol, which is exactly the "guess a witness" step the whole
construction depends on.
-/

/-- States of the NonEmptyLang NTM:
1. `.skippingInput` / `.skippingInput_step`: scanning right past the input symbols without writing.
2. `.guessing`: nondeterministically guessing the candidate witness `x`.
3. `.rewinding` / `.rewinding_step` / `.rewound`: rewinding the tape head back to position 0.
4. `.simulating q`: running the universal simulator on `(M_w, x)` from position 0. -/
inductive NELState (UState : Type) where
  /-- Moving right past non-blank input symbols. -/
  | skippingInput : NELState UState
  | skippingInput_step : NELState UState
  /-- Nondeterministically guessing the candidate witness. -/
  | guessing : NELState UState
  /-- Moving left back to position 0 before starting simulation. -/
  | rewinding : NELState UState
  | rewinding_step : NELState UState
  | rewound : NELState UState
  /-- Running the universal simulator. -/
  | simulating : UState → NELState UState
deriving DecidableEq

/-! ### Universal TM interface

We postulate the existence of a universal TM that can simulate any encoded Boolean TM.
The exact construction (parsing the encoding, simulating step-by-step) is a standard
but lengthy result. We axiomatize its interface here.

**Key design point**: The correctness axiom `uSimulates` is stated in terms of
`Acceptor.Accepts universalNTM (encodeBoolTM M ++ w)`, which expands to:
  `∃ s ∈ start, ∃ c', c'.state ∈ accept ∧ MYields (Cfg.mk₁ s (encodeBoolTM M ++ w)) c'`
This threads `M` and `w` through the **tape** in the initial configuration `Cfg.mk₁`,
so the RHS genuinely depends on both `M` and `w`. This is in contrast to bare-state
reachability (`LTS.CanReach`), which would ignore the tape and produce a closed
proposition independent of `M` and `w`, leading to inconsistency. -/

/-- A universal simulator state type. Abstractly, the universal TM needs to track
the simulated machine's state, the simulated tape, and a program counter for
its own control logic. We leave the type abstract. -/
axiom UState : Type

/-- The transition relation of the universal simulator, operating on `TrLabel Bool`.
Each transition reads/writes/moves on the tape — the tape content is what distinguishes
different encoded machines and inputs. The `TrLabel` carries read/write/move/skip
operations that interact with the tape through `Yields`/`applyToTape`. -/
axiom uTr : UState → TrLabel Bool → UState → Prop

/-- The initial state of the universal simulator. -/
axiom uState₀ : UState

/-- The set of accepting states of the universal simulator. -/
axiom uAcceptStates : Set UState

/-- Accepting states of the universal simulator are halting (no outgoing transitions). -/
axiom uAccept_halting : ∀ s, s ∈ uAcceptStates → ¬∃ μ s', uTr s μ s'

/-- The universal simulator bundled as a proper `SingleTapeNTM`.
This lets us use the standard `Acceptor.Accepts`, `MYields`, `Yields` vocabulary,
which all operate on full configurations (`Cfg` = state + tape), not bare states. -/
def universalNTM : SingleTapeNTM UState Bool where
  Tr := uTr
  start := {uState₀}
  accept := uAcceptStates
  accept_halting := by
    intro s hmem
    exact uAccept_halting s hmem

/-- Correctness of the universal simulator.

`Acceptor.Accepts universalNTM (encodeBoolTM M ++ w)` expands to:
  `∃ s ∈ {uState₀}, ∃ c', c'.state ∈ uAcceptStates ∧`
  `  universalNTM.MYields (Cfg.mk₁ s (encodeBoolTM M ++ w)) c'`

The initial configuration `Cfg.mk₁ uState₀ (encodeBoolTM M ++ w)` has:
- state = `uState₀`
- tape = `BiTape.mk₁ (encodeBoolTM M ++ w)` (encoding of M followed by input w)

`MYields` is `ReflTransGen Yields`, where each `Yields` step is:
  `∃ μ, uTr c.state μ c'.state ∧ μ.applyToTape c.tape = c'.tape`

So `uTr` reads/writes/moves on the tape at each step, and the tape content
(which encodes `M` and `w`) determines the computation. Different `M` and `w`
produce different initial tapes, hence different computations. -/
axiom uSimulates (M : SingleTapeTM Bool) [DecidableEq M.State] (w : List Bool) :
  Accepts M w ↔ Acceptor.Accepts universalNTM (encodeBoolTM M ++ w)

/-- The transition relation for the NonEmptyLang NTM.

This machine is **completely independent of `M`**. It operates in 4 phases:

Phase 1 (`.skippingInput`):
  Scans right over `encodeBoolTM M` using `read b → move right`.
  Reads do not alter the tape. `skip` transitions to `.guessing` once past input.

Phase 2 (`.guessing`):
  Nondeterministically writes witness bits `w` using `write b → move right`.
  `skip` transitions to `.rewinding`.

Phase 3 (`.rewinding`):
  Scans left back to position 0 using `read b → move left`.
  When hitting the left blank space (`none`), `read` fails, `skip` transitions to `.rewound`,
  and `move right` steps back onto index 0 before entering `.simulating uState₀`.

Phase 4 (`.simulating q`):
  Follows universal simulator transitions `uTr` from position 0 on tape `encodeBoolTM M ++ w`. -/
inductive NTM_NonEmptyLang_Tr : NELState UState → TrLabel Bool → NELState UState → Prop where
  -- Phase 1: Skipping input (scan right over non-blank symbols without writing)
  | skip_read_false : NTM_NonEmptyLang_Tr .skippingInput (.read false) .skippingInput_step
  | skip_read_true  : NTM_NonEmptyLang_Tr .skippingInput (.read true)  .skippingInput_step
  | skip_move_right : NTM_NonEmptyLang_Tr .skippingInput_step (.move .right) .skippingInput
  | skip_done       : NTM_NonEmptyLang_Tr .skippingInput .skip .guessing

  -- Phase 2: Guessing witness (write bits and move right)
  | guess_false      : NTM_NonEmptyLang_Tr .guessing (.write false) .guessing
  | guess_true       : NTM_NonEmptyLang_Tr .guessing (.write true)  .guessing
  | guess_move_right : NTM_NonEmptyLang_Tr .guessing (.move .right) .guessing
  | start_rewind     : NTM_NonEmptyLang_Tr .guessing .skip .rewinding

  -- Phase 3: Rewinding to head position 0 (scan left over non-blank symbols)
  | rewind_read_false : NTM_NonEmptyLang_Tr .rewinding (.read false) .rewinding_step
  | rewind_read_true  : NTM_NonEmptyLang_Tr .rewinding (.read true)  .rewinding_step
  | rewind_move_left  : NTM_NonEmptyLang_Tr .rewinding_step (.move .left) .rewinding
  | rewind_done       : NTM_NonEmptyLang_Tr .rewinding .skip .rewound
  | rewind_step_back  : NTM_NonEmptyLang_Tr .rewound (.move .right) (.simulating uState₀)

  -- Phase 4: Universal simulation
  | sim_step (q q' : UState) (μ : TrLabel Bool) :
      uTr q μ q' → NTM_NonEmptyLang_Tr (.simulating q) μ (.simulating q')

/-- The single, fixed NonEmptyLang NTM.
It is **independent of `M`** — it reads `M`'s encoding off the tape, guesses `x`,
rewinds the head back to position 0, and simulates `universalNTM`. -/
def NTM_NonEmptyLang : SingleTapeNTM (NELState UState) Bool where
  Tr := NTM_NonEmptyLang_Tr
  start := {.skippingInput}
  accept := { s | ∃ q, s = .simulating q ∧ q ∈ uAcceptStates }
  accept_halting := by
    intro s hmem
    obtain ⟨q, rfl, hq⟩ := hmem
    rintro ⟨μ, s', htr⟩
    cases htr with
    | sim_step q q' μ hutr =>
      exact uAccept_halting q hq ⟨μ, q', hutr⟩

/-! ## Part 2: Correctness of the NTM

The NTM accepts `encodeBoolTM M` iff `∃ w, Accepts M w`, i.e., iff `isNonEmptyLang M`.
Both directions require reasoning about the 4-phase execution:

- **Forward**: An accepting run witnesses a skipping phase (preserves input),
  a guessing phase (writes `w`), a rewinding phase (returns head to 0),
  and a simulation phase reaching an accepting state. By `uSimulates`, `M` accepts `w`.

- **Backward**: Given `w` such that `Accepts M w`, build the accepting run by scanning past
  `encodeBoolTM M`, guessing `w`, rewinding to 0, and executing `universalNTM`. -/

theorem ntm_accepts_iff (M : SingleTapeTM Bool) [DecidableEq M.State] :
    Acceptor.Accepts NTM_NonEmptyLang (encodeBoolTM M) ↔ ∃ w, Accepts M w := by
  constructor
  · -- Forward: extract guessed witness from accepting run
    rintro ⟨s, hs, c', hc'_acc, hrun⟩
    -- s ∈ start = {.skippingInput}
    -- c'.state ∈ accept, so c'.state = .simulating q for some q ∈ uAcceptStates
    -- The run decomposes into:
    -- 1. Skipping phase: moves right past encodeBoolTM M using read (leaves input intact)
    -- 2. Guessing phase: writes witness w past encodeBoolTM M
    -- 3. Rewinding phase: moves left back to position 0
    -- 4. Simulation phase: starts at position 0 of (encodeBoolTM M ++ w), accepts iff Accepts M w
    sorry
  · -- Backward: build accepting run from witness
    rintro ⟨w, hw⟩
    -- Scan past encodeBoolTM M (skip_read_* + skip_move_right)
    -- Transition to .guessing (skip_done)
    -- Guess w symbol by symbol (guess_false/guess_true + guess_move_right)
    -- Transition to .rewinding (start_rewind)
    -- Rewind left back to position 0 (rewind_read_* + rewind_move_left + rewind_done + rewind_step_back)
    -- Enter .simulating uState₀ at position 0 and apply uSimulates
    sorry

/-! ## Part 3: NTM to DTM conversion via BFS/dovetailing

An NTM's nondeterministic tree can be infinitely deep with unboundedly many branches.
The standard fix (Sipser, "dovetailing"/BFS over the choice tree) is:

Since at each configuration the NTM has only finitely many nondeterministic choices
(bounded by the branching factor of `Tr`), enumerate all finite sequences of choices
in order of increasing length, breadth-first, and accept as soon as any explored
configuration is accepting.

The DTM **only recognizes** the language (semi-decides it) — it need not halt on
rejecting input, since it BFS-searches forever if no branch ever accepts.

Note: The BFS state (depth counter, path index) is encoded on the *tape*, not in the
finite state type. The DTM's finite state type tracks only which phase of the
BFS cycle we are in (e.g., incrementing the counter, rewinding, replaying a branch,
checking acceptance). The unbounded counters live on the tape as unary or binary
numbers. This is the standard approach from Sipser Ch. 3. -/

variable {State Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

/-- A finite sequence of nondeterministic choices, encoding one branch
of the NTM's computation tree. Each `Nat` picks which successor to
explore at that step (indexing into the finite set of transitions). -/
abbrev ChoicePath := List Nat

/-- The phases of the BFS-dovetailing DTM's finite control.
The unbounded BFS counters (depth, path index) are stored on the tape. -/
inductive BFSPhase where
  | incrementCounter  -- Advance to the next choice path / depth
  | rewindInput       -- Rewind the tape head to the start of the input
  | replayBranch      -- Simulate the NTM along the current choice path
  | checkAcceptance   -- Check if the current branch reached an accepting state
deriving DecidableEq

instance : Fintype BFSPhase where
  elems := {.incrementCounter, .rewindInput, .replayBranch, .checkAcceptance}
  complete := by intro x; cases x <;> simp

/-- Deterministically replay an NTM along a fixed sequence of choices for
a given number of steps, returning `none` if the path is invalid or
the chosen branch index exceeds the available transitions. -/
def replay (ntm : SingleTapeNTM State Symbol)
    (startState : State) (tape : BiTape Symbol)
    (path : ChoicePath) : Option (Cfg State Symbol) :=
  sorry -- fold over `path`, at each step picking branch `path[i]` out of
        -- the (finite) set `{(μ, s') // ntm.Tr s μ s'}`
        -- applying μ to the tape and continuing with s'

/-- The DTM that BFS-dovetails over the NTM's computation tree.
On input `xs`, it breadth-first searches over increasing depth `n`
and all choice paths of length `n`; accepts if any reachable state is
in `ntm.accept`.

The finite state type `BFSPhase` tracks which phase of the BFS cycle
we are in. The unbounded BFS counters (depth, path index) and a copy
of the NTM's current configuration are encoded on the tape. -/
def ntm_to_dtm (ntm : SingleTapeNTM State Symbol) : SingleTapeTM Symbol where
  State := BFSPhase
  q₀ := .incrementCounter
  tr := fun _phase _head =>
    -- At each phase:
    -- .incrementCounter: advance the tape-encoded path index (or bump depth)
    -- .rewindInput: rewind the head to the start of the original input
    -- .replayBranch: simulate one step of the NTM along the current choice path
    -- .checkAcceptance: if accepting state reached, halt; otherwise go to .incrementCounter
    -- The exact encoding is complex but standard (Sipser Ch. 3).
    sorry

/-- Correctness of the NTM→DTM conversion: the DTM accepts exactly the same
language as the NTM. The DTM semi-decides the language by BFS exploration. -/
theorem ntm_to_dtm_correct (ntm : SingleTapeNTM State Symbol) (xs : List Symbol) :
    Acceptor.Accepts ntm xs ↔ ∃ ys, (ntm_to_dtm ntm).Outputs xs ys := by
  sorry

/-! ## Part 4: Putting it all together -/

-- The SINGLE fixed DTM for NonEmptyLanguage (completely independent of M!)
noncomputable def DTM_NonEmptyLang : SingleTapeTM Bool :=
  ntm_to_dtm NTM_NonEmptyLang

-- The constructive proof that NonEmptyLanguage is RE (i.e. recognized by a single DTM)
theorem NonEmptyLang_RE_constructive (M : SingleTapeTM Bool) [DecidableEq M.State] :
    isNonEmptyLang M ↔ ∃ ys, DTM_NonEmptyLang.Outputs (encodeBoolTM M) ys := by
  -- isNonEmptyLang M is defined as `∃ w, Accepts M w`
  -- Which is equivalent to NTM_NonEmptyLang accepting `encodeBoolTM M`
  dsimp [isNonEmptyLang]
  rw [← ntm_accepts_iff M]
  -- And by the correctness of NTM to DTM conversion, this is equivalent to
  -- DTM_NonEmptyLang outputting something on `encodeBoolTM M`.
  have h := ntm_to_dtm_correct NTM_NonEmptyLang (encodeBoolTM M)
  exact h

end DiagonaLean.Rice.Constructive
