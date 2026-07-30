import Cslib.Computability.Machines.Turing.SingleTape.NonDeterministic
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
import Cslib.Computability.Automata.NA.Basic

-- ## File overview:
-- used for testing definitions and writing down ideas. Essentially a scratchpad.

-- How does a non-deterministic TM work?

/-
  A non deterministic turing machine branches out and can do multiple operations at the same time.
  In a non deterministic turing machine, instead of having a transition function we have a transition relation.
  In a deterministic turing machine, for each corresponding state and input, theres a unique output state and action, whereas in a non deterministic turing machine, for each corresponding state and input, there can be multiple output states and actions.
  So, in a non deterministic turing machine, corresponding to a state and input, there can be multiple transitions possible and if it halts in any of those branches, then the machine halts.
  In a deterministic turing machine, we have none as the halting state.
-/

-- Breakdown of turing machines definition

/-
  The definitions have TrLabel which are just actions over that Symbol. The actions are read x, write y, move d: Turing.Dir and skip
  Note, here Turing.Dir comes from Mathlib.Computability.TuringMachine where Dir is defined as an inductive type with two constructors: left and right.
  The Bitape Structure is the defined with head : Option Symbol(Whatever you're reading), left : Stacktape Symbol, right : Stacktape Symbol. stacktape is just a list of symbols ig, nothing more should be needed.
  TrLabel.applyToTape gives the smeantics of the TrLabel constructors. It takes μ and otape as option Turing.BiTape Symbol and returns a new option Turing.BiTape Symbol.
  `read x, some tape => if x = tape.head then some tape else none`, implcying that the action on the tape after reading is nothing.
  `write x, some tape => some (tape.write x)` applying the action of writing x to the tape.
  `move d, some tape => some (tape.move d)` applying the action of moving the tape in direction d.
  `skip, some tape => some tape` applying the action of skipping to the tape.
  `_, _ => none` concludes the rest case.
  Having option type makes the function composable.
  Cfg is the configuration of the turing machine which is defined as a structure, that takes in input State and Symbol. The structure has a state : State and a tape : Turing.BiTape Symbol.
  An instance of this structure is a snapshot of the tm. The default constructor used is Cfg.mk₁ which inputs s:State and xs: List Symbol and basically constructs a BiTape with head as the first element of the list and left as []. How generally Turing Machines have.
-/

-- Breakdown of NTMs

/-
  NTMs extend the definition of NAs. NA(Non deterministic Automaton) is extends LTS which is a labelled transition system.
  `structure LTS (State Symbol : Type*) where \n step : State → Symbol → Set State`. NA's just extend LTS with a set of Start States.
  The reason to use set and not list is to avoid duplicates and unnecessary segregation based on order. Set theory by default has a none type which is the empty set, as there is no where to transition to.
  There are no accept conditions in LTS and NA, but in another structure FinAcc(used to recognise languages) extending NA with `accept : Set State` .
  A singleTapeNTM extends NA with the accept state(could have used FinAcc) and a proof that all accepting states are halting states.?
  Note, that Configuration is a snapshot of the states, so it's just current state and the tape.
  Yields is a proposition that there exists a transition that connects two configurations. yields_tr is a theorem equating the definition useful for automation.
  MYields makes the Yields relation transitive and reflexive. Basically, making sure we have a transition that composes.
-/
open Cslib.Computability.Turing.SingleTape Cslib.Automata

#check TrLabel Nat

#check Cfg Nat

#check NA Nat Nat

/-- error: Unknown identifier `LTS` -/
#guard_msgs in
#check LTS

#check SingleTapeNTM.Yields

#check SingleTapeNTM Nat Nat

open Cslib.Turing

variable {State Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

/-- A function that produces a singleTapeTM from an NTM on the same alphabet. -/
def ntm_to_dtm (ntm : SingleTapeNTM State Symbol) : SingleTapeTM Symbol := sorry

/-- Bridging lemma connecting the Acceptance condition of an NTM and its produced singleTapeTM. -/
lemma ntm_to_dtm_correct (ntm : SingleTapeNTM State Symbol) (xs : List Symbol) :
  Acceptor.Accepts ntm xs ↔ ∃ ys, (ntm_to_dtm ntm).Outputs xs ys := sorry
