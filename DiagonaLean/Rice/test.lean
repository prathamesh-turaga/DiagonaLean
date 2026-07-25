import Cslib.Computability.Machines.Turing.SingleTape.NonDeterministic

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

--

/-

-/
open Cslib.Computability.Turing.SingleTape

#check TrLabel Nat

#check Cfg Nat
