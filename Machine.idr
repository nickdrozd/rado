module Machine

import Program
import public Tape

%default total

public export
interface Tape t => Machine t where
  exec : Program -> State -> t -> (State, t)
  exec prog state tape =
    let (color, dir, nextState) = prog state $ read tape in
      (nextState, shift dir $ print color tape)

  partial
  runToHalt : Nat -> Program -> State -> t -> (Nat, t)
  runToHalt count prog state tape =
    let (nextState, nextTape) = exec prog state tape in
      case nextState of
        H => (count, nextTape)
        _ => runToHalt (S count) prog nextState nextTape

  partial
  runOnBlankTape : Program -> (Nat, t)
  runOnBlankTape prog = runToHalt 1 prog A (the t blank)

public export
[MicroMachine] Machine MicroTape where

public export
[MacroMachine] Machine MacroTape where
