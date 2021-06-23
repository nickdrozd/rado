module Machine

import Program
import public Tape

%default total

public export
interface Tape tape => Machine tape where
  exec : Program -> State -> tape -> Nat -> (State, tape, Nat)
  exec prog state tape count =
    let
      scan = read tape
      (cx, dir, nextState) = prog state scan
      printed = print cx tape
      skip = if state /= nextState then Nothing else Just (scan, cx)
      (steps, shifted) = shift dir printed skip
    in
      (nextState, shifted, steps + count)

  partial
  run : Program -> State -> tape -> Nat -> (Nat, tape)
  run prog state tape count =
    let (nextState, nextTape, nextCount) = exec prog state tape count in
      case nextState of
        H => (count, nextTape)
        _ => run prog nextState nextTape nextCount

  partial
  runOnBlankTape : Program -> (Nat, tape)
  runOnBlankTape prog = run prog A (the tape blank) 1

public export
[MicroMachine] Machine MicroTape where

public export
[MacroMachine] Machine MacroTape where
