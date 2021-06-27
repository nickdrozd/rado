module Parse

import Data.List
import Data.Vect
import Data.String

import Program

%default total

parseColor : Char -> Color
parseColor '0' = 0
parseColor '1' = 1
parseColor '2' = 2
parseColor '3' = 3
parseColor _   = 0

parseShift : Char -> Shift
parseShift 'L' = L
parseShift 'R' = R
parseShift _   = L

parseState : Char -> State
parseState 'H' = H
parseState 'A' = A
parseState 'B' = B
parseState 'C' = C
parseState 'D' = D
parseState 'E' = E
parseState 'F' = F
parseState _   = H

parseAction : String -> Action
parseAction action =
  let actionIndex = assert_total $ strIndex action in do
    let color = parseColor $ actionIndex 0
    let shift = parseShift $ actionIndex 1
    let state = parseState $ actionIndex 2

    (color, shift, state)

public export
parseProgram : String -> IO (Maybe Program)
parseProgram prog = do
  let actions = map parseAction $ words prog

  case actions of
    [a0, a1, a2, a3, b0, b1, b2, b3] =>
      pure $ Just $ makeProgram a0 a1 a2 a3 b0 b1 b2 b3
    _ => pure Nothing
  where
  makeProgram : Action -> Action -> Action -> Action ->
                Action -> Action -> Action -> Action ->
                Program
  makeProgram a0 _  _  _  _  _  _  _  A 0 = a0
  makeProgram _  a1 _  _  _  _  _  _  A 1 = a1
  makeProgram _  _  a2 _  _  _  _  _  A 2 = a2
  makeProgram _  _  _  a3 _  _  _  _  A 3 = a3
  makeProgram _  _  _  _  b0 _  _  _  B 0 = b0
  makeProgram _  _  _  _  _  b1 _  _  B 1 = b1
  makeProgram _  _  _  _  _  _  b2 _  B 2 = b2
  makeProgram _  _  _  _  _  _  _  b3 B 3 = b3
  makeProgram _  _  _  _  _  _  _  _  _ c = (c, R, H)
