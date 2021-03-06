module Parse

import Data.List
import Data.Vect
import Data.String

import Program

[ShowAction] Show Action where
  show (color, shift, state) =
    show color ++ show shift ++ show state

-- show @{ShowAction} $ bb4 A 0

----------------------------------------

-- λΠ> runOnBlankTape BB2
-- (6, MkDPair 3 ([1, 1, 1, 1], FS (FS FZ)))

----------------------------------------

-- For parse format, see http://www.logique.jussieu.fr/~michel/ha.html

parseColor : Char -> Maybe Color
parseColor '0' = Just 0
parseColor '1' = Just 1
parseColor _   = Nothing

parseShift : Char -> Maybe Shift
parseShift 'L' = Just L
parseShift 'R' = Just R
parseShift _   = Nothing

parseState : Char -> Maybe State
parseState 'H' = Just H
parseState 'A' = Just A
parseState 'B' = Just B
parseState 'C' = Just C
parseState 'D' = Just D
parseState 'E' = Just E
parseState 'F' = Just F
parseState _   = Nothing

parseAction : String -> Maybe Action
parseAction action =
  let actionIndex = assert_total $ strIndex action in do
    color <- parseColor $ actionIndex 0
    shift <- parseShift $ actionIndex 1
    state <- parseState $ actionIndex 2
    Just (color, shift, state)

-- n is 2; needs to be changed for more colors
public export
BWAction : Type
BWAction = Vect 2 Action

pairUp : List ty -> Maybe (List (Vect 2 ty))
pairUp [ ] = Just []
pairUp [_] = Nothing
pairUp (x1 :: x2 :: xs) = do
  rest <- pairUp xs
  Just $ [x1, x2] :: rest

partwayParse : String -> Maybe (List BWAction)
partwayParse input = pairUp $ mapMaybe parseAction $ words input

----------------------------------------

export
Cast State (Fin 1) where
  cast A = FZ
  cast _  = FZ

export
Cast State (Fin 2) where
  cast B = FS FZ
  cast x  = weaken $ cast x

export
Cast State (Fin 3) where
  cast C = FS $ FS FZ
  cast x  = weaken $ cast x

export
Cast State (Fin 4) where
  cast D = FS $ FS $ FS FZ
  cast x  = weaken $ cast x

export
Cast State (Fin 5) where
  cast E = FS $ FS $ FS $ FS FZ
  cast x  = weaken $ cast x

export
Cast State (Fin 6) where
  cast F = FS $ FS $ FS $ FS $ FS FZ
  cast x  = weaken $ cast x

export
Cast BWAction Instruction where
  cast [w, b] color =
    case color of
      0 => w
      1 => b
      _  => b

export
makeProgram : (Cast State $ Fin n) => (Vect n BWAction) -> Program
makeProgram actions state = cast $ index (cast state) actions

----------------------------------------

bb3input : String
bb3input = "1RB   1RH   1LB   0RC   1LC   1LA"

bb3parsed : Maybe (List BWAction)
bb3parsed = partwayParse bb3input

----------------------------------------

bb4input : String
bb4input = "1RB   1LB   1LA   0LC   1RH   1LD   1RD   0RA"

bb4parsed : Maybe (List BWAction)
bb4parsed = partwayParse bb4input

----------------------------------------

tm5parse : Maybe $ List BWAction
tm5parse = partwayParse
  "1RB   0LC   1RC   1RD   1LA   0RB   0RE   1RH   1LC   1RA"

bb5parse : Maybe $ List BWAction
bb5parse = partwayParse
  "1RB   1LC   1RC   1RB   1RD   0LE   1LA   1LD   1RH   0LA"
