module Tape

import Data.List

import Program

%default total

public export
interface Tape tape where
  cells : tape -> Nat
  marks : tape -> Nat

  blank : tape

  read  :          tape -> Color
  print : Color -> tape -> tape

  shift : Shift -> tape -> Maybe Color -> (Nat, tape)
  shift L =  left
  shift R = right

  left  :          tape -> Maybe Color -> (Nat, tape)
  right :          tape -> Maybe Color -> (Nat, tape)

public export
Tape tape => Show tape where
  show tape = show (cells tape, marks tape)

----------------------------------------

TapeSpan : Type
TapeSpan = List Color

public export
MicroTape : Type
MicroTape = (TapeSpan, Color, TapeSpan)

pullNextSquare : TapeSpan -> (Color, TapeSpan)
pullNextSquare [] = (0, [])
pullNextSquare (x :: xs) = (x, xs)

pushCurrSquare : Color -> TapeSpan -> TapeSpan
pushCurrSquare = (::)

public export
Tape MicroTape where
  cells (l, _, r) = length l + 1 + length r

  marks (l, c, r) = length $ filter (/= 0) $ l ++ [c] ++ r

  blank = ([], 0, [])

  read (_, c, _) = c

  left (l, c, r) _ =
    let (x, k) = pullNextSquare l in
      (1, (k, x, pushCurrSquare c r))

  right (l, c, r) skip =
    let (s, (k, x, e)) = left (r, c, l) skip in
      (s, (e, x, k))

  print cx (l, _, r) = (l, cx, r)

----------------------------------------

Block : Type
Block = (Color, Nat)

BlockSpan : Type
BlockSpan = List Block

public export
MacroTape : Type
MacroTape = (BlockSpan, Color, BlockSpan)

pullNextBlock : BlockSpan -> (Color, BlockSpan)
pullNextBlock [] = (0, [])
pullNextBlock ((c, n) :: xs) =
  (c, case n of
    0       => xs
    1       => xs
    S $ S k => (c, S k) :: xs)

pushCurrBlock : Block -> BlockSpan -> BlockSpan
pushCurrBlock block [] = [block]
pushCurrBlock block@(c, k) ((q, n) :: xs) =
  if c == q
    then (q, k + n) :: xs
    else block :: (q, n) :: xs

public export
Tape MacroTape where
  cells (l, _, r) =
    S $ foldl (\a, (_, n) => a + n) 0 $ l ++ r

  marks (l, c, r) =
    (+) (if c == 0 then 0 else 1) $
        foldl (\a, (q, n) =>
                   (+) a $ if q == 0 then 0 else n)
              0
              (l ++ r)

  blank = ([], 0, [])

  read (_, c, _) = c

  print cx (l, _, r) = (l, cx, r)

  left tape@(((bc, bn) :: l), c, r) (Just cx) =
    if bc /= c then assert_total $ left (print cx tape) Nothing else
      let (x, k) = pullNextBlock l in
        (1 + bn, (k, x, pushCurrBlock (cx, 1 + bn) r))

  left tape@([], _, _) (Just cx) =
    assert_total $ left (print cx tape) Nothing

  left (l, c, r) Nothing =
    let (x, k) = pullNextBlock l in
      (1, (k, x, pushCurrBlock (c, 1) r))

  right (l, c, r) skip =
    let (s, (k, x, e)) = left (r, c, l) skip in
      (s, (e, x, k))
