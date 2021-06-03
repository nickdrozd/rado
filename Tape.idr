module Tape

import Data.Nat
import public Data.Vect

import Program

%default total

public export
interface Tape tape where
  cells : tape -> Nat
  marks : tape -> Nat

  blank : tape

  read  :          tape -> Color
  print : Color -> tape -> tape

  shift : Shift -> tape -> tape
  shift L tape =  left tape
  shift R tape = right tape

  left  :          tape -> tape
  right :          tape -> tape

public export
Tape tape => Show tape where
  show tape = show (cells tape, marks tape)

----------------------------------------

public export
MicroTape : Type
MicroTape = (i : Nat ** (Fin (S i), Vect (S i) Color))

public export
Tape MicroTape where
  cells (_ ** (_, tape))  = length tape
  marks (_ ** (_, tape)) = let (n ** _) = filter ((/=) 0) tape in n

  blank = (Z ** (FZ, [0]))

  read (_ ** (pos, tape)) =
    index pos tape

  print color (i ** (pos, tape)) =
    (i ** (pos, replaceAt pos color tape))

  left (i ** (FZ,   tape)) = (S i ** (FZ, [0] ++ tape))
  left (i ** (FS p, tape)) = (  i ** ( weaken p, tape))

  right (i ** (pos, tape)) =
    case strengthen pos of
      Right p => (  i ** (FS p, tape))
      Left  _ =>
        let prf = sym $ plusCommutative i 1 in
          (S i ** (FS pos, rewrite prf in tape ++ [0]))

----------------------------------------

MacroBlock : Type
MacroBlock = (Color, (j : Nat ** Fin (S j)))

data SplitBlock
  = NoChange
  | Replaced MacroBlock
  | SplitBeg MacroBlock MacroBlock
  | SplitMid MacroBlock MacroBlock MacroBlock
  | SplitEnd MacroBlock MacroBlock

splitPrint : Color -> MacroBlock -> SplitBlock
splitPrint cx (c0, coord) =
  if c0 == cx then NoChange else
    case coord of
      (Z ** FZ) =>
        Replaced (cx, (Z ** FZ))

      (S j ** FZ) =>
        SplitBeg (cx, (Z ** FZ)) (c0, (j ** FZ))

      (S j ** FS pos) =>
        case strengthen (FS pos) of
          Left  _ =>
            SplitEnd (c0, (j ** pos)) (cx, (Z ** FZ))

          Right p =>
            case splitPrint cx (c0, (j ** p)) of
              NoChange => NoChange

              Replaced x =>
                SplitEnd (c0, (0 ** FZ)) x

              SplitBeg   x c =>
                SplitMid (c0, (0 ** FZ)) x c

              SplitMid (_, (k ** q)) x c =>
                SplitMid (c0, (S k ** FS q)) x c

              SplitEnd (_, (k ** q)) x =>
                SplitEnd (c0, (S k ** FS q)) x

public export
MacroTape : Type
MacroTape = (i : Nat ** (Fin (S i), Vect (S i) MacroBlock))

public export
Tape MacroTape where
  cells (_ ** (_, blocks)) =
    foldl (\acc, (_, (i ** _)) => S i + acc) 0 blocks

  marks (_ ** (_, blocks)) =
    foldl (\acc, (c, (i ** _)) =>
                 (if c == 0 then 0 else S i) + acc) 0 blocks

  blank = (0 ** (FZ, [(0, (0 ** FZ))]))

  read (_ ** (blockIndex, blocks)) =
    let (color, _) = index blockIndex blocks in
      color

  right _ = ?qwer
  left _ = ?wert

  ----------------------------------------

  print cx (0 ** (FZ, [b])) =
    case splitPrint cx b of
      NoChange       => (0 ** (   FZ, [   b   ]))
      Replaced   x   => (0 ** (   FZ, [   x   ]))
      SplitBeg   x c => (1 ** (   FZ, [   x, c]))
      SplitEnd a x   => (1 ** (FS FZ, [a, x   ]))
      SplitMid a x c => (2 ** (FS FZ, [a, x, c]))

  print cx tape@(S k ** (FZ, b0 :: b1@(c1, (j ** pos)) :: bs)) =
    case splitPrint cx b0 of
      NoChange       => tape

      SplitBeg   x c =>
        (    S $ S k ** (   FZ,      x :: c :: b1 :: bs))

      SplitMid a x c =>
        (S $ S $ S k ** (FS FZ, a :: x :: c :: b1 :: bs))

      Replaced   x   =>
        if cx == c1
          then (S k ** (FZ, x :: b1 :: bs))
          else (  k ** (FZ, (c1, (S j ** FZ)) :: bs))

      SplitEnd a x   =>
        if cx == c1
          then (S $ S k ** (FS FZ, a :: x :: b1 :: bs))
          else (    S k ** (FS FZ, a :: (c1, (S j ** FZ)) :: bs))

  print cx tape@(S k ** (FS FZ, b0 :: b1 :: bs)) =
    case splitPrint cx b1 of
      NoChange       => tape

      SplitMid a x c =>
        (S $ S $ S k ** (FS $ FS FZ, b0 :: a :: x :: c :: bs))

      Replaced   x   => ?zxcv_2

      SplitBeg   x c => ?zxcv_3

      SplitEnd a x   => ?zxcv_5

  print cx (S k ** (FS $ FS p, b0 :: b1 :: rest)) =
    let
      tail = the MacroTape (k ** (FS p, b1 :: rest))
      (j ** (pos, blocks)) = print cx tail
    in
      (S j ** (FS pos, b0 :: blocks))

  ----------------------------------------

  -- right (0 ** (FZ, [(c, (j ** pos))])) =
  --   case strengthen pos of
  --     Right p => (0 ** (FZ, [(c, (j ** FS p))]))
  --     Left  p =>
  --       case c of
  --         0 => (0 ** (FZ, [(0, (S j ** FS p))]))
  --         _ => (1 ** (FS FZ, (c, (j ** pos)) :: [(0, (0 ** FZ))]))

  -- right (S i ** (FZ, (c, (j ** pos)) :: blocks)) =
  --   case strengthen pos of
  --     Right p => (S i ** (FZ, (c, (j ** FS p)) :: blocks))
  --     Left  _ =>
  --       let (q, (k ** _)) :: rest = blocks in
  --         (S i ** (FS FZ, (c, (j ** pos)) :: (q, (k **  FZ)) :: rest))

  -- right (S i ** (FS p, b0 :: rest)) =
  --   let
  --     tail = the MacroTape (i ** (p, rest))
  --     (j ** (pos, blocks)) = right tail
  --   in
  --     (S j ** (FS pos, b0 :: blocks))

  ----------------------------------------

  -- left (0 ** (FZ, block@[(S _, (j ** FZ))])) =
  --   (1 ** (FZ, (0, (0 ** FZ)) :: block))
  -- left (S i ** (FZ, blocks@((S _, (j ** FZ)) :: rest))) =
  --   (S $ S i ** (FZ, (0, (0 ** FZ)) :: blocks))

  -- left (0 ** (FZ, (c, (j ** FS p)) :: rest)) =
  --   (0 ** (FZ, (c, (j ** weaken p)) :: rest))
  -- left (S i ** (FZ, (c, (j ** FS p)) :: rest)) =
  --   (S i ** (FZ, (c, (j ** weaken p)) :: rest))

  -- left (S i ** (FS FZ, b0@(c, (j ** _)) :: b1@(_, (_ ** FZ)) :: rest)) =
  --   -- check what's inside b0?
  --   -- yes, figure out how to get max pos for j
  --   (S i ** (FZ, b0 :: b1 :: rest))

  -- left (S i ** (FS FZ, b0 :: (c, (j ** FS p)) :: rest)) =
  --   (S i ** (FS FZ, b0 :: (c, (j ** weaken p)) :: rest))

  -- left (S i ** (FS $ FS p, block :: rest)) =
  --   let
  --     tail = the MacroTape (i ** (FS p, rest))
  --     (k ** (pos, blocks)) = left tail
  --   in
  --     (S k ** (FS pos, block :: blocks))

  -- left (i ** (FZ, (0, (j ** FZ)) :: rest)) =
  --   (i ** (FZ, (0, (S j ** FZ)) :: rest))
