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
splitPrint q (c, block) =
  if c == q then NoChange else
    case block of
      (Z ** FZ) => Replaced (q, (Z ** FZ))
      (S j ** FZ) => SplitBeg (q, (Z ** FZ)) (c, (j ** FZ))
      (S j ** FS pos) =>
        case strengthen (FS pos) of
          Left  _ => SplitEnd (c, (j ** pos)) (q, (Z ** FZ))
          Right p => ?asd

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

  print cx (0 ** (FZ, [block])) = ?asdf_1

  print cx tape@(S k ** (FZ, b0 :: b1@(c1, _) :: bs)) =
    case splitPrint cx b0 of
      NoChange          =>
        tape
      Replaced bx       =>
        ?asdf_5
      SplitBeg bx bc    =>
        (S $ S k ** (FZ, bx :: bc :: b1 :: bs))
      SplitMid bc bx bd =>
        (S $ S $ S k ** (FZ, bc :: bx :: bd :: b1 :: bs))
      SplitEnd    bc bx =>
        ?asdf_8

  print cx tape@(S k ** (FS FZ, b0 :: b1 :: bs)) =
    case splitPrint cx b1 of
      NoChange       => tape
      Replaced x     => ?zxcv_2
      SplitBeg x y   => ?zxcv_3
      SplitMid x y z => ?zxcv_4
      SplitEnd   y z => ?zxcv_5

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
