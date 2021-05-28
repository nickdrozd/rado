module Tape

import Data.Nat
import public Data.Vect

import Program

%default total

public export
interface Tape tape where
  marks : tape -> Nat
  cells : tape -> Nat

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
  marks (_ ** (_, tape)) = let (n ** _) = filter ((/=) 0) tape in n
  cells (_ ** (_, tape))  = length tape

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

MacroTape : Type
MacroTape = (i : Nat ** (Fin (S i), Vect (S i) Block)) where
  Block : Type
  Block = (Color, (j : Nat ** Fin (S j)))

Tape MacroTape where
  marks _ = 0
  cells _ = 0

  blank = (0 ** (FZ, [(0, (0 ** FZ))]))

  read (_ ** (blockIndex, blocks)) =
    let (color, _) = index blockIndex blocks in
      color

  ----------------------------------------

  print color tape = ?qwer
  left _ = ?tyui

  ----------------------------------------

  right (0 ** (FZ, [(c, (j ** pos))])) =
    case strengthen pos of
      Right p => (0 ** (FZ, [(c, (j ** FS p))]))
      Left  p =>
        case c of
          0 => (0 ** (FZ, [(0, (S j ** FS p))]))
          _ => (1 ** (FS FZ, (c, (j ** pos)) :: [(0, (0 ** FZ))]))

  right (S i ** (  FZ, block :: blocks)) = ?zxcv_3

  right (S i ** (FS p, block :: blocks)) =
    let
      (k ** (pos, rest)) = right (the MacroTape (i ** (p, blocks)))
    in
      (S k ** (FS pos, block :: rest))

  -- ----------------------------------------

  -- left (0 ** (FZ, [(0, (j ** FZ))])) =
  --   (0 ** (FZ, [(0, (S j ** FZ))]))

  -- left (0 ** (FZ, [block@(c, (j ** FZ))])) =
  --   (1 ** (FZ, (0, (0 ** FZ)) :: [block]))

  -- left (0 ** (FZ, [(c, (j ** FS p))])) =
  --   (0 ** (FZ, [(c, (j ** weaken p))]))

  -- left (S i ** (FZ, (0, (j ** FZ)) :: rest)) =
  --   (S i ** (FZ, (0, (S j ** FZ)) :: rest))

  -- left (S i ** (FZ, blocks@((S _, (j ** FZ)) :: rest))) =
  --   (S $ S i ** (FZ, (0, (0 ** FZ)) :: blocks))

  -- left (S i ** (FZ, (c, (j ** FS p)) :: rest)) =
  --   (S i ** (FZ, (c, (j ** weaken p)) :: rest))

  -- left (S i ** (FS FZ, b0 :: b1@(_, (_ ** FZ)) :: rest)) =
  --   -- check what's inside b0?
  --   (S i ** (FZ, b0 :: b1 :: rest))

  -- left (S i ** (FS FZ, b0 :: (c, (j ** FS p)) :: rest)) =
  --   (S i ** (FS FZ, b0 :: (c, (j ** weaken p)) :: rest))

  -- left (S i ** (FS $ FS p, block :: rest)) =
  --   let (k ** (pos, blocks)) = left (the MacroTape (i ** (FS p, rest))) in
  --     (S k ** (FS pos, block :: blocks))
