module Tape

import Data.Nat
import public Data.Vect

import Program

%default total

public export
interface Show tape => Tape tape where
  blank : tape

  read  :          tape -> Color
  print : Color -> tape -> tape

  shift : Shift -> tape -> tape
  shift L tape =  left tape
  shift R tape = right tape

  left  :          tape -> tape
  right :          tape -> tape

----------------------------------------

public export
MicroTape : Type
MicroTape = (i : Nat ** (Fin (S i), Vect (S i) Color))

public export
Show MicroTape where
  show (_ ** (_, tape)) = show (length tape, marks tape) where
    marks : Vect k Color -> Nat
    marks xs = let (n ** _) = filter ((/=) 0) xs in n

public export
Tape MicroTape where
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

Show MacroTape where
  show x = "not implemented"

Tape MacroTape where
  blank = (0 ** (FZ, [(0, (0 ** FZ))]))

  read (_ ** (blockIndex, blocks)) =
    let (color, _) = index blockIndex blocks in
      color

  ----------------------------------------

  print color tape = ?qwer

  right tape = ?zxcv

  ----------------------------------------

  left (0 ** (FZ, [(0, (j ** FZ))])) =
    (0 ** (FZ, [(0, (S j ** FZ))]))

  left (0 ** (FZ, [block@(c, (j ** FZ))])) =
    (1 ** (FZ, (0, (0 ** FZ)) :: [block]))

  left (0 ** (FZ, [(c, (j ** FS p))])) =
    (0 ** (FZ, [(c, (j ** weaken p))]))

  left (S i ** (FZ, (0, (j ** FZ)) :: rest)) =
    (S i ** (FZ, (0, (S j ** FZ)) :: rest))

  left (S i ** (FZ, blocks@((S _, (j ** FZ)) :: rest))) =
    (S $ S i ** (FZ, (0, (0 ** FZ)) :: blocks))

  left (S i ** (FZ, (c, (j ** FS p)) :: rest)) =
    (S i ** (FZ, (c, (j ** weaken p)) :: rest))

  left (S i ** (FS p, block :: rest)) = ?asdf_2
