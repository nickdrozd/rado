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

  left (i ** (FZ, (0, (j ** FZ)) :: blocks)) =
    (i ** (FZ, (0, (S j ** FZ)) :: blocks))

  left (i ** (FZ, block@(c, (j ** FZ)) :: blocks)) =
    (S i ** (FZ, (0, (0 ** FZ)) :: block :: blocks))

  left (i ** (FZ, (c, (j ** FS p)) :: blocks)) =
    (i ** (FZ, (c, (j ** weaken p)) :: blocks))

  left (S i ** (FS p, blocks)) = ?asdf_2
