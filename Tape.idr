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

  right (  Z ** (FZ, tape)) = (S Z ** (FS FZ, tape ++ [0]))
  right (S i ** (FZ, tape)) = (S i ** (FS FZ, tape       ))

  right (i ** (FS p, tape)) =
    case strengthen $ FS p of
      Right p => (  i ** (FS p, tape))
      Left  _ =>
        let prf = sym $ plusCommutative i 1 in
          (S i ** (FS $ FS p, rewrite prf in tape ++ [0]))

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

  right tape = ?zxcv

  left (i ** (FZ, (0, (j ** FZ)) :: rest)) =
    (i ** (FZ, (0, (S j ** FZ)) :: rest))

  left (i ** (FZ, (c, (j ** FS p)) :: rest)) =
    (i ** (FZ, (c, (j ** weaken p)) :: rest))

  left (i ** (FZ, blocks @ ((c, (_ ** FZ)) :: _))) =
    let newBlock = (0, (1 ** FZ)) in
      (S i ** (FZ, newBlock :: blocks))

  left (i ** (FS p, block :: blocks)) = ?qwer

  print color (0 ** (FZ, [(curr, (0 ** FZ))])) =
    (0 ** (FZ, [(color, (0 ** FZ))]))

  print color (0 ** (FZ, [(curr, (S j ** FZ))])) =
    let
      newBlock = (color, (0 ** FZ))
      oldBlock = (curr, (j ** FZ))
    in
      (1 ** (FZ, [newBlock] ++ [oldBlock]))

  print color (0 ** (FZ, [(curr, (S j ** FS p))])) =
    case strengthen $ FS p of
      Right x => ?asdf_3
      Left  x => ?asdf_1

  print color (S i ** (pos, blocks)) = ?asdf_2
