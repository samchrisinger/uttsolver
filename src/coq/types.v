Require Import Arith.
Require Export List.
Import ListNotations.

Inductive mark: Set:=
  | B: mark
  | X: mark
  | O: mark.

Definition mark_eq(m1 m2: mark): bool:= 
  match m1, m2 with
      | B, B => true
      | X, X => true
      | O, O => true
      | _, _ => false
  end.



Record board:= mk_board {
                   m00: mark;  m01: mark; m02: mark;
                   m10: mark; m11: mark; m12: mark;
                   m20: mark; m21: mark; m22: mark
}.


Record macro_board := mk_macro_board {
                   b00: board;  b01: board; b02: board;
                   b10: board; b11: board; b12: board;
                   b20: board; b21: board; b22: board
}.

Inductive cell: Set :=
  | C00
  | C01
  | C02
  | C10
  | C11
  | C12
  | C20
  | C21
  | C22.
  
  
Definition cell_equal (c1 c2: cell) :=
  match c1, c2 with
    | C00, C00
    | C01, C01
    | C02, C02
    | C10, C10
    | C11, C11
    | C12, C12
    | C20, C20
    | C21, C21
    | C22, C22 => true
    | _, _ => false
  end.

Definition empty_board: board:= 
  (mk_board 
     B B B
     B B B
     B B B
  ).
  
Fixpoint lift_list_to_board (l : list mark) :=
  match l with
    | [x1; x2; x3; x4; x5; x6; x7; x8; x9] => mk_board x1 x2 x3 x4 x5 x6 x7 x8 x9 
    | _ => empty_board
  end.

Definition empty_macro_board: macro_board:= 
  (mk_macro_board 
     empty_board empty_board empty_board
     empty_board empty_board empty_board
     empty_board empty_board empty_board
  ).

Inductive move: Set :=
  | mk_move: cell -> cell -> mark -> move
  | first_move.
  
Inductive outcome: Set :=
  | Xwins
  | Owins
  | incomplete
  | tie
  | malformed.
  
  
Inductive game: Set :=
  | mk_game: list move -> nat -> macro_board -> outcome -> game.
