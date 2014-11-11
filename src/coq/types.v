Require Import Arith.

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

Inductive position: Set:=
  | P00: position
  | P01: position
  | P02: position
  | P10: position
  | P11: position
  | P12: position
  | P20: position
  | P21: position
  | P22: position.

Definition pos_to_nat(p: position): nat:=
  match p with
    | P00 => 0
    | P01 => 1
    | P02 => 2
    | P10 => 3
    | P11 => 4
    | P12 => 5
    | P20 => 6
    | P21 => 7
    | P22 => 8
  end.

Definition pos_eq(p1 p2: position): bool:=
  (beq_nat (pos_to_nat p1) (pos_to_nat p2)).

Record board:= mk_board {
                   m00: mark;
                   m01: mark;
                   m02: mark;
                   m10: mark;
                   m11: mark;
                   m12: mark;
                   m20: mark;
                   m21: mark;
                   m22: mark
}.

Definition empty_board: board:= 
  (mk_board 
     B B B
     B B B
     B B B
  ).

Definition mark_board (brd: board)(mv: mark)(pos: position): board:=
  match brd with
    | mk_board
         e0 e1 e2 
         e3 e4 e5
         e6 e7 e8
      => (match pos with
              | P00 => (mk_board 
                          mv e1 e2
                          e3 e4 e5
                          e6 e7 e8
                       )
              | P01 => (mk_board 
                          e0 mv e2
                          e3 e4 e5
                          e6 e7 e8
                       )
              | P02 => (mk_board 
                          e0 e1 mv
                          e3 e4 e5
                          e6 e7 e8
                       )
              | P10 => (mk_board 
                          e0 e1 e2
                          mv e4 e5
                          e6 e7 e8
                       )
              | P11 => (mk_board 
                          e0 e1 e2
                          e3 mv e5
                          e6 e7 e8
                       )
              | P12 => (mk_board 
                          e0 e1 e2
                          e3 e4 mv
                          e6 e7 e8
                       )
              | P20 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          mv e7 e8
                       )
              | P21 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          e6 mv e8
                       )
              | P22 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          e6 e7 mv
                       )                                                  
          end)
  end.

Compute (mark_board empty_board X P11).
