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
  | P0: position
  | P1: position
  | P2: position
  | P3: position
  | P4: position
  | P5: position
  | P6: position
  | P7: position
  | P8: position.

Definition pos_to_nat(p: position): nat:=
  match p with
    | P0 => 0
    | P1 => 1
    | P2 => 2
    | P3 => 3
    | P4 => 4
    | P5 => 5
    | P6 => 6
    | P7 => 7
    | P8 => 8
  end.

Definition pos_eq(p1 p2: position): bool:=
  (beq_nat (pos_to_nat p1) (pos_to_nat p2)).

                              