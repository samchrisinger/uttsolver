Require Import types.
Require Import game.

Require Import Notations.

Inductive mmove: Set:=
  | mk_mmove: cell -> mark -> mmove.

Definition apply_move_to_board (b: board) (m: mmove): board:=
  match m with
      | mk_mmove c mk => (mark_board b mk c)
  end.

Definition complete (bd: board): Prop:=
  match evaluate_board bd with
      | Xwins | tie => True
      | _ => False
  end.

Inductive safe: board -> Prop:=
| is_safe: move -> move -> (forall (bd: board), 
              (safe bd) -> (exists (x: mmove), 
                             forall (y: mmove), 
                               safe (apply_move_to_board (apply_move_to_board bd x) y)))
| done: forall (bd: board), complete bd -> safe bd.
end.


      