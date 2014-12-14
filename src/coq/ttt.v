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

(* Also need some sort of valid board, which errors if there are more Os than Xs *)
  
Definition valid_moves (m1 m2: mmove): Prop :=
  match m1, m2 with
    mk_mmove c1 mk1, mk_mmove c2 mk2 =>
      match mk1, mk2 with
        | B, _ | _, B | X, X | O, O => False
        | X, O | O, X =>
          match c1, c2 with
            | C00, C00 | C01, C01 | C02, C02 
            | C10, C10 | C11, C11 | C12, C12
            | C20, C20 | C21, C21 | C22, C22 => False
            | _, _ => True
          end
      end
  end.

Inductive safe: board -> Prop:=
  | is_safe: forall (bd: board),  (exists (x: mmove), forall (y: mmove), (valid_moves x y) ->
  (safe (apply_move_to_board (apply_move_to_board bd x) y))) -> (safe bd)
  | done: forall (bd: board), complete bd -> safe bd.

Theorem init_safe: safe empty_board.
Proof.
apply is_safe. exists (mk_mmove C00 X). intros. destruct y. destruct m. simpl in H. inversion H.
  simpl in H. inversion H. destruct c. simpl in H. inversion H. simpl. 
apply is_safe. exists (mk_mmove C11 X). intros. destruct y. destruct m. simpl in H0. inversion H0.
  simpl in H0. inversion H0. destruct c. simpl.
      