Require Import types.
Require Import game.
Require Import List.
Require Import Arith.
Import ListNotations.

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
  
Fixpoint count_mark (l: list mark) (equality: mark -> bool) : nat :=
  match l with
    | nil => 0
    | h :: t => if equality h then (S (count_mark t equality)) else (count_mark t equality)
  end.
  
Definition valid_board_state (brd: board): Prop :=
  match brd with
    | mk_board m1 m2 m3 m4 m5 m6 m7 m8 m9 => 
      let l := [m1;m2;m3;m4;m5;m6;m7;m8;m9] in
        match (beq_nat (count_mark l (mark_eq X)) (count_mark l (mark_eq O))) with
          | true => True
          | false => False
        end
  end.

Inductive safe: board -> Prop:=
  | is_safe: forall (bd: board),  (exists (x: mmove), forall (y: mmove), ((valid_moves x y) /\ (valid_board_state (apply_move_to_board (apply_move_to_board bd x) y))) ->
  ((safe (apply_move_to_board (apply_move_to_board bd x) y)))) -> (safe bd)
  | done: forall (bd: board), complete bd -> safe bd.

Theorem init_safe: safe empty_board.
Proof.
apply is_safe. exists (mk_mmove C00 X). intros. inversion H. destruct y. destruct m. simpl in H0.
    inversion H0. simpl in H0. inversion H0. destruct c. simpl in H0. inversion H0. simpl.
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    simpl in H3. inversion H3. inversion H3. destruct c. inversion H4. inversion H4. simpl.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl.
apply done. compute. trivial. inversion H7. simpl in H7.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
apply done. trivial.
repeat (apply is_safe; exists (mk_mmove C22 X); intros; inversion H5; destruct y; destruct m; inversion H6;
    inversion H6; destruct c; inversion H7; inversion H7; repeat (apply done; trivial)).

     simpl. simpl in H6. simpl in H7. simpl in H5. simpl in H4. simpl in H3. simpl in H2. simpl in H1. simpl in H0. simpl in H.

      