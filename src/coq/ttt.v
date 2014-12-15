Require Import types.
Require Import game.
Require Import List.
Require Import Arith.
Import ListNotations.

Require Import Notations.

Inductive mmove: Set:=
  | mk_mmove: cell -> mark -> mmove.

Definition is_blank (mk: mark): bool :=
  match mk with 
    | B => true
    | _ => false
  end.

Definition cell_is_blank (b: board) (c: cell): bool :=
  match b with
    | mk_board m1 m2 m3 m4 m5 m6 m7 m8 m9 =>
        match c with
          | C00 => is_blank m1
          | C01 => is_blank m2
          | C02 => is_blank m3
          | C10 => is_blank m4
          | C11 => is_blank m5
          | C12 => is_blank m6
          | C20 => is_blank m7
          | C21 => is_blank m8
          | C22 => is_blank m9
      end
end.

Definition invalid_board := mk_board O O O O O O O O O.

Definition apply_move_to_board (b: board) (m: mmove): board:=
  match m with
      | mk_mmove c mk => if (cell_is_blank b c) then (mark_board b mk c) else invalid_board
  end.
  
Fixpoint count_mark (l: list mark) (equality: mark -> bool) : nat :=
  match l with
    | nil => 0
    | h :: t => if equality h then (S (count_mark t equality)) else (count_mark t equality)
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
  ((safe (apply_move_to_board (apply_move_to_board bd x) y)) \/ (safe (apply_move_to_board bd x)))) -> (safe bd)
  | done: forall (bd: board), complete bd -> safe bd.

Theorem init_safe: safe empty_board.
Proof. (* X gets first move *)
apply is_safe. exists (mk_mmove C00 X). intros. inversion H. destruct y. destruct m. simpl in H0.
    inversion H0. simpl in H0. inversion H0. destruct c. simpl in H0. inversion H0. simpl in *.  left.
(* Y goes in 01 *)
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    simpl in H3. inversion H3. inversion H3. destruct c. inversion H4. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl.  left.
apply done. compute. trivial.  inversion H7. simpl in H7. simpl in *. left.
 apply done. trivial. left. 
 apply done. trivial. left. 
 apply done. trivial. left. 
 apply done. trivial. left. 
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. 
 apply done. trivial. left. 
 apply done. trivial. left. 
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C10 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. simpl. left.
apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl. simpl in *.

apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl. simpl in *.
apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
 
(* Y goes in 02 *)
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C10 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. left.
apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl. left.
 apply done. trivial. left. inversion H10. inversion H10. simpl in *.  left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl. simpl in *. inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. left.
 inversion H10. simpl in *. inversion H10. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *.  left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
 
(* Y goes in 10 *)

apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *. inversion H4. simpl in *.  left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. simpl in *.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. simpl in *.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *. inversion H6. simpl in *. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C21 X). intros. inversion H11. destruct y. destruct m.
    inversion H12. inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13. 
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13.
    simpl in *.  left.

(* A complete board *)
apply is_safe. exists (mk_mmove C21 X). intros. inversion H11. destruct y. destruct m.
    inversion H12. inversion H12. destruct c. simpl in *. right.
apply done. trivial. simpl in *. left.
apply is_safe. exists (mk_mmove C20 X). intros. inversion H14. destruct y. destruct m. simpl in *.
    inversion H15. inversion H15. destruct c. simpl in *. inversion H16. inversion H16. inversion H16.
    inversion H16. inversion H16.  inversion H16.  inversion H16.  inversion H16.  inversion H16.
    inversion H13.  inversion H13. simpl in *.  right.
apply done. trivial. simpl in *. left.
apply done. trivial. simpl in *. inversion H13. simpl in *. inversion H12. simpl in *. inversion H13.
    simpl in *. inversion H10. simpl in *. inversion H7. inversion H7. simpl in *. left.
    
apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. left.

 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. left. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. trivial. left. simpl in *.
apply done. trivial. left. simpl in *.
apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. left. simpl in *. inversion H10. simpl in *. inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. trivial. left. simpl in *.
apply done. trivial. left. simpl in *.
apply done. trivial. left. simpl in *. inversion H7. simpl in *. left.

(* Y goes in 11 *)
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. simpl in *. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *. inversion H4. simpl in *.  left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. simpl in *.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *. inversion H4. inversion H4. simpl in *. left.

(* Y goes in 12 *)
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. simpl in *. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.


apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. simpl in *.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H4. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. simpl in *. left.
 
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C02 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left. simpl in *.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. left. simpl in *.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. inversion H7. inversion H7. simpl in *.  left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 
apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. inversion H10. inversion H7. simpl in *. left.

(* Y goes in 20 *)
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. left. simpl in *.
apply is_safe. exists (mk_mmove C10 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. left. simpl in *. 
apply is_safe. exists (mk_mmove C12 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C02 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H10. inversion H10.
     inversion H7. inversion H7. inversion H7. simpl in *. left.

(* Y goes in 21 *)
apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. simpl in *. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
simpl in *. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.


apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left. simpl in *.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.  simpl in *.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. simpl in *.
 apply done. trivial. left. inversion H7. inversion H7. inversion H4. simpl in *. left.
 
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left. inversion H7. inversion H7. inversion H7. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left. simpl in *.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. left. simpl in *.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H10. simpl in *. left.
 apply done. trivial. left. inversion H10. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C12 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. simpl in *. left.


apply is_safe. exists (mk_mmove C10 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. simpl in *. left.
 apply done. trivial. left. inversion H13. inversion H13. inversion H13. simpl in *. left.
 apply done. trivial. left. inversion H13. inversion H10. simpl in *. left.
 
apply is_safe. exists (mk_mmove C01 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. simpl in *. left.
 apply done. trivial. left. inversion H13. inversion H13. inversion H13. simpl in *. left.
 apply done. trivial. left. inversion H13. inversion H10. inversion H10. inversion H10.
     inversion H10. inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H7. simpl in *. left.
 
apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H10. inversion H10.
     inversion H7. inversion H7. inversion H7. simpl in *. left.

(* Y goes in 22 *)

apply is_safe. exists (mk_mmove C11 X). intros. inversion H2. destruct y. destruct m.  
    inversion H3. inversion H3. destruct c. simpl in *. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C22 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. inversion H7. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left.
 apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C12 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. left. simpl in *.

apply is_safe. exists (mk_mmove C10 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
 apply done. trivial. left.
 apply done. trivial. left. inversion H10. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. simpl in *. left.
 apply done. trivial. left. inversion H13. inversion H13. inversion H13. simpl in *. left.
 apply done. trivial. left. inversion H13. inversion H10. inversion H10. inversion H7. inversion H7.
     simpl in *. left.
  

apply is_safe. exists (mk_mmove C10 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H7. simpl in *. left.
apply done. trivial. inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C10 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
 apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H7. simpl in *. left.
apply done. trivial. inversion H10.  inversion H10. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. simpl. trivial. inversion H10. inversion H10. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. simpl. trivial. inversion H10. inversion H10. inversion H7. inversion H7. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. simpl. trivial. inversion H10. inversion H10. inversion H7. inversion H7. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10.  simpl in *. left.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C12 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C02 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. simpl in *.  inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. inversion H7. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. simpl. trivial. inversion H10. inversion H10. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H10. inversion H10. 
    simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H7. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C21 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H10. inversion H10.
    simpl in *. left.
apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.

apply done. trivial. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C21 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C10 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.

apply is_safe. exists (mk_mmove C12 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. simpl in *.  inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. inversion H7. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C02 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. simpl in *.  inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. inversion H7. inversion H4. simpl in *. left.

apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C01 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H7. inversion H7. inversion H7. simpl in *. left.

apply is_safe. exists (mk_mmove C20 X). intros. inversion H5. destruct y. destruct m. inversion H6.
    inversion H6. destruct c. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. left.
apply done. trivial. left.
apply done. trivial. left.
apply done. trivial. left.
apply done. trivial. left.
apply done. trivial. left. simpl in *.

apply is_safe. exists (mk_mmove C10 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply is_safe. exists (mk_mmove C12 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. simpl in *.  inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. inversion H7. inversion H4. simpl in *. left.
apply is_safe. exists (mk_mmove C01 X). intros. inversion H11. destruct y. destruct m. inversion H12.
    inversion H12. destruct c. inversion H13. inversion H13. inversion H13. inversion H13.
    inversion H13. inversion H13. inversion H13. inversion H13. inversion H13. inversion H10.
    inversion H10. inversion H10. simpl in *. left. simpl in *.

apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H7. simpl in *. left.
apply is_safe. exists (mk_mmove C02 X). intros. inversion H8. destruct y. destruct m. inversion H9.
    inversion H9. destruct c. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. simpl in *. left.
apply done. trivial. inversion H10. inversion H10. inversion H10. inversion H10. inversion H10.
    inversion H7. inversion H7. inversion H7. inversion H4.
Qed.