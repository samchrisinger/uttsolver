Require Export List.
Require Export Bool.
Import ListNotations.
Require Import types.

Definition mark_board (brd: board)(mv: mark)(c: cell): board:=
  match brd with
    | mk_board
         e0 e1 e2 
         e3 e4 e5
         e6 e7 e8
      => (match c with
              | C00 => (mk_board 
                          mv e1 e2
                          e3 e4 e5
                          e6 e7 e8)
              | C01 => (mk_board 
                          e0 mv e2
                          e3 e4 e5
                          e6 e7 e8)
              | C02 => (mk_board 
                          e0 e1 mv
                          e3 e4 e5
                          e6 e7 e8)
              | C10 => (mk_board 
                          e0 e1 e2
                          mv e4 e5
                          e6 e7 e8)
              | C11 => (mk_board 
                          e0 e1 e2
                          e3 mv e5
                          e6 e7 e8)
              | C12 => (mk_board 
                          e0 e1 e2
                          e3 e4 mv
                          e6 e7 e8)
              | C20 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          mv e7 e8)
              | C21 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          e6 mv e8)
              | C22 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          e6 e7 mv)
          end)
  end.

Definition convert_outcome_to_mark (o: outcome) :=
  match o with
    | Xwins => X
    | Owins => O
    | _ => B
  end.

Fixpoint in_list {A: Type} (x: A) (l: list A) (equality: A -> A -> bool) : bool :=
  match l with
    | nil => false
    | h :: t => if equality h x then true else in_list x t equality
  end.

Definition do_match_mark (mk: mark) (l: list mark): bool :=
  match l with
    | [X; X; X] => match mk with
                            | X => true
                            | _ => false
                          end
    | [O; O; O] => match mk with
                            | O => true
                            | _ => false
                          end
    | _ => false
  end.

Definition match_mark (brd: board) (mk: mark) : bool :=
  match brd with
    | mk_board m1 m2 m3
                       m4 m5 m6
                       m7 m8 m9 => in_list true (map (do_match_mark mk) 
                            [[m1; m2; m3]; [m4;m5;m6]; [m7;m8;m9];
                             [m1; m4; m7]; [m2;m5;m8]; [m3;m6;m9];
                             [m1; m5; m9]; [m3;m5;m7]]) eqb
  
  end.

Definition has_blanks (brd: board): bool :=
  match brd with
    | mk_board m1 m2 m3
                       m4 m5 m6
                        m7 m8 m9 => in_list B [m1;m2;m3;m4;m5;m6;m7;m8;m9] mark_eq
  end.

Definition evaluate_board (brd: board): outcome :=
  if (match_mark brd X) then Xwins
  else if (match_mark brd O) then Owins
  else if (has_blanks brd) then incomplete
  else tie.


Definition evaluate_boards (l : list board) :=
  map evaluate_board l.

Definition evaluate_macro_board (b: macro_board) :=
  match b with
      | mk_macro_board 
          b00 b01 b02 
          b10 b11 b12 
          b20 b21 b22 =>
        evaluate_board (lift_list_to_board 
                          (map convert_outcome_to_mark 
                               (evaluate_boards [b00; b01; b02; 
                                                 b10; b11; b12; 
                                                 b20; b21; b22])))
  end.

Definition get_board (b: macro_board) (c: cell) := 
  match b with
    | mk_macro_board 
        b00 b01 b02 
        b10 b11 b12 
        b20 b21 b22 =>
     match c with
        | C00 => b00
        | C01 => b01
        | C02 => b02
        | C10 => b10
        | C11 => b11
        | C12 => b12
        | C20 => b20
        | C21 => b21
        | C22 => b22
      end
    end.

Definition update_macro_board (b: macro_board) (c: cell) (brd: board) :=
  match b with
    | mk_macro_board 
        b00 b01 b02 
        b10 b11 b12 
        b20 b21 b22 =>
     match c with
        | C00 => mk_macro_board brd b01 b02 b10 b11 b12 b20 b21 b22
        | C01 => mk_macro_board b00 brd b02 b10 b11 b12 b20 b21 b22
        | C02 => mk_macro_board b00 b01 brd b10 b11 b12 b20 b21 b22
        | C10 => mk_macro_board b00 b01 b02 brd b11 b12 b20 b21 b22
        | C11 => mk_macro_board b00 b01 b02 b10 brd b12 b20 b21 b22
        | C12 => mk_macro_board b00 b01 b02 b10 b11 brd b20 b21 b22
        | C20 => mk_macro_board b00 b01 b02 b10 b11 b12 brd b21 b22
        | C21 => mk_macro_board b00 b01 b02 b10 b11 b12 b20 brd b22
        | C22 => mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 brd
      end
    end.

Definition mark_macro_board (brd: macro_board) (mv: move): macro_board := 
  match mv with
    | mk_move c1 c2 mk => update_macro_board brd c1 (mark_board (get_board brd c1) mk c2)
    | first_move => brd
  end.

Definition valid_board (b: board) (c: cell) (mk: mark) := 
  match evaluate_board (mark_board b mk c) with
    | malformed => false
    | _ => true
  end.

Definition macro_valid (b: macro_board) (mv: move) (last_move: move) :=
  match mv, last_move with
    | mk_move c1 c2 mk, mk_move c1' c2' mk' =>
      match evaluate_board (get_board b c1) with
        | incomplete => 
            if (orb  (cell_equal c1 c2')
              match (evaluate_board (get_board b c2' )) with
                | incomplete => false
                | _ => true
              end)
                then valid_board (get_board b c1) c2 mk else false
       | _ => false
     end
   | _, first_move => true
   | _, _ => false
  end.

