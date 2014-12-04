Require Import List.
Require Import Bool.
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
                          e6 e7 e8
                       )
              | C01 => (mk_board 
                          e0 mv e2
                          e3 e4 e5
                          e6 e7 e8
                       )
              | C02 => (mk_board 
                          e0 e1 mv
                          e3 e4 e5
                          e6 e7 e8
                       )
              | C10 => (mk_board 
                          e0 e1 e2
                          mv e4 e5
                          e6 e7 e8
                       )
              | C11 => (mk_board 
                          e0 e1 e2
                          e3 mv e5
                          e6 e7 e8
                       )
              | C12 => (mk_board 
                          e0 e1 e2
                          e3 e4 mv
                          e6 e7 e8
                       )
              | C20 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          mv e7 e8
                       )
              | C21 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          e6 mv e8
                       )
              | C22 => (mk_board 
                          e0 e1 e2
                          e3 e4 e5
                          e6 e7 mv
                       )
          end)
  end.

Definition convert (o: outcome) :=
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
      | mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 b22 =>
        evaluate_board (lift_list_to_board ( 
          map (convert) (evaluate_boards [b00; b01; b02; b10; b11; b12; b20; b21; b22]))
        )
  end.

Definition get_board (b: macro_board) (c: cell) := 
  match b with
    | mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 b22 =>
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
    | mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 b22 =>
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


Definition mark_macro_board (b: macro_board) (mv: move): macro_board := 
  match mv with
    | mk_move c1 c2 mk => update_macro_board b c1 (mark_board (get_board b c1) mk c2)
    | first_move => b
  end.

Definition valid (b: board) (c: cell) (mk: mark) := 
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
                then valid (get_board b c1) c2 mk else false
       | _ => false
     end
   | _, first_move => true
   | _, _ => false
  end.

Fixpoint doPlayGame (b: macro_board) (l: list move) (last_move: move): outcome :=
  match l with 
    | nil => evaluate_macro_board b
    | h :: t => if negb (macro_valid b h last_move) then malformed else 
                   let b2 := mark_macro_board b h in
                      match (evaluate_macro_board b2) with
                        | incomplete => doPlayGame b2 t h
                        | a => a
                      end
  end.

Definition playGame (l: list move): outcome :=
  doPlayGame empty_macro_board l first_move.

Definition naive_player_small_board (brd: board) (mk: mark): cell :=
  match brd with
    | mk_board B _ _ _ _ _ _ _ _ => C00
    | mk_board _ B _ _ _ _ _ _ _ => C01
    | mk_board _ _ B _ _ _ _ _ _ => C02
    | mk_board _ _ _ B _ _ _ _ _ => C10
    | mk_board _ _ _ _ B _ _ _ _ => C11
    | mk_board _ _ _ _ _ B _ _ _ => C12
    | mk_board _ _ _ _ _ _ B _ _ => C20
    | mk_board _ _ _ _ _ _ _ B _ => C21
    | mk_board _ _ _ _ _ _ _ _ B => C22
    | _ => C00
  end.
 
Fixpoint do_naive_player_free_move (brds: list board) (outcomes: list outcome) (cells: list cell) (mk: mark): move := 
  match brds, outcomes, cells with
    | b::t1, o::t2, c::t3 => 
      match o with
        | incomplete => mk_move (c) (naive_player_small_board b mk) mk
        | _ => do_naive_player_free_move t1 t2 t3 mk
      end
    | _, _,_ => first_move
  end.

Definition naive_player_free_move (brd: macro_board) (mk: mark): move :=
  match brd with
    | mk_macro_board brd00 brd01 brd02 brd10 brd11 brd12 brd20 brd21 brd22 => 
      let brds := ([brd00;brd01;brd02;brd10;brd11;brd12;brd20;brd21;brd22]) in
        do_naive_player_free_move brds (evaluate_boards brds) [C00;C01;C02;C10;C11;C12;C20;C21;C22] mk
  end.

Definition naive_player (brd: macro_board) (last_mv: move): move :=
  let c := match last_mv with
                | first_move => C11
                | mk_move _ c2 _ => c2
  end in
  let mk := match last_mv with
                   | first_move => X
                   | mk_move _ _ mk => 
                 match mk with
                   | X => O
                   | O => X
                   | _ => B
                 end
  end in
  let small_brd := (get_board brd c) in
  match evaluate_board (small_brd) with
    | malformed => first_move
    | incomplete => mk_move c (naive_player_small_board small_brd mk) mk
    | tie | Xwins | Owins => naive_player_free_move brd mk
  end.
  
Fixpoint doPlayGameWithPlayers (player: macro_board -> move -> move) 
                                                       (brd: macro_board) (last_mv: move) (turn: nat) (l: list move): game :=
  match turn with
    | 0 => mk_game l turn brd (evaluate_macro_board brd)
    | S n' => 
    let mv := player brd last_mv in
    if negb (macro_valid brd mv last_mv) then mk_game (mv::l) n' brd malformed else (* hitting this branch *)
    let b2 := mark_macro_board brd mv in
    match (evaluate_macro_board b2) with
      | incomplete => doPlayGameWithPlayers player b2 mv n'  (mv :: l)
      | a => mk_game (mv::l) turn b2 a
    end
  end.

Definition playGameWithPlayers (player : macro_board -> move -> move): game :=
  doPlayGameWithPlayers player empty_macro_board first_move 81 [].

Compute playGameWithPlayers naive_player.


(* Temporal logic *)
