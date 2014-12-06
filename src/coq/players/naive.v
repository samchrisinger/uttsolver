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
    | mk_macro_board 
        brd00 brd01 brd02 
        brd10 brd11 brd12 
        brd20 brd21 brd22 => 
      let brds := ([brd00; brd01; brd02;
                    brd10; brd11; brd12;
                    brd20; brd21; brd22]) in
        do_naive_player_free_move brds (evaluate_boards brds) [C00;C01;C02;C10;C11;C12;C20;C21;C22] mk
  end.

Definition naive_player (brd: macro_board) (last_mv: move): move :=
  let c := match last_mv with
                | first_move => C00
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
