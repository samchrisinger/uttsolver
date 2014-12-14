Require Export types.
Require Export game.

Require Export List.
Include ListNotations.

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

(* The naive player simply chooses the top left macro and micro boards, always *)

Fixpoint doPlayGameWithPlayers (cur_player next_player: macro_board -> move -> move) 
                                                       (brd: macro_board) (last_mv: move) (turn: nat) (l: list move): outcome :=
  match turn with
    | 0 =>  (evaluate_macro_board brd)
    | S n' => 
    let mv := cur_player brd last_mv in
    if negb (macro_valid brd mv last_mv) then malformed else
    let b2 := mark_macro_board brd mv in
    match (evaluate_macro_board b2) with
      | incomplete => (doPlayGameWithPlayers (next_player) (cur_player) b2 mv n' (mv :: l))
      | a => a
    end
  end.

Definition playGameWithPlayers (cur_player next_player : macro_board -> move -> move): outcome :=
  doPlayGameWithPlayers cur_player next_player empty_macro_board first_move 81 [].
  

(* This is good for debugging, but makes proofs trickier *)
Fixpoint DEBUG_doPlayGameWithPlayers (cur_player next_player: macro_board -> move -> move) 
                                                       (brd: macro_board) (last_mv: move) (turn: nat) (l: list move): game :=
  match turn with
    | 0 => mk_game l turn brd (evaluate_macro_board brd)
    | S n' => 
    let mv := cur_player brd last_mv in
    if negb (macro_valid brd mv last_mv) then mk_game (mv::l) n' brd malformed else
    let b2 := mark_macro_board brd mv in
    match (evaluate_macro_board b2) with
      | incomplete => DEBUG_doPlayGameWithPlayers next_player cur_player b2 mv n'  (mv :: l)
      | a => mk_game (mv::l) turn b2 a
    end
  end.

Definition DEBUG_playGameWithPlayers (player1 player2 : macro_board -> move -> move): game :=
  DEBUG_doPlayGameWithPlayers player1 player2 empty_macro_board first_move 81 [].
  
Require Export players.