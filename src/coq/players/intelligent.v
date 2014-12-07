(* COMMENT OUT after debugging *)
(*
Require Import "../types".
Require Import "../game".
Require Import List.
Import ListNotations.
*)

Inductive node (T: Type): Set:=
    | mk_node: node T -> list (node T) -> node T
    | leaf: node T.

Implicit Arguments node [T].

Inductive tree {T: Type}: Set:=
    | empty_tree: tree
    | mk_tree: (@node T) -> tree.

Inductive micro_move: Set:= 
    | mk_micro_move: cell -> mark -> micro_move.

(* an ordered pair of cells, inner first outer second *)
Inductive position: Set :=
   | mk_position: cell -> cell -> position.

Definition mark_to_partial_position (mv: micro_move): option (cell -> position) :=
  match mv with
      | mk_micro_move pos B => Some (mk_position pos)
      | _ => None
  end.

Definition intelligent_player_get_options_macro (brd: macro_board): list (cell -> position) :=
  nil.

Definition intelligent_player_get_options_micro (brd: board): list (cell -> position) :=
  match brd with
      | mk_board 
          m00 m01 m02
          m10 m11 m12
          m20 m21 m22 => 
        (map
           (fun (o: option (cell -> position)) => 
              match o with 
                  | Some f => f
                  (* better to avoid this case? *)
                  | None => (mk_position C11)
              end)
           (filter 
              (fun (o: option (cell -> position)) => 
                 match o with 
                   | Some f => true 
                   | None => false 
                 end)
              (map mark_to_partial_position
                   [(mk_micro_move C00 m00); (mk_micro_move C01 m01); (mk_micro_move C02 m02); 
                    (mk_micro_move C10 m10); (mk_micro_move C11 m11); (mk_micro_move C12 m12); 
                    (mk_micro_move C20 m20); (mk_micro_move C21 m21); (mk_micro_move C22 m22)])))
  end.

Definition intelligent_player_get_options (brd: polyboard): list (cell -> position) :=
  match brd with
      | macro macro_board => 
        intelligent_player_get_options_macro macro_board
      | micro micro_board => 
        intelligent_player_get_options_micro micro_board
  end.

Definition intelligent_player_evaluate_options (brd: macro_board) (options: list move): move :=
  match options with
      | nil => mk_move C11 C11 X (* bad? *)
      | h::t => h (* todo fixme *)
  end.

(* if the player gets to choose macro_board cell *)
Definition intelligent_player_optimal_move_unrestrained 
           (brd: macro_board)
           (mk: mark): move:=
  mk_move C00 C00 X.

(* if the player has no choice of macro_board cell *)
Definition intelligent_player_optimal_move_restrained
           (macro_brd: macro_board)
           (pos: cell)
           (mk: mark): move:= 
  let options := 
      (map
         (fun (f: (cell -> position)) => 
            match (f pos) with 
              | mk_position c_inner c_outer => (mk_move c_outer c_inner mk)                
            end
         )
         (intelligent_player_get_options 
            (micro (get_board macro_brd pos)))) in
  (intelligent_player_evaluate_options macro_brd options).

Definition intelligent_player (brd: macro_board) (last_mv: move): move :=
  let mk := match last_mv with
              | first_move => X
              | mk_move _ _ last_mk => other_mark last_mk
            end
  in
  match last_mv with
    | first_move => (intelligent_player_optimal_move_unrestrained brd mk)
    | mk_move _ c2 _ => (intelligent_player_optimal_move_restrained brd c2 mk)
  end.

