(* COMMENT OUT after debugging *)
(*
Require Import "../types".
Require Import "../game".
Require Import List.
Import ListNotations.
*)
Fixpoint flatten {X: Type} (l: list (list X)): list X:=
  match l with
      | nil => []
      | h::t => h ++ flatten t
  end.       
Arguments flatten {X} _.

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

Definition intelligent_player_get_options_micro (brd: board)(pos: cell): list position :=
  (* redundancy? *)
  match evaluate_board brd with
    | incomplete =>   
      let options:= match brd with
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
                    end in
      (map (fun (pp: cell->position) => pp pos) options)
    | _ => []
  end.

Definition intelligent_player_get_options_macro (brd: macro_board): list position :=
  let cells:= [C00;C01;C02;C10;C11;C12;C20;C21;C22] in  
  (flatten (map (fun (c: cell) => (intelligent_player_get_options_micro (get_board brd c) c)) cells)).

Definition intelligent_player_get_options (brd: polyboard)(mk: mark)(pos: cell): list move:=
  (map
     (fun (p: position) => 
        match p with 
            | mk_position inner outer => mk_move outer inner mk
        end)
     (match brd with
        | macro macro_board => 
          intelligent_player_get_options_macro macro_board
        | micro micro_board => 
          intelligent_player_get_options_micro micro_board pos
      end)).

Definition intelligent_player_evaluate_options (brd: macro_board) (options: list move): move :=
  match options with
      | nil => mk_move C11 C11 X (* bad? *)
      | h::t => h (* todo fixme *)
  end.

(* if the player gets to choose macro_board cell *)
Definition intelligent_player_optimal_move_unrestrained 
           (brd: macro_board)
           (mk: mark): move:=
  let options:=       
      (intelligent_player_get_options (macro brd) mk C00)
  in (intelligent_player_evaluate_options brd options).

(* if the player has no choice of macro_board cell *)
Definition intelligent_player_optimal_move_restrained
           (macro_brd: macro_board)
           (pos: cell)
           (mk: mark): move:= 
  let options := (intelligent_player_get_options 
                    (micro (get_board macro_brd pos)) mk pos) in
  (intelligent_player_evaluate_options macro_brd options).

Definition intelligent_player (brd: macro_board) (last_mv: move): move :=
  let mk := match last_mv with
              | first_move => X
              | mk_move _ _ last_mk => other_mark last_mk
            end
  in
  match last_mv with
    | first_move => (intelligent_player_optimal_move_unrestrained brd mk)
    | mk_move _ c2 _ => match (evaluate_board (get_board brd c2)) with
                            | malformed => first_move
                            | incomplete => (intelligent_player_optimal_move_restrained brd c2 mk)
                            | tie | Xwins | Owins => (intelligent_player_optimal_move_unrestrained brd mk)
                        end
  end.

