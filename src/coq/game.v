Require Import List.
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
Definition evaluate_board (brd: board): outcome :=
  match brd with
   | mk_board 
               X X X
               _ _ _
               _ _ _ => Xwins
   | mk_board 
               _ _ _
               X X X
               _ _ _ => Xwins
   | mk_board 
               _ _ _
               _ _ _
               X X X => Xwins
   | mk_board 
               X _ _
               X _ _
               X _ _ => Xwins
   | mk_board 
               _ X _
               _ X _
               _ X _ => Xwins
   | mk_board 
               _ _ X
               _ _ X
               _ _ X => Xwins
   | mk_board 
               X _ _
               _ X _
               _ _ X => Xwins
   | mk_board 
               _ _ X
               _ X _
               X _ _ => Xwins
   | mk_board 
              O O O
               _ _ _
               _ _ _ => Owins
   | mk_board 
               _ _ _
               O O O
               _ _ _ => Owins
   | mk_board 
               _ _ _
               _ _ _
               O O O => Owins
   | mk_board 
               O _ _
               O _ _
               O _ _ => Owins
   | mk_board 
               _ O _
               _ O _
               _ O _ => Owins
   | mk_board 
               _ _ O
               _ _ O
               _ _ O => Owins
   | mk_board 
               O _ _
               _ O _
               _ _ O => Owins
   | mk_board 
               _ _ O
               _ O _
               O _ _ => Owins
   | mk_board 
               B _ _
               _ _ _
               _ _ _ => incomplete
   | mk_board 
               _ B _
               _ _ _
               _ _ _ => incomplete
   | mk_board 
               _ _ B
               _ _ _
               _ _ _ => incomplete
   | mk_board 
               _ _ _
               B _ _
               _ _ _ => incomplete
   | mk_board 
               _ _ _
               _ B _
               _ _ _ => incomplete
   | mk_board 
               _ _ _
               _ _ B
               _ _ _ => incomplete
   | mk_board 
               _ _ _
               _ _ _
               B _ _ => incomplete
   | mk_board 
               _ _ _
               _ _ _
               _ B _ => incomplete
   | mk_board 
               _ _ _
               _ _ _
               _ _ B => incomplete             
   | mk_board 
               _ _ _
               _ _ _
               _ _ _ => tie
  end.


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


Definition mark_macro_board (b: macro_board) (mv: move) := 
  match mv with
    | mk_move c1 c2 mk => update_macro_board b c1 (mark_board (get_board b c1) mk c2)
    | first_move => b
  end.

Definition valid (b: board) (mv: move) := true.

Definition macro_valid (b: macro_board) (mv: move) (last_move: move) :=
  match mv, last_move with
    | mk_move c1 c2 mk, mk_move c1' c2' mk' =>
      match evaluate_board (get_board b c1) with
        | incomplete => 
            if negb (orb  (cell_equal c1 c2')
              match (evaluate_board (get_board b c2' )) with
                | incomplete => true
                | _ => false
              end)
                then false else valid (get_board b c1) mv
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


