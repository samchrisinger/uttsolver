module Game where

import qualified Prelude

data Bool =
   True
 | False

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data List a =
   Nil
 | Cons a (List a)

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False ->
    case b2 of {
     True -> False;
     False -> True}}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

data Mark =
   B
 | X
 | O

mark_eq :: Mark -> Mark -> Bool
mark_eq m1 m2 =
  case m1 of {
   B ->
    case m2 of {
     B -> True;
     _ -> False};
   X ->
    case m2 of {
     X -> True;
     _ -> False};
   O ->
    case m2 of {
     O -> True;
     _ -> False}}

data Board =
   Mk_board Mark Mark Mark Mark Mark Mark Mark Mark Mark

data Macro_board =
   Mk_macro_board Board Board Board Board Board Board Board Board Board

data Cell =
   C00
 | C01
 | C02
 | C10
 | C11
 | C12
 | C20
 | C21
 | C22

cell_equal :: Cell -> Cell -> Bool
cell_equal c1 c2 =
  case c1 of {
   C00 ->
    case c2 of {
     C00 -> True;
     _ -> False};
   C01 ->
    case c2 of {
     C01 -> True;
     _ -> False};
   C02 ->
    case c2 of {
     C02 -> True;
     _ -> False};
   C10 ->
    case c2 of {
     C10 -> True;
     _ -> False};
   C11 ->
    case c2 of {
     C11 -> True;
     _ -> False};
   C12 ->
    case c2 of {
     C12 -> True;
     _ -> False};
   C20 ->
    case c2 of {
     C20 -> True;
     _ -> False};
   C21 ->
    case c2 of {
     C21 -> True;
     _ -> False};
   C22 ->
    case c2 of {
     C22 -> True;
     _ -> False}}

empty_board :: Board
empty_board =
  Mk_board B B B B B B B B B

lift_list_to_board :: (List Mark) -> Board
lift_list_to_board l =
  case l of {
   Nil -> empty_board;
   Cons x1 l0 ->
    case l0 of {
     Nil -> empty_board;
     Cons x2 l1 ->
      case l1 of {
       Nil -> empty_board;
       Cons x3 l2 ->
        case l2 of {
         Nil -> empty_board;
         Cons x4 l3 ->
          case l3 of {
           Nil -> empty_board;
           Cons x5 l4 ->
            case l4 of {
             Nil -> empty_board;
             Cons x6 l5 ->
              case l5 of {
               Nil -> empty_board;
               Cons x7 l6 ->
                case l6 of {
                 Nil -> empty_board;
                 Cons x8 l7 ->
                  case l7 of {
                   Nil -> empty_board;
                   Cons x9 l8 ->
                    case l8 of {
                     Nil -> Mk_board x1 x2 x3 x4 x5 x6 x7 x8 x9;
                     Cons m l9 -> empty_board}}}}}}}}}}

empty_macro_board :: Macro_board
empty_macro_board =
  Mk_macro_board empty_board empty_board empty_board empty_board empty_board
    empty_board empty_board empty_board empty_board

data Move =
   Mk_move Cell Cell Mark
 | First_move

data Outcome =
   Xwins
 | Owins
 | Incomplete
 | Tie
 | Malformed

mark_board :: Board -> Mark -> Cell -> Board
mark_board brd mv c =
  case brd of {
   Mk_board e0 e1 e2 e3 e4 e5 e6 e7 e8 ->
    case c of {
     C00 -> Mk_board mv e1 e2 e3 e4 e5 e6 e7 e8;
     C01 -> Mk_board e0 mv e2 e3 e4 e5 e6 e7 e8;
     C02 -> Mk_board e0 e1 mv e3 e4 e5 e6 e7 e8;
     C10 -> Mk_board e0 e1 e2 mv e4 e5 e6 e7 e8;
     C11 -> Mk_board e0 e1 e2 e3 mv e5 e6 e7 e8;
     C12 -> Mk_board e0 e1 e2 e3 e4 mv e6 e7 e8;
     C20 -> Mk_board e0 e1 e2 e3 e4 e5 mv e7 e8;
     C21 -> Mk_board e0 e1 e2 e3 e4 e5 e6 mv e8;
     C22 -> Mk_board e0 e1 e2 e3 e4 e5 e6 e7 mv}}

convert :: Outcome -> Mark
convert o =
  case o of {
   Xwins -> X;
   Owins -> O;
   _ -> B}

in_list :: a1 -> (List a1) -> (a1 -> a1 -> Bool) -> Bool
in_list x l equality =
  case l of {
   Nil -> False;
   Cons h t -> equality h x}

match_marks :: (List Mark) -> Bool
match_marks l =
  case l of {
   Nil -> False;
   Cons m l0 ->
    case m of {
     B -> False;
     X ->
      case l0 of {
       Nil -> False;
       Cons m0 l1 ->
        case m0 of {
         X ->
          case l1 of {
           Nil -> False;
           Cons m1 l2 ->
            case m1 of {
             X ->
              case l2 of {
               Nil -> True;
               Cons m2 l3 -> False};
             _ -> False}};
         _ -> False}};
     O ->
      case l0 of {
       Nil -> False;
       Cons m0 l1 ->
        case m0 of {
         O ->
          case l1 of {
           Nil -> False;
           Cons m1 l2 ->
            case m1 of {
             O ->
              case l2 of {
               Nil -> True;
               Cons m2 l3 -> False};
             _ -> False}};
         _ -> False}}}}

match_mark :: Board -> Mark -> Bool
match_mark brd mk =
  case brd of {
   Mk_board m1 m2 m3 m4 m5 m6 m7 m8 m9 ->
    in_list True
      (map match_marks (Cons (Cons m1 (Cons m2 (Cons m3 Nil))) (Cons (Cons m4
        (Cons m5 (Cons m6 Nil))) (Cons (Cons m7 (Cons m8 (Cons m9 Nil)))
        (Cons (Cons m1 (Cons m4 (Cons m7 Nil))) (Cons (Cons m2 (Cons m5 (Cons
        m8 Nil))) (Cons (Cons m3 (Cons m6 (Cons m9 Nil))) (Cons (Cons m1
        (Cons m2 (Cons m3 Nil))) (Cons (Cons m4 (Cons m5 (Cons m6 Nil)))
        Nil))))))))) eqb}

has_blanks :: Board -> Bool
has_blanks brd =
  case brd of {
   Mk_board m1 m2 m3 m4 m5 m6 m7 m8 m9 ->
    in_list B (Cons m1 (Cons m2 (Cons m3 (Cons m4 (Cons m5 (Cons m6 (Cons m7
      (Cons m8 (Cons m9 Nil))))))))) mark_eq}

evaluate_board :: Board -> Outcome
evaluate_board brd =
  case match_mark brd X of {
   True -> Xwins;
   False ->
    case match_mark brd O of {
     True -> Owins;
     False ->
      case has_blanks brd of {
       True -> Incomplete;
       False -> Tie}}}

evaluate_boards :: (List Board) -> List Outcome
evaluate_boards l =
  map evaluate_board l

evaluate_macro_board :: Macro_board -> Outcome
evaluate_macro_board b =
  case b of {
   Mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 b22 ->
    evaluate_board
      (lift_list_to_board
        (map convert
          (evaluate_boards (Cons b00 (Cons b01 (Cons b02 (Cons b10 (Cons b11
            (Cons b12 (Cons b20 (Cons b21 (Cons b22 Nil))))))))))))}

get_board :: Macro_board -> Cell -> Board
get_board b c =
  case b of {
   Mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 b22 ->
    case c of {
     C00 -> b00;
     C01 -> b01;
     C02 -> b02;
     C10 -> b10;
     C11 -> b11;
     C12 -> b12;
     C20 -> b20;
     C21 -> b21;
     C22 -> b22}}

update_macro_board :: Macro_board -> Cell -> Board -> Macro_board
update_macro_board b c brd =
  case b of {
   Mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 b22 ->
    case c of {
     C00 -> Mk_macro_board brd b01 b02 b10 b11 b12 b20 b21 b22;
     C01 -> Mk_macro_board b00 brd b02 b10 b11 b12 b20 b21 b22;
     C02 -> Mk_macro_board b00 b01 brd b10 b11 b12 b20 b21 b22;
     C10 -> Mk_macro_board b00 b01 b02 brd b11 b12 b20 b21 b22;
     C11 -> Mk_macro_board b00 b01 b02 b10 brd b12 b20 b21 b22;
     C12 -> Mk_macro_board b00 b01 b02 b10 b11 brd b20 b21 b22;
     C20 -> Mk_macro_board b00 b01 b02 b10 b11 b12 brd b21 b22;
     C21 -> Mk_macro_board b00 b01 b02 b10 b11 b12 b20 brd b22;
     C22 -> Mk_macro_board b00 b01 b02 b10 b11 b12 b20 b21 brd}}

mark_macro_board :: Macro_board -> Move -> Macro_board
mark_macro_board b mv =
  case mv of {
   Mk_move c1 c2 mk ->
    update_macro_board b c1 (mark_board (get_board b c1) mk c2);
   First_move -> b}

valid :: Board -> Move -> Bool
valid b mv =
  True

macro_valid :: Macro_board -> Move -> Move -> Bool
macro_valid b mv last_move =
  case mv of {
   Mk_move c1 c2 mk ->
    case last_move of {
     Mk_move c1' c2' mk' ->
      case evaluate_board (get_board b c1) of {
       Incomplete ->
        case negb
               (orb (cell_equal c1 c2')
                 (case evaluate_board (get_board b c2') of {
                   Incomplete -> True;
                   _ -> False})) of {
         True -> False;
         False -> valid (get_board b c1) mv};
       _ -> False};
     First_move -> True};
   First_move ->
    case last_move of {
     Mk_move c c0 m -> False;
     First_move -> True}}

doPlayGame :: Macro_board -> (List Move) -> Move -> Outcome
doPlayGame b l last_move =
  case l of {
   Nil -> evaluate_macro_board b;
   Cons h t ->
    case negb (macro_valid b h last_move) of {
     True -> Malformed;
     False ->
      let {b2 = mark_macro_board b h} in
      case evaluate_macro_board b2 of {
       Incomplete -> doPlayGame b2 t h;
       x -> x}}}

playGame :: (List Move) -> Outcome
playGame l =
  doPlayGame empty_macro_board l First_move

