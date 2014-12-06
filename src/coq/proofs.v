Require Import game.
Require Import types.

Theorem naive_player_Owins: playGameWithPlayers naive_player = Owins.
Proof. reflexivity. Qed.