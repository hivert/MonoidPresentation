(* This file extract the proof of a presentation from the checked database *)
From mathcomp Require Import eqtype.
Require Import database_dec CompleteRewritingSystem_batch013_dec.

Definition P :=
  make_pres [::1;0] [:: ([::1;0;1;0;0;1;0;0], [::0;1;0;0;0;1;0;0;0])].

Theorem P_dec : WPdecidable P.
Proof.
have : P \in CompleteRewritingSystem_batch013_pres.all_pres by [].
exact: CompleteRewritingSystem_batch013_dec.all_pres_dec.
Qed.



