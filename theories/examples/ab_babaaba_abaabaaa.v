(* This file extract the proof of a presentation from the checked database *)
Require Import database_dec CompleteRewritingSystem_batch013_dec.

Definition P :=
  make_pres [::0;1] [:: ([::1;0;1;0;0;1;0;0], [::0;1;0;0;0;1;0;0;0])].

Theorem P_dec : WPdecidable P.
Proof. exact: CompleteRewritingSystem_batch013_dec.all_pres_dec. Qed.



