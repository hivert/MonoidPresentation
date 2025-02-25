(** Presentation isomorphism certificate / To be extracted from James database *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Proof that the entry and final presentations define the same monoid.
   Warning: this is an effective result, containing the data of the isomorphism,
   hence the Defined. *)
Section RewriteProofs.

Variables A : choiceType.

Record cquad : Type := CQuad {
  cpre : word A;
  crel1 : word A;
  crel2 : word A;
  csuf : word A;
}.

Definition rew_cert := seq cquad.

Definition wf_cquad (R : relat A) (c : cquad) :=
  (crel1 c, crel2 c) \in undirected R.

Definition cquad_rel (c1 c2 : cquad) :=
  cpre c1 ++ crel2 c1 ++ csuf c1 == cpre c2 ++ crel1 c2 ++ csuf c2.

Definition wf_rew_cert (R : relat A) (c : cquad) (prf : rew_cert):=
  path cquad_rel c prf.

Definition init_cquad (u : word A) := CQuad [::] [::] u [::].
Definition end_cquad  (u : word A) := CQuad [::] u [::] [::].

Definition check_rew_cert (R : relat A) (u v : word A) (prf : rew_cert) :=
  (all (wf_cquad R) prf)
  && (wf_rew_cert R (init_cquad u) (rcons prf (end_cquad v))).

Lemma check_certP (R : relat A) (u v : word A) (prf : rew_cert) :
  check_rew_cert R u v prf -> u = v %[mod R].
Proof.
elim: prf u => [| c prf ihprf] u /=.
- case/andP=> /= _; rewrite andbT => /eqP /=; rewrite !cats0 => ->.
  exact: rewrites_to_refl.
case/andP=> /= /andP[wfc hall] /andP[] /eqP /=; rewrite cats0 => e hwf.
pose u1 := cpre c ++ crel2 c ++ csuf c.
have t1 : u = u1 %[mod R].
  rewrite e /u1. apply: rewrites_to_stable; apply: rewrites_to1.
  exact: rewrites_rel.
apply: rewrites_to_trans t1 _.
apply: ihprf; rewrite /check_rew_cert hall /=.
case: prf hwf {hall} => [| c1 prf]/=.
- by rewrite andbT /cquad_rel /= !cats0 andbT //.
case/andP=> hcc1 ->; rewrite andbT.
by move: hcc1; rewrite /cquad_rel /= !cats0 => /eqP<-.
Qed.


Inductive transfo : Type :=
  | rm_rel : nat -> rew_cert -> transfo
  | add_rel : word A -> word A -> rew_cert -> transfo
  | add_gen : A -> word A -> transfo.
  (* | rm_gen : nat -> A -> word A -> transfo
     | perm_transf ??? *)

Definition pres_cert := seq transfo.

Definition pres_transfo (p : pres A) (t : transfo) : pres A.
Admitted.

Fixpoint pres_of_cert (init_pres : pres A) (cert : pres_cert) :=
  if cert is t :: cert' then
    pres_of_cert (pres_transfo init_pres t) cert'
  else init_pres.

Definition wf_cert : pres A -> pres A -> pres_cert -> bool.
Admitted.

Definition image_of_cert (p1 p2 : pres A) (c : pres_cert) : seq (word A).
Admitted.

Theorem isopres_of_cert (p1 p2 : pres A) (c : pres_cert) :
  wf_cert p1 p2 c -> isopres p1 p2.
Admitted.

Definition morph_of_cert (p1 p2 : pres A) (c : pres_cert) :
  wf_cert p1 p2 c -> {presmorph p1 -> p2}.
Admitted.

Theorem morph_correct p1 p2 c (wfc : wf_cert p1 p2 c) :
  morph_of_cert wfc = isopres_of_cert wfc.
Admitted.

