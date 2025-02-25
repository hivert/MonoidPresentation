From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter cool : False.

(* A sample of formalized page of the encyclopaedia of 1-relation of monoid
   presentations. *)


(* Presentation entry, in this case <a, b | babaabaa = abaaabaaa>. *)
Definition present_entry := @Pres _ [::0; 1]
    [:: ([:: 1; 0; 1; 0; 0; 1; 0; 0], [::0; 1; 0; 0; 0; 1; 0; 0; 0])]
    erefl erefl.

(* Candidate alternate presentation, this time with three generators *)
Definition present_final := @Pres _ [:: 0; 1; 2]
    [:: ([:: 1; 0; 0; 0], [:: 2]);
        ([:: 1; 0; 1; 0; 0; 2], [:: 0; 2; 2; 0]);
        ([:: 1; 0; 1; 0; 0; 1; 0; 0], [:: 0; 2; 2])] erefl erefl.


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

Definition wf_cert (R : relat A) (c : cquad) (prf : rew_cert):=
  path cquad_rel c prf.

Definition init_cquad (u : word A) := CQuad [::] [::] u [::].
Definition end_cquad  (u : word A) := CQuad [::] u [::] [::].

Definition check_cert (R : relat A) (u v : word A) (prf : rew_cert) :=
  (all (wf_cquad R) prf)  && (wf_cert R (init_cquad u) (rcons prf (end_cquad v))).

Lemma check_certP (R : relat A) (u v : word A) (prf : rew_cert) :
  check_cert R u v prf -> u = v %[mod R].
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
apply: ihprf; rewrite /check_cert hall /=.
case: prf hwf {hall} => [| c1 prf]/=.
- by rewrite andbT /cquad_rel /= !cats0 andbT //.
case/andP=> hcc1 ->; rewrite andbT.
by move: hcc1; rewrite /cquad_rel /= !cats0 => /eqP<-.
Qed.

End RewriteProofs.


Theorem present_equiv :  isopres present_entry present_final.
Proof.
pose p0 := present_entry.
pose p1 := @Pres _ [::0; 1; 2]
  [:: ([:: 1; 0; 1; 0; 0; 1; 0; 0], [:: 0; 1; 0; 0; 0; 1; 0; 0; 0]);
      ([:: 2], [:: 1; 0; 0; 0])] erefl erefl.
have step_0 : isopres p0 p1.
  exact: (@Tietze_add_gen _ _ _ 2 [:: 1; 0; 0; 0]).
apply: isopres_trans step_0 _.
pose p2 := @Pres _ [:: 0; 1; 2]
  [:: ([:: 1; 0; 1; 0; 0; 1; 0; 0], [:: 0; 1; 0; 0; 0; 1; 0; 0; 0]);
      ([:: 2], [:: 1; 0; 0; 0]);
      ([:: 1; 0; 1; 0; 0; 2], [:: 0; 2; 2; 0])] erefl erefl.
have step_1 : isopres p1 p2.
  apply: (@Tietze_add_rel _ _ _ [:: 1; 0; 1; 0; 0; 2] [:: 0; 2; 2; 0]) => //.
  pose prf : rew_cert nat :=
    [:: CQuad [:: 1; 0; 1; 0; 0] [:: 2] [:: 1; 0; 0; 0] [:: ];
        CQuad [:: ] [:: 1; 0; 1; 0; 0; 1; 0; 0] [:: 0; 1; 0; 0; 0; 1; 0; 0; 0] [:: 0];
        CQuad [:: 0] [:: 1; 0; 0; 0] [:: 2] [:: 1; 0; 0; 0; 0];
        CQuad [:: 0; 2] [:: 1; 0; 0; 0] [:: 2] [:: 0]].
  exact: (check_certP (prf := prf)).
apply: isopres_trans step_1 _.


pose p3 := @Pres _ [::0; 1; 2]
[::
([:: 2], [:: 1; 0; 0; 0]);
([:: 1; 0; 1; 0; 0; 2], [:: 0; 2; 2; 0])] erefl erefl.
have step_1 : isopres p2 p3.
Admitted.
(* Step 0*)


Corollary equiv_equal u v :
(u = v %[mod present_entry]) <-> (present_equiv u = present_equiv v %[mod present_final_1]).
Proof. admit. Admitted.

(* Proof that the presentation is terminating + confluent. *)
Theorem final_1_ok : convergent present_final_1.
Proof. exact: (check_convergence_natP (fuel := 5)). Qed.

(* The word problem is hence decidable in this monoid. *)
Theorem decidable_entry : True.
Proof. done. Qed.

(* To be implemented combining norfuel and termination somehow *)
Parameter normalize : seq nat -> seq nat.

Definition test_eq_entry u v :=
    (normalize (present_equiv u)) == normalize (present_equiv v).

(* And now we provide a formally verified equality test for this monoid. *)
Theorem test_eqP u v :
reflect (u = v %[mod present_entry]) (test_eq_entry u v).
Proof. admit. Admitted.

(* Now users can test (dis)equalities and get a formal proof of the result
 *)


 (* And now an optimized variant: implement a test_eq_opt and prove that it is
   pointwise equal to tes_eq *)


(***** END ******)

Goal ([:: 1; 2; 2] < [:: 2; 2; 1])%O. by []. Qed.
Goal ~~ ([:: 2; 2] < [:: 1])%O. by []. Qed.
Goal ~~ ([:: 1; 2; 2] < [:: 2; 2])%O. by []. Qed.

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]); ([:: 1], [:: 0])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]);
                             ([:: 1], [:: 0]);
                             ([:: 2; 1; 2], [::])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Definition present_page_3_1 :=
  [::
   ([:: 2; 1; 1], [:: 1; 1; 2; 1]);
   ([:: 1; 2], [:: 3]);
   ([:: 2; 1], [:: 4]);
   ([:: 1; 3], [:: 5]);
   ([:: 1; 4], [:: 3; 1]);
   ([:: 2; 3], [:: 4; 2]);
   ([:: 2; 5], [:: 5; 3])].



Goal not (correctpres present_page_3_1 (geq 3)). by []. Qed.
Goal not (correctpres present_page_3_1 (geq 4)). by []. Qed.
Goal correctpres present_page_3_1 (geq 5). by []. Qed.
Goal correctpres present_page_3_1 (geq 6). by []. Qed.


Lemma step_3_1 : [:: 2; 5] = [:: 5; 3] %[mod present_page_3_1].
Proof.
by exists [::
        [:: 2; 1; 3];
        [:: 2; 1; 1; 2];
        [:: 1; 1; 2; 1; 2];
        [:: 1; 3; 1; 2];
        [:: 5; 1; 2];
        [:: 5; 3]].
Qed.

Eval vm_compute in norfuel present_page_3_1 10 [:: 2; 5].

Eval vm_compute in all_spairs present_page_3_1.
Eval vm_compute in all_npairs present_page_3_1.
