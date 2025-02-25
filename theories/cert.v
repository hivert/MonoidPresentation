(** Presentation isomorphism certificate / To be extracted from James database *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma perm_eq_move_to_end (T : eqType) (x0 : T) (s : seq T) (n : nat) :
  n < size s ->  perm_eq (rcons (take n s ++ drop n.+1 s) (nth x0 s n)) s.
Proof.
move=> ltnsz.
rewrite -cats1 -catA -[X in perm_eq _ X](cat_take_drop n s) perm_cat2l perm_catC.
by rewrite [X in perm_eq _ X](drop_nth x0).
Qed.


(* Proof that the entry and final presentations define the same monoid.
   Warning: this is an effective result, containing the data of the isomorphism,
   hence the Defined. *)
Section Certificate.

Variables A : choiceType.

Section RewriteProofs.

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

End RewriteProofs.


Inductive transfo : Type :=
  | add_gen : A -> word A -> transfo
  | add_rel : word A -> word A -> rew_cert -> transfo
  | rm_rel : nat -> rew_cert -> transfo.
  (* | rm_gen : nat -> A -> word A -> transfo
     | perm_transf ??? *)

Definition pres_cert := seq transfo.

Section Defs.

Section Transfo.

Variable (G : seq A) (R : relat A) (t : transfo).

Definition wf_transfo : bool :=
  match t with
  | add_gen g w => (g \notin G) && (all (mem G) w)
  | add_rel u v prf =>
      [&& all (mem G) u, all (mem G) v & check_rew_cert R u v prf]
  | rm_rel n prf =>
      (n < size R) &&
        let: (u, v) := nth ([::], [::]) R n in
        check_rew_cert (take n R ++ drop n.+1 R) u v prf
  end.
Definition gen_transfo : seq A :=
  match t with
  | add_gen g w => rcons G g
  | _ => G
  end.
Definition rel_transfo : relat A :=
  match t with
  | add_gen g w => rcons R ([:: g], w)
  | add_rel u v prf => rcons R (u, v)
  | rm_rel n prf => take n R ++ drop n.+1 R
  end.

End Transfo.

Variable (R : pres A) (t : transfo) (wft : wf_transfo (pgen R) (prelat R) t).

Lemma uniq_gen_transfo : uniq (gen_transfo (pgen R) t).
Proof.
case: t wft.
- by move=> g w /andP[gok _]; apply: Tietze2_gen_uniq.
- by move=> u v /= _ _; case: R.
- by move=> n /= _ _; case: R.
Qed.
Lemma correct_rel_transfo :
  correctrelat (rel_transfo (prelat R) t) (mem (gen_transfo (pgen R) t)).
Proof.
case: t wft.
- by move=> g w /andP[gok win]; apply: Tietze2_wf_relat.
- move=> u v prf /and3P[uin vin /check_certP eq_u_v].
  exact: wf_rcons_ext_pres.
- move=> n prf _; case: R => gens rels /= _.
  rewrite /correctrelat /= all_cat => /allP /= allok.
  apply/andP; split; apply/allP => /= p pin; apply allok.
  + exact: mem_take pin.
  + exact: mem_drop pin.
Qed.
Definition pres_transfo := Pres uniq_gen_transfo correct_rel_transfo.

End Defs.

Theorem isopres_transfo (R : pres A) (t : transfo)
  (prf : wf_transfo (pgen R) (prelat R) t) :
  isopres R (pres_transfo prf).
Proof.
case: t prf => /=.
- move=> g w /[dup] /andP[gok win] prf /=.
  apply: (isopres_trans (isopres_Tietze2 win gok)).
  exact: pres_irrelevance.
- move=> u v prf /[dup] /and3P[uin vin /check_certP eq_u_v] tok.
  apply: (isopres_trans (isopres_rcons_rule uin vin eq_u_v)).
  exact: pres_irrelevance.
- move=> n prf /[dup] /andP[lt_n_sz].
  case Huv : {1}(nth ([::], [::]) (prelat R) n) => [u v] /check_certP eq_u_v prf0.
  set newpres := pres_transfo _.
  have [uin vin]: u \in words_of newpres /\ v \in words_of newpres.
    have eq_words_of : words_of newpres = words_of R by [].
    have {lt_n_sz} : (u, v) \in prelat R by rewrite -Huv; apply: mem_nth.
    rewrite eq_words_of /words_of; case R => gens rels /= _.
    by rewrite /correctrelat !inE => /allP /= /[apply] /= /andP[-> ->].
  apply: isopres_sym.
  apply: (isopres_trans (isopres_rcons_rule uin vin eq_u_v)).
  apply: pres_irrelevance_perm_eq => //=.
  rewrite -{eq_u_v prf0 newpres uin vin u v}Huv.
  exact: perm_eq_move_to_end.
Qed.

Implicit Types (R : pres A) (c : pres_cert) (t : transfo).

Fixpoint gen_cert (gens : seq A) (c : pres_cert) :=
  if c is t :: c' then gen_cert (gen_transfo gens t) c' else gens.
Fixpoint rel_cert (rels : relat A) (c : pres_cert) :=
  if c is t :: c' then rel_cert (rel_transfo rels t) c' else rels.
Fixpoint wf_cert (gens : seq A) (rels : relat A) (c : pres_cert) :=
  if c is t :: c' then
    (wf_transfo gens rels t) &&
      (wf_cert (gen_transfo gens t) (rel_transfo rels t) c')
  else true.

Definition wfpres_cert R c := wf_cert (pgen R) (prelat R) c.

Lemma pres_certP R c (wfc : wfpres_cert R c) :
  { Res : pres A |
    pgen Res = gen_cert (pgen R) c /\ prelat Res = rel_cert (prelat R) c }.
Proof.
elim: c R wfc => [R _ | t c IHc R /= /andP[wft wfc]]; first by exists R.
pose R1 := pres_transfo wft; move: wfc.
have <- : pgen R1 = gen_transfo (pgen R) t by [].
have <- : prelat R1 = rel_transfo (prelat R) t by [].
exact: IHc.
Qed.

Definition final_pres R c (wfc : wfpres_cert R c) :=
  let: exist Res _ := pres_certP wfc in Res.

Lemma pgen_final_pres R c (wfc : wfpres_cert R c) :
  pgen (final_pres wfc) = gen_cert (pgen R) c.
Proof. by rewrite /final_pres; case: (pres_certP wfc) => /= Res []. Qed.
Lemma prelat_final_pres R c (wfc : wfpres_cert R c) :
  prelat (final_pres wfc) = rel_cert (prelat R) c.
Proof. by rewrite /final_pres; case: (pres_certP wfc) => /= Res []. Qed.

Theorem iso_final_pres R c (wfc : wfpres_cert R c) :  isopres R (final_pres wfc).
Proof.
rewrite /final_pres; elim: c R wfc => [| t c IHc] R /= wf.
  by apply: pres_irrelevance; rewrite ?pgen_final_pres ?prelat_final_pres.
have:= wf => /andP[wft wfc].
apply: (isopres_trans (isopres_transfo wft)).
set R1 := pres_transfo wft.
have genR1 : pgen R1 = gen_transfo (pgen R) t by [].
have relR1 : prelat R1 = rel_transfo (prelat R) t by [].
move: wfc; rewrite -{1}genR1 -{1}relR1 => wfcR1.
apply: (isopres_trans (IHc R1 wfcR1)).
apply: pres_irrelevance => //=.
  by rewrite !pgen_final_pres genR1.
by rewrite !prelat_final_pres relR1.
Qed.

End Certificate.

Definition present_entry := @Pres _ [::1; 0]
    [:: ([:: 1; 0; 1; 0; 0; 1; 0; 0], [::0; 1; 0; 0; 0; 1; 0; 0; 0])]
    erefl erefl.

Definition present_final := @Pres _ [:: 1; 0; 2]
    [:: ( [:: 2], [:: 1; 0; 0; 0]);
        ([:: 1; 0; 1; 0; 0; 2], [:: 0; 2; 2; 0]);
        ([:: 1; 0; 1; 0; 0; 1; 0; 0], [:: 0; 2; 2])] erefl erefl.

Definition cert : pres_cert nat := [::
  add_gen 2 [:: 1; 0; 0; 0];
  add_rel [:: 1; 0; 1; 0; 0; 2] [:: 0; 2; 2; 0]
    [:: CQuad [:: 1; 0; 1; 0; 0] [:: 2] [:: 1; 0; 0; 0] [:: ];
        CQuad [:: ] [:: 1; 0; 1; 0; 0; 1; 0; 0] [:: 0; 1; 0; 0; 0; 1; 0; 0; 0] [:: 0];
        CQuad [:: 0] [:: 1; 0; 0; 0] [:: 2] [:: 1; 0; 0; 0; 0];
        CQuad [:: 0; 2] [:: 1; 0; 0; 0] [:: 2] [:: 0]];
  add_rel [:: 1; 0; 1; 0; 0; 1; 0; 0] [:: 0; 2; 2]
    [:: CQuad [:: ] [:: 1; 0; 1; 0; 0; 1; 0; 0] [:: 0; 1; 0; 0; 0; 1; 0; 0; 0] [:: ];
        CQuad [:: 0] [:: 1; 0; 0; 0] [:: 2] [:: 1; 0; 0; 0];
        CQuad [:: 0; 2] [:: 1; 0; 0; 0] [:: 2] [:: ]];
  rm_rel 0
    [:: CQuad [:: ] [:: 1; 0; 1; 0; 0; 1; 0; 0] [:: 0; 2; 2] [:: ];
        CQuad [:: 0] [:: 2] [:: 1; 0; 0; 0] [:: 2];
        CQuad [:: 0; 1; 0; 0; 0] [:: 2] [:: 1; 0; 0; 0] [:: ]]
].

Theorem isopres_final : isopres present_entry present_final.
Proof.
apply: (isopres_trans (@iso_final_pres _ present_entry cert is_true_true)).
apply: pres_irrelevance.
  by rewrite pgen_final_pres.
by rewrite prelat_final_pres.
Qed.


Definition image_of_cert (p1 p2 : pres A) (c : pres_cert) : seq (word A).
Admitted.

Definition morph_of_cert (p1 p2 : pres A) (c : pres_cert) :
  wf_cert p1 p2 c -> {presmorph p1 -> p2}.
Admitted.

Theorem morph_correct p1 p2 c (wfc : wf_cert p1 p2 c) :
  morph_of_cert wfc = isopres_of_cert wfc.
Admitted.

