(** * Normal forms of a convergent monoid presentation *)
(******************************************************************************)
(*      Copyright (C) 2025      Florent Hivert <florent.hivert@lri.fr>        *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq eqtype
  choice path bigop.

Require Import factor monoids present monpres.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** The monoid of normal forms of a convergent presentation *)
Section NormalFormMonoid.

Context {Alph : choiceType} (P : pres Alph).
Hypothesis convP : convergent P.

Definition normalword_of (u : word Alph) := (u \in words_of P) && (normal P u).

Structure norword := NorWord {
    nwval :> word Alph;
    _ : normalword_of nwval
  }.

HB.instance Definition _ := [isSub of norword for nwval].

Implicit Type (x y : norword).

Lemma norword_of x : (x : word Alph) \in words_of P.
Proof. by case: x => [x /= /andP[]]. Qed.
Lemma norwordP x : normal P x.
Proof. by case: x => [x /= /andP[]]. Qed.
Hint Resolve norword_of norwordP : core.


Fact normalword_of_onepm : normalword_of [::].
Proof. by rewrite /normalword_of /= (normal0 convP.2). Qed.
Definition onepm := NorWord normalword_of_onepm.

Let mk (u : word Alph) := normal_of convP.2 u.
Fact mkP u : u \in words_of P -> normalword_of (mk u).
Proof.
rewrite /mk /normalword_of normal_ofP andbT.
by rewrite (equiv_words_ofE (equiv_normal_of convP.2 u)).
Qed.

Let mulpmval x y : word Alph := mk ((x : word Alph) ++ (y : word Alph)).
Fact normalword_of_mulpm x y : normalword_of (mulpmval x y).
Proof.
rewrite /mulpmval; apply: mkP.
by rewrite words_of_cat !norword_of.
Qed.
Definition mulpm x y := NorWord (normalword_of_mulpm x y).

Fact mult1pm : left_id onepm mulpm.
Proof.
move=> x; apply val_inj => /=.
rewrite /mulpmval /=; apply (confluentE convP.1 (normalf_ofP convP.2 _)).
exact/normalf_rewrite0/norwordP.
Qed.
Fact multpm1 : right_id onepm mulpm.
Proof.
move=> x; apply val_inj => /=.
rewrite /mulpmval /=; apply (confluentE convP.1 (normalf_ofP convP.2 _)).
by rewrite cats0; exact/normalf_rewrite0/norwordP.
Qed.
Fact multpmA : associative mulpm.
Proof.
move=> x y z; apply val_inj => /=.
repeat rewrite /mulpmval /=.
by rewrite /mk normal_of_catl normal_of_catr catA.
Qed.
HB.instance Definition _ := [Choice of norword by <:].
HB.instance Definition _ := isMonoid.Build norword multpmA mult1pm multpm1.

Definition nword_monoid : monoidType := norword.

Definition mknormal u : nword_monoid :=
  if boolP (u \in words_of P) is AltTrue pf then NorWord (@mkP u pf)
  else onepm.
Lemma mknormalE u : u \in words_of P -> \val (mknormal u) = normal_of convP.2 u.
Proof. by rewrite /mknormal; case (boolP (u \in words_of P)). Qed.

Lemma mknormal_ofE u : normalword_of u -> \val (mknormal u) = u.
Proof.
by move=> /[dup] norwu /andP[uin noru]; rewrite mknormalE // normal_of_normal.
Qed.

End NormalFormMonoid.


(** nwordmonoid P is presented by P *)
Section Convergent.

Context {I: choiceType} (P : pres I) (convP : convergent P).

Let gen := [fun i : I => mknormal convP [:: i]].

Lemma univmor_mknormalE u :
  u \in words_of P -> univmor gen u = normal_of convP.2 u :> word I.
Proof.
elim: u => [_ | u0 u IHu  u0uin]/=.
  by rewrite univmor_nil normal_of_normal // (normal0 convP.2).
have [u0in uin] : ([:: u0] \in words_of P) /\ u \in words_of P.
  by move: u0uin; rewrite !unfold_in /= => /andP[-> ->].
rewrite univmor_cons /= {}IHu // -[in RHS]cat1s -[RHS]normal_of_cat /=.
by rewrite mknormalE.
Qed.
Lemma univmor_mknormal_ofE u :
  normalword_of P u -> univmor gen u = u :> word I.
Proof.
by case/andP=> uin unor; rewrite univmor_mknormalE ?normal_of_normal.
Qed.

Fact nword_monoid_genP m : exists2 w, w \in words_of P & univmor gen w = m.
Proof.
case: m => u /= noru; exists u; first by case/andP : noru.
by apply val_inj => /=; exact: univmor_mknormal_ofE.
Qed.
Fact nword_monoid_eq (u v : seq I) :
  u \in words_of P -> v \in words_of P ->
  (u = v %[mod P] <-> univmor gen u = univmor gen v).
Proof.
move=> uin vin; split => [Heq | /(congr1 val) /=].
  by apply: val_inj => /=; rewrite !univmor_mknormalE // -equiv_normal_ofE.
by rewrite (univmor_mknormalE uin) (univmor_mknormalE vin) -equiv_normal_ofE.
Qed.
Definition nword_monoid_present : P \present (nword_monoid convP) :=
  Presentation nword_monoid_genP nword_monoid_eq.

End Convergent.


(** TODO : use a Gilman graph here *)
Section EnumNormalForms.

Context {Alph : choiceType} (P : pres Alph).
Hypothesis convP : convergent P.
Variable rew1 : word Alph -> option (word Alph).
Hypothesis rew1P : rewrites1_Ok P rew1.

Implicit Types (u v w : word Alph) (norf : seq (word Alph)).

Definition normal_sz (n : nat) u := (size u == n) && (normalword_of P u).
Definition enum_normal_next norf :=
  [seq x <- [seq g :: w | g <- pgen P, w <- norf] | ~~ rew1 x].
Definition enum_normal_sz n := iter n enum_normal_next [:: [::]].

Lemma normal_sz0 : normal_sz 0 [::].
Proof. by rewrite /normal_sz /=; apply normal0; case: convP. Qed.

Lemma normal_sz_enum_normal_sz n : all (normal_sz n) (enum_normal_sz n).
Proof.
elim: n => [| n]; first by rewrite /= normal_sz0.
rewrite {2}/enum_normal_sz /= -/(enum_normal_sz n).
move: (enum_normal_sz n) => norf /allP /= allnorf; apply/allP => /= [[| u0 u]].
  by rewrite mem_filter => /andP[_ /allpairsP[[/= u0 u []]]].
rewrite mem_filter => /andP[]; case: rew1P => nrew // _.
case/allpairsP => /= - [v0 v]/= [ugen unor []] equ0 equ; subst v0 v.
have := allnorf u unor; rewrite /normal /= /normal_sz /= eqSS.
case: eqP => //= _; rewrite /normalword_of.
have -> : (u0 :: u \in words_of P) = (u \in words_of P).
  by rewrite !unfold_in /words_of /= ugen.
by case: (u \in _).
Qed.

Lemma count_mem_enum_normal_sz n u :
  normal_sz n u -> count_mem u (enum_normal_sz n) = 1%N.
Proof.
elim: n u => [|n]; first by case.
rewrite {2}/enum_normal_sz /= -/(enum_normal_sz n).
move: (enum_normal_sz n) => norf Hn [|u0 u] //=.
rewrite /normal_sz /= eqSS /normalword_of.
have -> : (u0 :: u \in words_of P) = (u0 \in pgen P) && (u \in words_of P).
  by rewrite !unfold_in /words_of /=.
case: (boolP (u0 \in pgen P)) => [u0P |]; rewrite ?andbF ?andbT //=.
rewrite /normal /= cat_eq0 map_eq0 -/(normal _ u) [X in [&& _, _ & X]]andbC.
rewrite !andbA andbC -!andbA -/(normal_sz n u) andbC.
case/andP => /[dup] unorf {}/Hn cunorf /eqP rew0.
rewrite count_filter /normal /= count_flatten sumnE 2!big_map.
rewrite (bigD1_seq _ u0P (uniq_pgen P)) /= big1_seq ?addn0; first last.
  move=> /= i /andP[/negbTE neq _].
  rewrite -count_filter; apply/count_memPn/negP.
  rewrite mem_filter => /andP[_ /mapP[/= x _ /eqP]].
  by rewrite eqseq_cons eq_sym neq.
rewrite count_map -[RHS]cunorf; apply eq_count => /= v /=.
rewrite eqseq_cons eqxx /=; case: eqP => //= {v}->.
case: rew1P => //= v; rewrite rew0 /= => /mapP[/= w + _].
by case/and3P: unorf => _ _ /eqP ->.
Qed.

Lemma uniq_enum_normal_sz n : uniq (enum_normal_sz n).
Proof.
have /allP /= allnorf := normal_sz_enum_normal_sz n.
apply: count_mem_uniq => /= u.
case: (boolP (u \in _)) => [/allnorf/count_mem_enum_normal_sz -> // | /= unotin].
exact/count_memPn.
Qed.

Lemma mem_enum_normalP n u : (u \in enum_normal_sz n) = normal_sz n u.
Proof.
have /allP /= allnorf := normal_sz_enum_normal_sz n.
case: (boolP (u \in _)) => [/allnorf -> // | /= unotin].
apply/esym; apply/contraNF: unotin => /count_mem_enum_normal_sz.
by rewrite -has_pred1 has_count => ->.
Qed.

Lemma enum_normal_sz_nil m n :
  m <= n -> enum_normal_sz m = [::] -> enum_normal_sz n = [::].
Proof.
elim: n m => [|n IHn] m; first by rewrite leqn0 => /eqP ->.
move=> /[swap] Hm.
rewrite leq_eqVlt ltnS => /orP[/eqP <-| /IHn /= ->] //.
by rewrite /enum_normal_next /=; elim: (pgen P).
Qed.

Lemma enum_normal_wordP n u :
  u \in flatten (traject enum_normal_next [:: [::]] n) -> normalword_of P u.
Proof.
case/flattenP => /= l /trajectP[m ltmn {l}->].
by rewrite /normalword_of mem_enum_normalP => /and3P[_ -> ->].
Qed.

Lemma enum_normalE n :
  enum_normal_sz n = [::] ->
  forall u, normalword_of P u =
              (u \in flatten (traject enum_normal_next [:: [::]] n)).
Proof.
move=> Hiter u.
apply/idP/idP; last exact: enum_normal_wordP.
case/andP => uin noru.
have {uin}noru : normal_sz (size u) u.
  by rewrite /normal_sz /normalword_of eqxx uin noru.
apply/flattenP => /=; exists (iter (size u) enum_normal_next [:: [::]]).
  apply/trajectP; exists (size u) => //.
  apply/negP => /negP; rewrite -leqNgt => /enum_normal_sz_nil eqnor.
  by rewrite -mem_enum_normalP eqnor in noru.
by rewrite mem_enum_normalP.
Qed.

(** Given a bound returns the list of normal forms of size less than bound
and a boolean certifying that list is complete *)
Definition enum_normal bound :=
  let l := traject enum_normal_next [:: [::]] bound in
  (flatten l, last [::[::]] l == [::]).
(** l is a complete list of normal forms for P *)
Definition is_enum_normal l :=
  uniq l /\ forall u, (normalword_of P u) = (u \in l).

Lemma enum_normal_uniq bound : uniq (enum_normal bound).1.
Proof.
rewrite /enum_normal; elim: bound => // n IHn.
rewrite trajectSr flatten_rcons cat_uniq {}IHn uniq_enum_normal_sz andbT /=.
apply/negP => /hasP[/= u]; rewrite mem_enum_normalP => /andP[/eqP szu _].
case/flattenP => /= l /trajectP[i ltin {l}->].
rewrite mem_enum_normalP => /andP[ + _].
by rewrite szu gtn_eqF.
Qed.

Lemma enum_normalP bound :
  let: (l, ok) := enum_normal bound in ok -> is_enum_normal l.
Proof.
move => /= H; split; first exact: enum_normal_uniq.
rewrite /enum_normal; case: bound H => [//| b].
rewrite {2}trajectSr /= last_traject => /eqP/[dup]/enum_normalE H ->.
by rewrite flatten_rcons cats0.
Qed.

End EnumNormalForms.


(** A map between normal forms of P and Q *)
Section IsoCan.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (isoPQ : isopres P Q)
  (Pconv : convergent P) (Qconv : convergent Q).

Definition isocan u := normal_of Qconv.2 (isoPQ u).
Lemma isocan_words_of w : w \in words_of P -> isocan w \in words_of Q.
Proof.
have [_ /rewrites_to_words_ofE <-] := normalf_ofP Qconv.2 (isoPQ w).
by move/(isopres_words_of isoPQ).
Qed.
Lemma isocanP u : normalf Q (isoPQ u) (isocan u).
Proof. exact: normalf_ofP. Qed.
Lemma normal_isocan u : normal Q (isocan u).
Proof. by have [] := isocanP u. Qed.
Lemma rewrites_to_isocan u : rewrites_to Q (isoPQ u) (isocan u).
Proof. by have [] := isocanP u. Qed.
Lemma equiv_isocan u : isoPQ u = isocan u %[mod Q].
Proof. exact/rewrites_to_equiv/rewrites_to_isocan. Qed.

End IsoCan.

(** isocan is a bijection between normal forms *)
Section IsoCanK.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (isoPQ : isopres P Q)
  (Pconv : convergent P) (Qconv : convergent Q).

Let P2Q := isocan isoPQ Qconv.
Let Q2P := isocan (isopres_sym isoPQ) Pconv.

Lemma isocanK u : normalword_of P u -> Q2P (P2Q u) = u.
Proof.
rewrite /normalword_of; case/andP => uinP norPu.
have norfPu : normalf P u u by split => //; apply: rewrites_to_refl.
have /equiv_sym := canmor isoPQ uinP; rewrite -(normalf_equivE Pconv.1 norfPu).
move/(confluentE Pconv.1 _); apply.
rewrite (normalf_equivE Pconv.1 (isocanP (isopres_sym isoPQ) Pconv (P2Q u))).
rewrite (isopres_invP _ (isocan_words_of _ _ uinP) (isopres_words_of _ uinP)).
exact/equiv_sym/equiv_isocan.
Qed.

End IsoCanK.


(** `isopres` preserve the number of normal forms (if finite) *)
Section NormalIso.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (isoPQ : isopres P Q)
  (Pconv : convergent P) (Qconv : convergent Q)
  (lP : seq (word Alph)) (lQ : seq (word Beta))
  (norlP : is_enum_normal P lP).

Section IsEnumNormalLQ.

Hypothesis norlQ : is_enum_normal Q lQ.

Theorem is_enum_normal_isocan :
  is_enum_normal Q [seq isocan isoPQ Qconv i | i <- lP].
Proof.
move: norlP norlQ; rewrite /is_enum_normal => -[uniqlP memlP] [uniqlQ memlQ].
set P2Q := isocan isoPQ Qconv.
pose Q2P := isocan (isopres_sym isoPQ) Pconv.
have P2QK : {in lP, cancel P2Q Q2P} by move=> u; rewrite -memlP; exact: isocanK.
have Q2PK : {in lQ, cancel Q2P P2Q} by move=> v; rewrite -memlQ; exact: isocanK.
split => [|u].
  rewrite map_inj_in_uniq => //; first exact: (can_in_inj P2QK).
rewrite memlQ; suff -> : [seq P2Q i | i <- lP] =i lQ by [].
move=> /= v; rewrite -memlQ; apply/mapP/idP => [[/= {}u]|].
  rewrite /normalword_of -memlP => /andP[uinP _ {v}->].
  by rewrite isocan_words_of // normal_isocan.
case/andP => vinQ norv; exists (Q2P v).
  by rewrite -memlP /normalword_of isocan_words_of // normal_isocan.
by rewrite Q2PK // -memlQ /normalword_of vinQ norv.
Qed.

Theorem isopres_perm_eq_enum :
  perm_eq [seq isocan isoPQ Qconv i | i <- lP] lQ.
Proof.
have:= is_enum_normal_isocan; move: (map _ _) => l2.
move: norlQ; rewrite /is_enum_normal => -[uniq_lQ memlQ] [uniq_l2 meml2].
by apply: uniq_perm => //= u; rewrite -memlQ -meml2.
Qed.
Corollary isopres_size_enum : size lP = size lQ.
Proof. by have /perm_size := isopres_perm_eq_enum; rewrite size_map. Qed.

End IsEnumNormalLQ.

Section NormalNonIso.

Hypotheses
  (uniq_lQ : uniq lQ)
  (normalword_of_lQ : forall u : word Beta, u \in lQ -> normalword_of Q u).

Theorem isopres_size_le : size lQ <= size lP.
Proof.
have := isocanK (isopres_sym isoPQ) Qconv Pconv.
set P2Q := isocan _ Qconv; set Q2P := isocan _ Pconv.
move=> isoK.
have {isoK} Q2P_inj : {in lQ &, injective Q2P}.
  by apply: (can_in_inj (g := P2Q)) => u /normalword_of_lQ/isoK.
have norQ2P u : normalf P (Q2P u) (Q2P u).
  apply: normalf_rewrite0; rewrite -/(normal _ _).
  exact: normal_isocan.
rewrite -(size_map (normal_of Pconv.2 \o Q2P)); apply: uniq_leq_size.
  rewrite map_inj_in_uniq // => u v uin vin.
  have /normalword_of_lQ/andP[uinQ noru] := uin.
  have /normalword_of_lQ/andP[vinQ norv] := vin.
  move/eqP/(normalf_equivP Pconv.1) => eqnor.
  have {}eqnor : Q2P u = Q2P v %[mod P].
    by apply: eqnor => /=; apply: normalf_ofP.
  apply: Q2P_inj => //.
  by apply/eqP/(normalf_equivP Pconv.1); last exact: eqnor.
move=> /= u /mapP[/= v /normalword_of_lQ norv {u}->].
move: norlP; rewrite /is_enum_normal => -[_ <-].
move: norv; rewrite /normalword_of => /andP[vin _].
rewrite normal_ofP andbT -(equiv_words_ofE (equiv_normal_of _ (Q2P v))).
exact: isocan_words_of.
Qed.

End NormalNonIso.

End NormalIso.


(** * Allows to prove that two presentations are not isomorphic. *)
Section NonIsoPres.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (rew1P :  word Alph -> option (word Alph))
  (rew1Q :  word Beta -> option (word Beta))
  (rew1P_ok : rewrites1_Ok P rew1P)
  (rew1Q_ok : rewrites1_Ok Q rew1Q)
  (Pconv : convergent P) (Qconv : convergent Q).

Theorem size_non_isopres (boundP boundQ : nat) :
  let (lP, okP) := enum_normal P rew1P boundP in
  let (lQ, okQ) := enum_normal Q rew1Q boundQ in
  okP -> size lP < size lQ -> isopres P Q -> False.
Proof.
have /= := enum_normalP Pconv rew1P_ok (bound := boundP).
move: (traject _ _ _) => lP /[apply] norlP /[swap].
move/isopres_size_le=> /(_ Pconv Qconv _ _ norlP) H.
rewrite ltnNge => /negP; apply; apply: H => [|u].
  exact: (enum_normal_uniq Qconv rew1Q_ok).
exact: enum_normal_wordP.
Qed.

End NonIsoPres.
