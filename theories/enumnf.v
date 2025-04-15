(** * Monoid Presentations *)
(******************************************************************************)
(*      Copyright (C) 2021      Florent Hivert <florent.hivert@lri.fr>        *)
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

Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section EnumNormalForms.

Context {Alph : choiceType} (P : pres Alph).
Hypothesis convP : convergent (prelat P).

Variable (rew1 : word Alph -> option (word Alph)).
Hypothesis (rew1P : forall u, rewrites1_spec (prelat P) u (rew1 u)).

Implicit Types (u v w : word Alph) (norf : seq (word Alph)).

Definition normal_sz (n : nat) u :=
  [&& size u == n, u \in words_of P & normal (prelat P) u].
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
case: eqP => //= _.
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
rewrite /normal_sz /= eqSS.
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

Lemma enum_normalE n :
  enum_normal_sz n = [::] ->
  forall u,
    (u \in words_of P) && (normal (prelat P) u) =
      (u \in flatten (traject enum_normal_next [:: [::]] n)).
Proof.
move=> Hiter u.
have gt m : m >= n -> enum_normal_sz m = [::].
  elim: m => [|m IHm] /=.
    by rewrite leqn0 => /eqP Hn; rewrite Hn /= in Hiter.
  rewrite leq_eqVlt ltnS => /orP[/eqP eq| /IHm ->].
    by move: Hiter; rewrite eq /=.
  by rewrite /enum_normal_next /=; elim: (pgen P).
apply/idP/idP.
  case/andP => uin noru.
  have {uin}noru : normal_sz (size u) u by rewrite /normal_sz eqxx uin noru.
  apply/flattenP => /=; exists (iter (size u) enum_normal_next [:: [::]]).
    apply/trajectP; exists (size u) => //.
    apply/negP => /negP; rewrite -leqNgt => {}/gt eqnor.
    by rewrite -mem_enum_normalP eqnor in noru.
  by rewrite mem_enum_normalP.
case/flattenP => /= l /trajectP[m ltmn {l}->].
by rewrite mem_enum_normalP => /and3P[_ -> ->].
Qed.

(** Given a bound returns the list of normal forms of size less than bound
and a boolean telling if that list is complete *)
Definition enum_normal bound :=
  let l := traject enum_normal_next [:: [::]] bound in
  (flatten l, last [::[::]] l == [::]).
Definition is_enum_normal l :=
  uniq l /\ forall u, (u \in words_of P) && (normal (prelat P) u) = (u \in l).

Lemma enum_normalP bound :
  let: (l, ok) := enum_normal bound in ok -> is_enum_normal l.
Proof.
move => /= H; split; first last.
  rewrite /enum_normal; case: bound H => [//| b].
  rewrite {2}trajectSr /= last_traject => /eqP/[dup]/enum_normalE H ->.
  by rewrite flatten_rcons cats0.
elim: bound {H} => // n IHn.
rewrite trajectSr flatten_rcons cat_uniq {}IHn uniq_enum_normal_sz andbT /=.
apply/negP => /hasP[/= u]; rewrite mem_enum_normalP => /andP[/eqP szu _].
case/flattenP => /= l /trajectP[i ltin {l}->].
rewrite mem_enum_normalP => /andP[ + _].
by rewrite szu gtn_eqF.
Qed.

End EnumNormalForms.


(* isopres preserve the number of normal forms (if finite) *)
Section IsoCan.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (Qconv : convergent (prelat Q))
  (isoPQ : isopres P Q).

Definition isocan u := normal_of Qconv.2 (isoPQ u).
Local Lemma isocan_words w : w \in words_of P -> isocan w \in words_of Q.
Proof.
have [_ /rewrites_to_words_ofE <-] := normal_ofP Qconv.2 (isoPQ w).
by move/(isopres_word_of isoPQ).
Qed.
Local Lemma isocanP u : normalf (prelat Q) (isoPQ u) (isocan u).
Proof. exact: normal_ofP. Qed.

End IsoCan.


Section IsoCanK.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (Pconv : convergent (prelat P))
  (Qconv : convergent (prelat Q))
  (isoPQ : isopres P Q).

Let P2Q := isocan Qconv isoPQ.
Let Q2P := isocan Pconv (isopres_sym isoPQ).

Lemma isocanK u :
  (u \in words_of P) && (normal (prelat P) u) -> Q2P (P2Q u) = u.
Proof.
case/andP => uinP norPu.
have norfPu : normalf (prelat P) u u by split => //; apply: rewrites_to_refl.
have /equiv_sym := canmor isoPQ uinP; rewrite -(normalf_equivE Pconv.1 norfPu).
move/(confluentE Pconv.1 _); apply.
rewrite (normalf_equivE Pconv.1 (isocanP Pconv (isopres_sym isoPQ) (P2Q u))).
rewrite (isopres_invP _ (isocan_words _ _ uinP) (isopres_word_of _ uinP)).
by have [_ /rewrites_to_equiv/equiv_sym] := isocanP Qconv isoPQ u.
Qed.

End IsoCanK.


Section NormalIso.

Context {Alph Beta : choiceType}
  (P : pres Alph) (Q : pres Beta)
  (Pconv : convergent (prelat P))
  (Qconv : convergent (prelat Q))
  (isoPQ : isopres P Q)
  (lP : seq (word Alph)) (lQ : seq (word Beta))
  (norlP :   is_enum_normal P lP) (norlQ : is_enum_normal Q lQ).

Theorem isopres_perm_eq_enum : perm_eq [seq isocan Qconv isoPQ i | i <- lP] lQ.
Proof.
move: norlP norlQ; rewrite /is_enum_normal => -[uniqlP memlP] [uniqlQ memlQ].
set P2Q := isocan Qconv isoPQ.
pose Q2P := isocan Pconv (isopres_sym isoPQ).
have P2QK : {in lP, cancel P2Q Q2P} by move=> u; rewrite -memlP; exact: isocanK.
have Q2PK : {in lQ, cancel Q2P P2Q} by move=> v; rewrite -memlQ; exact: isocanK.
apply: uniq_perm => //.
  rewrite map_inj_in_uniq => //; first exact: (can_in_inj P2QK).
move=> /= v; rewrite -memlQ; apply/mapP/idP => [[u]|].
  rewrite -memlP => /andP[uinP _ {v}->].
  rewrite (isocan_words _ _ uinP) /=.
  by have[] := isocanP Qconv isoPQ u.
case/andP => vinQ norv; exists (Q2P v).
  rewrite -memlP; rewrite (isocan_words _ _ vinQ) /=.
  by have[] := isocanP Pconv (isopres_sym isoPQ) v.
by rewrite Q2PK // -memlQ vinQ norv.
Qed.
Corollary isopres_size_enum : size lP = size lQ.
Proof. by have /perm_size := isopres_perm_eq_enum; rewrite size_map. Qed.

End NormalIso.

