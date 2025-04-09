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
Definition enum_normal n := iter n enum_normal_next [:: [::]].

Lemma normal_sz0 : normal_sz 0 [::].
Proof. by rewrite /normal_sz /=; apply normal0; case: convP. Qed.

Lemma normal_sz_enum_normal n : all (normal_sz n) (enum_normal n).
Proof.
elim: n => [| n]; first by rewrite /= normal_sz0.
rewrite {2}/enum_normal /= -/(enum_normal n).
move: (enum_normal n) => norf /allP /= allnorf; apply/allP => /= [[| u0 u]].
  by rewrite mem_filter => /andP[_ /allpairsP[[/= u0 u []]]].
rewrite mem_filter => /andP[]; case: rew1P => nrew // _.
case/allpairsP => /= - [v0 v]/= [ugen unor []] equ0 equ; subst v0 v.
have := allnorf u unor; rewrite /normal /= /normal_sz /= eqSS.
case: eqP => //= _.
have -> : (u0 :: u \in words_of P) = (u \in words_of P).
  by rewrite !unfold_in /words_of /= ugen.
by case: (u \in _).
Qed.

Lemma count_mem_enum_normal n u :
  normal_sz n u -> count_mem u (enum_normal n) = 1%N.
Proof.
elim: n u => [|n]; first by case.
rewrite {2}/enum_normal /= -/(enum_normal n).
move: (enum_normal n) => norf Hn [|u0 u] //=.
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

Lemma uniq_enum_normal n : uniq (enum_normal n).
Proof.
have /allP /= allnorf := normal_sz_enum_normal n.
apply: count_mem_uniq => /= u.
case: (boolP (u \in _)) => [/allnorf/count_mem_enum_normal -> // | /= unotin].
exact/count_memPn.
Qed.

Lemma mem_enum_normalP n u : (u \in enum_normal n) = normal_sz n u.
Proof.
have /allP /= allnorf := normal_sz_enum_normal n.
case: (boolP (u \in _)) => [/allnorf -> // | /= unotin].
apply/esym; apply/contraNF: unotin => /count_mem_enum_normal.
by rewrite -has_pred1 has_count => ->.
Qed.

End EnumNormalForms.
