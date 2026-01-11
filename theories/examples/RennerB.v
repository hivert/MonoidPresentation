(** * Renner monoids of type B *)
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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice bigop fintype finfun finset ssralg monoid.
From mathcomp Require Import fingroup binomial.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import monoids.

Local Open Scope group_scope.

Lemma isSome_omapK (T1 T2 T3 : Type) (f : T1 -> option T2) (g : T2 -> T3) i :
  omap g (f i) -> f i.
Proof. by case: (f i). Qed.


Notation "''SI_' n" := ('I_n + 'I_n)%type
  (at level 0, n at level 2, format "''SI_' n").

Section SignedInts.

Context {n : nat}.

Definition absval (i : 'SI_n) := match i with | inl i | inr i => i end.
Definition swapsign (i : 'SI_n) : 'SI_n :=
  match i with | inl i => inr i | inr i => inl i end.

Lemma absval_swapsign i : absval (swapsign i) = absval i.
Proof. by case: i. Qed.
Lemma swapsignK : involutive swapsign.
Proof. by case. Qed.
Lemma omap_absvalE i j :
  omap absval i = omap absval j -> i = j \/ i = omap swapsign j.
Proof.
case: i j => [i|][j|]//=; last by move=> _; left.
by case: i j => []i []j //= [->]; [left|right|right|left].
Qed.

Lemma enum_SInE :
  enum {: 'SI_n} = [seq inl i | i <- enum 'I_n] ++ [seq inr i | i <- enum 'I_n].
Proof. by rewrite enumT /= unlock /= /sum_enum -!enumT /=. Qed.

Lemma enum_optSInE :
  enum {: option 'SI_n} =
    None ::
      [seq Some (inl i) | i <- enum 'I_n] ++ [seq Some (inr i) | i <- enum 'I_n].
Proof.
by rewrite enumT unlock /= /option_enum -!enumT enum_SInE map_cat -!map_comp.
Qed.

End SignedInts.


Section Defs.

Variable n : nat.
Implicit Type (p : {pperm 'SI_n}).

Definition is_antisymm_perm p :=
  [forall i : 'I_n, if (p (inl i), p (inr i)) is (Some k, Some l)
                    then k == swapsign l
                    else false].
Definition is_broken_pperm p := [forall i : 'I_n, ~~ (p (inl i) && p (inr i))].
Definition signed_pperm p := dinjectiveb (omap absval \o p) (isSome \o p).
Definition isRennerB p :=
  is_antisymm_perm p || is_broken_pperm p && signed_pperm p.

Lemma is_antisymm_permP p :
  reflect (forall i : 'SI_n, isSome (p i) /\ omap swapsign (p i) = p (swapsign i))
          (is_antisymm_perm p).
Proof.
apply (iffP forallP) => /= H.
  case=> [] i; move/(_ i) : H => /=;
    case: (p (inl i)) (p (inr i)) => //= rli [//|]rri // /eqP -> //=.
  by rewrite swapsignK.
move=> i; move/(_ (inl i)) : H => /= [].
case: (p (inl i)) (p (inr i)) => //= rli rri _ <-.
by rewrite swapsignK.
Qed.
Lemma is_broken_ppermP p :
  reflect (forall i : 'SI_n, isSome (p i) -> ~ isSome (p (swapsign i)))
          (is_broken_pperm p).
Proof.
apply (iffP forallP) => /= H.
  by case=> [] i; move/(_ i) : H => /=;
    case: (p (inl i)) (p (inr i)) => //= rli [//|]rri.
move=> i; move/(_ (inl i)) : H => /=.
case: (p (inl i)) => //= rli /(_ is_true_true).
by case: (p (inr i)).
Qed.
Lemma signed_ppermP p :
  reflect {on isSome &, injective ((omap absval) \o p)} (signed_pperm p).
Proof.
apply (iffP (dinjectiveP _ _)) => inj /= x y /=; rewrite !unfold_in.
- move=> Hx Hy; apply: inj => //; rewrite unfold_in.
  + by case: (p x) Hx.
  + by case: (p y) Hy.
- have:= inj x y; rewrite !unfold_in /=.
  by case: (p x) (p y) => [px | //][py | //].
Qed.

Record rennerB : predArgType :=
  RennerB {renval :> {pperm 'SI_n}; _ : isRennerB renval}.

HB.instance Definition _ := [isSub for renval].
HB.instance Definition _ := [Finite of rennerB by <:].

Lemma rennerB_closed : monoid_closed isRennerB.
Proof.
split => [|/= s t]; rewrite !unfold_in.
  by apply/orP; left; apply/is_antisymm_permP => i; rewrite !pperm1E.
case/orP=> [/is_antisymm_permP santi |].
  case/orP=> [/is_antisymm_permP tanti |].
    apply/orP; left; apply/is_antisymm_permP => i; rewrite !ppermME.
    by move/(_ i): santi => [/[swap] <-]; case: (s i) => /=.
  case/andP=> /is_broken_ppermP brt /signed_ppermP spt.
  apply/orP; right; apply/andP; split.
    apply/is_broken_ppermP => i; rewrite !ppermME.
    by move/(_ i): santi => [/[swap] <-]; case: (s i) => //= {}i _ /brt.
  apply/signed_ppermP => i j.
  rewrite !unfold_in -!/(isSome _) /= !ppermME /= => tsi tsj eqij.
  have [siSome _] := santi i; have [sjSome _] := santi j => {santi}.
  apply: (pperm_inj siSome sjSome).
  case: (s i) (s j) siSome sjSome tsi tsj eqij => [{}i|//][{}j|//] _ _ /=.
  by move=> /spt/[apply]/[apply] ->.
case/andP=> /is_broken_ppermP brs /signed_ppermP sps.
case/orP=> [/is_antisymm_permP tanti |].
  apply/orP; right; apply/andP; split.
    apply/is_broken_ppermP => i; rewrite !ppermME.
    move/(_ i): brs; case: (s i) => [si|]//= /(_ is_true_true).
    by case: (s _).
  apply/signed_ppermP=> i j.
  rewrite !unfold_in -!/(isSome _) /= => tsi tsj eqij.
  have {}tsi := isSome_omapK tsi; have {}tsj := isSome_omapK tsj.
  apply: (pperm_inj tsi tsj).
  rewrite !ppermME in tsi, tsj, eqij; rewrite !ppermME.
  move/omap_absvalE: eqij => [//|] Heq; congr (obind t (s _)); move: Heq.
  case eqsi: (s i) tsi => [si|] // tsi /=.
  case eqsj: (s j) tsj => [sj|] // tsj /=.
  have {tanti} [_ ->] := tanti sj => /[dup]Heq /pperm_inj.
  rewrite -Heq => /(_ tsi tsi) {t tsi tsj} Heq.
  have := brs i; rewrite eqsi => /(_ is_true_true).
  have:= congr1 absval Heq; rewrite absval_swapsign => eqabs nonssi.
  have {eqabs} : (omap absval \o s) i = (omap absval \o s) j.
    by rewrite /= eqsi eqsj /= eqabs.
  by apply: sps; rewrite !unfold_in /= ?eqsi ?eqsj.
case/andP=> /is_broken_ppermP brt /signed_ppermP spt.
apply/orP; right; apply/andP; split.
  apply/is_broken_ppermP => i; rewrite !ppermME.
  move/(_ i): brs; case: (s i) => [si|]//= /(_ is_true_true).
  by case: (s _).
apply/signed_ppermP=> i j.
rewrite !unfold_in -!/(isSome _) /= => tsi tsj eqij.
have {}tsi := isSome_omapK tsi; have {}tsj := isSome_omapK tsj.
apply: (pperm_inj tsi tsj).
rewrite !ppermME in tsi, tsj, eqij; rewrite !ppermME.
move/omap_absvalE: eqij => [//|] Heq; congr (obind t (s _)); move: Heq.
case eqsi: (s i) tsi => [si|] //= tsi.
case eqsj: (s j) tsj => [sj|] //= tsj Heq.
have {t spt brt tsi tsj Heq} Heq : si = sj.
  apply: spt => /=.
    by case: (t si) tsi.
    by case: (t sj) tsj.
  rewrite Heq /= -[LHS]omap_comp.
  exact/eq_omap/absval_swapsign.
apply: sps; rewrite /=.
  by rewrite eqsi.
  by rewrite eqsj.
by rewrite eqsi eqsj Heq.
Qed.
HB.instance Definition _ :=
  SubChoice_isSubMonoid.Build {pperm 'SI_n} isRennerB rennerB rennerB_closed.

End Defs.

Notation "''Ren_' n" := (rennerB n)
  (at level 8, n at level 2, format "''Ren_' n").


Section Theory.

Variable n : nat.
Implicit Types (r s t : 'Ren_n) (i j : 'SI_n).

Definition cardRennerB :=
  n`! * 2 ^ n + \sum_(k < n.+1) 4 ^ k * (binomial n k) ^ 2 * k`!.
Definition cardRennerB_comp :=
  n`! * 2 ^ n + sumn [seq 4 ^ k * (binomial n k) ^ 2 * k`! | k <- iota 0 n.+1]%N.

End Theory.

Eval compute in cardRennerB_comp 1.
Eval compute in cardRennerB_comp 2.
Eval compute in cardRennerB_comp 3.
Eval compute in cardRennerB_comp 4.


