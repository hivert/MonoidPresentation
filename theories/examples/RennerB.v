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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
From mathcomp Require Import choice bigop fintype finfun finset ssralg monoid.
From mathcomp Require Import fingroup perm binomial.


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
Implicit Type (f g : {pperm 'SI_n}).

(** From monoid.v: pperm_perm f := [forall x : T, isSome (f x)]. *)
Definition antisymm f :=
  [forall i : 'SI_n, omap swapsign (f i) == f (swapsign i)].
Definition halfpperm f := [forall i : 'I_n, ~~ (f (inl i) && f (inr i))].
Definition signed_pperm f := dinjectiveb (omap absval \o f) (isSome \o f).
Definition isRennerB f :=
  pperm_is_perm f && antisymm f || halfpperm f && signed_pperm f.

Lemma antisymmP f :
  reflect (omap swapsign \o f =1 f \o swapsign) (antisymm f).
Proof.
apply (iffP idP) => /= [/forallP/= Heq i | Heq]; first by apply/eqP => /=.
by apply/forallP => /= i; have /= -> := Heq i.
Qed.
Lemma halfppermP f :
  reflect (forall i : 'SI_n, isSome (f i) -> ~ isSome (f (swapsign i)))
          (halfpperm f).
Proof.
apply (iffP forallP) => /= H.
  by case=> [] i; move/(_ i) : H => /=;
    case: (f (inl i)) (f (inr i)) => //= rli [//|]rri.
move=> i; move/(_ (inl i)) : H => /=.
case: (f (inl i)) => //= rli /(_ is_true_true).
by case: (f (inr i)).
Qed.
Lemma signed_ppermP f :
  reflect {on isSome &, injective ((omap absval) \o f)} (signed_pperm f).
Proof.
apply (iffP (dinjectiveP _ _)) => inj /= x y /=; rewrite !unfold_in.
- move=> Hx Hy; apply: inj => //; rewrite unfold_in.
  + by case: (f x) Hx.
  + by case: (f y) Hy.
- have:= inj x y; rewrite !unfold_in /=.
  by case: (f x) (f y) => [px | //][py | //].
Qed.

Record RennerB : predArgType :=
  mkRennerB {renval :> {pperm 'SI_n}; _ : isRennerB renval}.

HB.instance Definition _ := [isSub for renval].
HB.instance Definition _ := [Finite of RennerB by <:].

Lemma RennerB_closed : monoid_closed isRennerB.
Proof.
split => [|/= s t]; rewrite !unfold_in.
  apply/orP; left; apply/andP; split.
    by apply/pperm_is_permP => i; rewrite pperm1E.
  by apply/antisymmP => i /=; rewrite !pperm1E.
case/orP=> [/andP[/pperm_is_permP alls /antisymmP santi]|].
  case/orP=> [/andP[/pperm_is_permP allt /antisymmP tanti]|].
    apply/orP; left; apply/andP; split.
      apply/pperm_is_permP => i; rewrite /= !ppermME.
      by case: (s i) (alls i) => // si _ /=.
    apply/antisymmP => i; rewrite /= !ppermME.
    have /= <- := santi i; case: (s i) => [si|] //=.
    exact: (tanti si).
  case/andP=> /halfppermP halft /signed_ppermP spt.
  apply/orP; right; apply/andP; split.
    apply/halfppermP => i; rewrite !ppermME.
    move/(_ i): santi => /= <-; case: (s i) => //= {}i _ /halft.
  apply/signed_ppermP => i j.
  rewrite !unfold_in -!/(isSome _) /= !ppermME /= => tsi tsj eqij.
  have siSome := alls i; have sjSome := alls j => {alls}.
  apply: (pperm_inj siSome sjSome).
  case: (s i) (s j) siSome sjSome tsi tsj eqij => [{}i|//][{}j|//] _ _ /=.
  by move=> /spt/[apply]/[apply] ->.
case/andP=> /halfppermP halfs /signed_ppermP sps.
case/orP=> [/andP[_ /antisymmP tanti]|].
  apply/orP; right; apply/andP; split.
    apply/halfppermP => i; rewrite !ppermME.
    move/(_ i): halfs; case: (s i) => [si|]//= /(_ is_true_true).
    by case: (s _).
  apply/signed_ppermP=> i j.
  rewrite !unfold_in -!/(isSome _) /= => tsi tsj eqij.
  have {}tsi := isSome_omapK tsi; have {}tsj := isSome_omapK tsj.
  apply: (pperm_inj tsi tsj).
  rewrite !ppermME in tsi, tsj, eqij; rewrite !ppermME.
  move/omap_absvalE: eqij => [//|] eqts; congr (obind t (s _)); move: eqts.
  case eqsi: (s i) tsi => [si|] // tsi /=.
  case eqsj: (s j) tsj => [sj|] // tsj /=.
  have {tanti} /= -> := tanti sj => /[dup]eqts /pperm_inj.
  rewrite -eqts => /(_ tsi tsi) {t tsi tsj eqts} eqs.
  have := halfs i; rewrite eqsi => /(_ is_true_true).
  have:= congr1 absval eqs; rewrite absval_swapsign => eqabs nonssi.
  have {eqabs} : (omap absval \o s) i = (omap absval \o s) j.
    by rewrite /= eqsi eqsj /= eqabs.
  by apply: sps; rewrite !unfold_in /= ?eqsi ?eqsj.
case/andP=> /halfppermP halft /signed_ppermP spt.
apply/orP; right; apply/andP; split.
  apply/halfppermP => i; rewrite !ppermME.
  move/(_ i): halfs; case: (s i) => [si|]//= /(_ is_true_true).
  by case: (s _).
apply/signed_ppermP=> i j.
rewrite !unfold_in -!/(isSome _) /= => tsi tsj eqij.
have {}tsi := isSome_omapK tsi; have {}tsj := isSome_omapK tsj.
apply: (pperm_inj tsi tsj).
rewrite !ppermME in tsi, tsj, eqij; rewrite !ppermME.
move/omap_absvalE: eqij => [//|] eqts; congr (obind t (s _)); move: eqts.
case eqsi: (s i) tsi => [si|] //= tsi.
case eqsj: (s j) tsj => [sj|] //= tsj eqts1.
have {t spt halft tsi tsj eqts1}eqs : si = sj.
  apply: spt => /=.
    by case: (t si) tsi.
    by case: (t sj) tsj.
  rewrite eqts1 /= -[LHS]omap_comp.
  exact/eq_omap/absval_swapsign.
apply: sps; rewrite /=.
  by rewrite eqsi.
  by rewrite eqsj.
by rewrite eqsi eqsj eqs.
Qed.
HB.instance Definition _ :=
  SubChoice_isSubMonoid.Build {pperm 'SI_n} isRennerB RennerB RennerB_closed.

Definition pi_pos_fun (i : 'SI_n) : option 'SI_n :=
  if i is inr j then Some (inr j) else None.
Lemma pi_pos_fun_inj : {on isSome &, injective pi_pos_fun}.
Proof. by case=> [] i [] j //= _ _ [] ->. Qed.
Lemma pi_pos_subproof : isRennerB (pperm pi_pos_fun_inj).
Proof.
apply/orP; right; apply/andP; split.
  by apply/halfppermP => -[] i /=; rewrite !ppermE.
by apply/signed_ppermP => /= -[]i []j //=; rewrite !ppermE //= => _ _ [] ->.
Qed.
Definition pi_pos := mkRennerB pi_pos_subproof.
Lemma pi_pos_idemp : pi_pos * pi_pos = pi_pos.
Proof.
apply: val_inj => /=; apply/ppermP => /= -[] i; rewrite ppermME !ppermE //=.
by rewrite ppermE /=.
Qed.

Definition sB_fun (i : 'SI_n) : option 'SI_n :=
  if \val (absval i) == 0 then Some (swapsign i) else Some i.
Lemma sB_fun_inj : {on isSome &, injective sB_fun}.
Proof.
apply in2W => i j; rewrite /sB_fun /=.
case: (altP (\val (absval i) =P 0)) => /= [ieq0 | ineq0].
- case: (altP (\val (absval j) =P 0)) => /= [jeq0 | jneq0].
  + by case=> /(congr1 swapsign); rewrite !swapsignK.
  + case=> [] /(congr1 (fun i => \val (absval i))) /= /esym.
    by move: jneq0 => /[swap]; rewrite absval_swapsign ieq0 => ->.
- case: (altP (\val (absval j) =P 0)) => /= [jeq0 | jneq0].
  + case=> [] /(congr1 (fun i => \val (absval i))) /=.
    by move: ineq0 => /[swap]; rewrite absval_swapsign jeq0 => ->.
  + by case.
Qed.
Lemma sB_subproof : isRennerB (pperm sB_fun_inj).
Proof.
apply/orP; left; apply/andP; split; apply/forallP=> /= i.
  by rewrite !ppermE /sB_fun; case: eqP.
rewrite !ppermE /sB_fun absval_swapsign.
by case: (altP (\val (absval i) =P 0)).
Qed.
Definition sB := mkRennerB sB_subproof.
Lemma sBK : sB * sB = 1.
Proof.
apply: val_inj => /=; apply/ppermP => /= i; rewrite ppermME !ppermE /sB_fun.
case: (altP (\val (absval i) =P 0)) => /= [ieq0 | ineq0].
  by rewrite ppermE /sB_fun absval_swapsign ieq0 eqxx swapsignK pperm1E.
by rewrite ppermE /sB_fun (negbTE ineq0) pperm1E.
Qed.


Implicit Type (p q : {perm 'I_n}) (r s t : RennerB).

Definition perm2B_fun p (i : 'SI_n) : option 'SI_n :=
  match i with
  | inl i => Some (inl (p i))
  | inr i => Some (inr (p i))
  end.
Lemma perm2B_funM p q :
  perm2B_fun (p * q) =1 obind (perm2B_fun q) \o (perm2B_fun p).
Proof. by case=> i /=; rewrite permM. Qed.
Lemma perm2B_fun2 : perm2B_fun 1 =1 Some.
Proof. by case=> i /=; rewrite perm1. Qed.
Lemma perm2B_funK p : obind (perm2B_fun p^-1) \o (perm2B_fun p) =1 Some.
Proof. by move=> i; rewrite -perm2B_funM mulgV perm2B_fun2. Qed.

Lemma perm2B_fun_inj p : {on isSome &, injective (perm2B_fun p)}.
Proof.
apply in2W => i j /(congr1 (obind (perm2B_fun p^-1))).
by have /= -> := perm2B_funK p i; have /= -> := perm2B_funK p j => -[].
Qed.
Lemma perm2B_subproof p : isRennerB (pperm (perm2B_fun_inj (p := p))).
Proof.
apply/orP; left; apply/andP; split; apply/forallP=> /= []i.
  by rewrite !ppermE /perm2B_fun; case i.
by case: i => i /=; rewrite !ppermE /perm2B_fun /=.
Qed.
Definition perm2B p := mkRennerB (perm2B_subproof p).
Lemma perm2B_monoid_morphism : monoid_morphism perm2B.
Proof.
by split => [| /= f g]; apply/val_inj/ppermP => -[]i;
  rewrite ?ppermE ?pperm1E ?ppermME /= !(perm1, permM) //=
    !ppermE /perm2B_fun /= ppermE.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {perm 'I_n} RennerB perm2B perm2B_monoid_morphism.
Lemma perm2B_inj : injective perm2B.
Proof.
move=> p q eqpq; apply/permP => i.
move/(congr1 (fun r => renval r (inl i))) : eqpq.
by rewrite /= !ppermE /perm2B_fun /= => -[].
Qed.

Section PermSign.

Variables (p : {perm 'I_n}) (sgn : n.-tuple bool).

Definition RB_of_perm_sign_fun :=
  [fun i => match i with
            | inl i => if tnth sgn i then Some (inl (p i)) else Some (inr (p i))
            | inr i => if tnth sgn i then Some (inr (p i)) else Some (inl (p i))
            end].
Lemma RB_of_perm_sign_inj : {on isSome &, injective RB_of_perm_sign_fun}.
Proof.
apply on2W.
by case=> [] i [] j /=;
   case ti: (tnth _ _); case tj: (tnth sgn j) => -[] // /perm_inj // eqij;
   move: ti; rewrite eqij // tj.
Qed.
Lemma RB_of_perm_sign_subproof : isRennerB (pperm RB_of_perm_sign_inj).
Proof.
apply/orP; left; apply/andP; split.
  apply/pperm_is_permP => /= i; rewrite ppermE /=.
  by case: i => i; case: (tnth sgn _).
by apply/antisymmP => -[]i /=; rewrite !ppermE /=; case: (tnth _ _).
Qed.
Definition RB_of_perm_sign := mkRennerB RB_of_perm_sign_subproof.

End PermSign.

Definition perm_of_RB r : {perm 'I_n} :=
  perm_of_transf (of_ptransf [ffun i : 'I_n => omap absval (r (inr i))]).
Definition sign_of_RB r : n.-tuple bool :=
  [tuple if (r (inr i)) is Some (inr _) then true else false  | i < n].

Definition RB_of_ps ps := RB_of_perm_sign ps.1 ps.2.
Definition ps_of_RB r := (perm_of_RB r, sign_of_RB r).

Lemma RB_of_psK : cancel RB_of_ps ps_of_RB.
Proof.
rewrite /RB_of_ps /ps_of_RB => -[p s] /=; congr (_, _).
  apply/permP => i; rewrite /perm_of_RB /=.
  rewrite perm_of_transfE => [|{}i j]; rewrite !ffunE /= !ffunE !ppermE /=.
    by case: (tnth s i).
  by case: (tnth s i) (tnth s j) => -[] /= /perm_inj.
apply: eq_from_tnth => i.
by rewrite tnth_mktuple /= ppermE /=; case: (tnth s i).
Qed.

Lemma ps_of_RBK :
  {in [set r : RennerB | pperm_is_perm r], cancel ps_of_RB RB_of_ps}.
Proof.

case=> /= r /= renr /[!inE] /= permr.
have r_inj : injective (of_ptransf [ffun i0 => omap absval (r (inr i0))]).
  move=> /= i j; rewrite !ffunE /= !ffunE /=.
  case: (r (inr i)) (allr (inr i)) => ri /= _.
  
apply/val_inj/ppermP => /= -[]i; rewrite !ppermE /=; case: (tnth _ _) => /=.
  rewrite /perm_of_RB /=.
  rewrite perm_of_transfE /= => [|{}i j]. ; rewrite !ffunE /= !ffunE /=.
        
Admitted.

Lemma RB_of_ps_bij:
  {on [set r : RennerB | pperm_is_perm r], bijective RB_of_ps}.
Proof.
exists ps_of_RB; first exact/in1W/RB_of_psK.
by move=> /= r Hr; rewrite ps_of_RBK.
Qed.




End Defs.

Notation "''RB_' n" := (RennerB n)
  (at level 8, n at level 2, format "''RB_' n").


Section Theory.

Variable n0 : nat.
Notation n := (n0.+1).
Implicit Types (r s t : 'RB_n) (i j : 'SI_n).

Lemma permVhalf :
  [disjoint [set r : 'RB_n | pperm_is_perm r] & [set r : 'RB_n | halfpperm r]].
Proof.
rewrite disjoint_subset; apply/subsetP => /= r.
rewrite !inE => /pperm_is_permP alls; apply/negP => /halfppermP halfs.
by have /halfs := alls (inr ord0); rewrite alls.
Qed.

Lemma cardRB_permVhalf :
  #|[set: 'RB_n]|
  = #|[set r : 'RB_n | pperm_is_perm r]| + #|[set r : 'RB_n | halfpperm r]|.
Proof.
rewrite -cardsUI (disjoint_setI0 permVhalf) cards0 addn0.
congr #|pred_of_set _|; apply/esym/eqP; rewrite -subTset.
apply/subsetP => r _; rewrite !inE.
by case: r => r /= /orP[/andP[-> _] | /andP[-> _ /[!orbT]]].
Qed.

Definition card'RB :=
  n`! * 2 ^ n + \sum_(k < n.+1) 4 ^ k * (binomial n k) ^ 2 * k`!.
Definition card'RB_comp :=
  n`! * 2 ^ n + sumn [seq 4 ^ k * (binomial n k) ^ 2 * k`! | k <- iota 0 n.+1]%N.

End Theory.

Goal card'RB_comp 1 = 7.     Proof. by compute. Qed.
Goal card'RB_comp 2 = 57.    Proof. by compute. Qed.
Goal card'RB_comp 3 = 757.   Proof. by compute. Qed.
#[warning="-abstract-large-number"]
Goal card'RB_comp 4 = 13889. Proof. by compute. Qed.
