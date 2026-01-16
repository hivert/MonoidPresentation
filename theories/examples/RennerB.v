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


Notation "''SI_' n" := (bool * 'I_n)%type
  (at level 0, n at level 2, format "''SI_' n").

Section SignedInts.

Context {n : nat}.

Definition absval (i : 'SI_n) := i.2.
Definition swapsign (i : 'SI_n) : 'SI_n := (~~ i.1, i.2).

Lemma absval_swapsign i : absval (swapsign i) = absval i.
Proof. by []. Qed.
Lemma swapsignK : involutive swapsign.
Proof. by rewrite /swapsign => -[i j]; rewrite negbK. Qed.

Lemma omap_absvalE i j :
  omap absval i = omap absval j -> i = j \/ i = omap swapsign j.
Proof.
case: i j => [[b0 i0]|]/= [[b1 i1]|]//=; last by move=> _; left.
by move=> [->]; case: b0 b1 => [] [] /=; [left|right|right|left].
Qed.

Lemma enum_bool : enum {: bool} = [:: true; false].
Proof. by rewrite enumT /= unlock /=. Qed.

Lemma enum_SInE :
  enum {: 'SI_n} =
    [seq (true, i) | i <- enum 'I_n] ++ [seq (false, i) | i <- enum 'I_n].
Proof. by rewrite enumT /= unlock /= /prod_enum /= enum_bool /= cats0. Qed.

End SignedInts.


Section Defs.

Variable n : nat.
Implicit Type (f g : {pperm 'SI_n}).

(** From monoid.v: pperm_perm f := [forall x : T, isSome (f x)]. *)
Definition antisymm f :=
  [forall i : 'SI_n, omap swapsign (f i) == f (swapsign i)].
Definition halfpperm f := [forall i : 'I_n, ~~ (f (true, i) && f (false, i))].
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
  by case=> [[] i] /=; rewrite /swapsign /=;
     case: (f (true, i)) (f (false, i)) (H i) => [ffi|][fti|].
move=> i /=; rewrite /swapsign /=.
case: (f (true, i)) (f (false, i)) (H (true, i)) (H (false, i)) => [ffi|][fti|]//=.
by move=> _ /= /(_ is_true_true).
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

Lemma RennerP (r : RennerB) : isRennerB r.
Proof. by case: r. Qed.

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
  apply: spt => /=; [ by case: (t si) tsi| by case: (t sj) tsj |].
  rewrite eqts1 /= -[LHS]omap_comp.
  exact/eq_omap/absval_swapsign.
by apply: sps => /=; rewrite ?eqsi ?eqsj // eqs.
Qed.
HB.instance Definition _ :=
  SubChoice_isSubMonoid.Build {pperm 'SI_n} isRennerB RennerB RennerB_closed.

End Defs.

Notation "''RB_' n" := (RennerB n)
  (at level 8, n at level 2, format "''RB_' n").


Section Theory.

Lemma RB0E : all_equal_to (1 : 'RB_0).
Proof. by move=> /= r; apply/val_inj/ppermP => -[/= b []]. Qed.

Lemma permVhalf n : n != 0 -> forall r : 'RB_n, pperm_is_perm r (+) halfpperm r.
Proof.
case: n => // n _; case=> r /=; rewrite /isRennerB.
case: (boolP (pperm_is_perm r)) => /= [ /pperm_is_permP alls _ |_  /andP[->] //].
apply/negP => /halfppermP halfs.
by have /halfs := alls (true, ord0); rewrite alls.
Qed.

Lemma Renner_perm_anti n (r : 'RB_n) : pperm_is_perm r -> antisymm r.
Proof.
case: n r => [|n] r.
  rewrite {r}RB0E => _; apply/antisymmP => /= -[/= b []] //.
move=> rperm; have:= RennerP r; rewrite /isRennerB.
have:= permVhalf (n := n.+1) is_true_true r.
by rewrite rperm => /= /negbTE->; rewrite orbF.
Qed.

Lemma Renner_half_signed n (r : 'RB_n) : halfpperm r -> signed_pperm r.
Proof.
case: n r => [|n] r.
  rewrite {r}RB0E => _; apply/signed_ppermP => /= -[/= b []] //.
move=> hperm; have:= RennerP r; rewrite /isRennerB.
have:= permVhalf (n := n.+1) is_true_true r.
by rewrite hperm addbT => /negbTE ->.
Qed.

End Theory.


Section Generators.

Variable (n : nat).

Definition pi_pos_fun (i : 'SI_n) : option 'SI_n := if i.1 then Some i else None.
Lemma pi_pos_fun_inj : {on isSome &, injective pi_pos_fun}.
Proof. by case=> [[]i][[]j] //= _ _ [->]. Qed.
Lemma pi_pos_subproof : isRennerB (pperm pi_pos_fun_inj).
Proof.
apply/orP; right; apply/andP; split.
  by apply/halfppermP => -[[] i] /=; rewrite !ppermE.
by apply/signed_ppermP => /= -[[]i] [[]j] //=; rewrite !ppermE //= => _ _ [] ->.
Qed.
Definition pi_pos := mkRennerB pi_pos_subproof.
Lemma pi_pos_idemp : pi_pos * pi_pos = pi_pos.
Proof.
apply: val_inj => /=; apply/ppermP => /= -[[]i]; rewrite ppermME !ppermE //=.
by rewrite ppermE /=.
Qed.

Definition sB_fun (i : 'SI_n) : option 'SI_n :=
  if \val (absval i) == 0 then Some (swapsign i) else Some i.
Lemma sB_fun_inj : {on isSome &, injective sB_fun}.
Proof.
apply in2W => i j; rewrite /sB_fun /=.
case: (altP (\val (absval i) =P 0)) => /= [ieq0 | ineq0].
- case: (altP (\val (absval j) =P 0)) => /= [jeq0 | jneq0] /Some_inj.
  + by move/(congr1 swapsign); rewrite !swapsignK.
  + move/(congr1 absval ) => /esym; rewrite absval_swapsign.
    by move: jneq0 => /[swap] ->; rewrite ieq0.
- case: (altP (\val (absval j) =P 0)) => /= [jeq0 | jneq0] /Some_inj //.
  + move/(congr1 absval ) => /esym; rewrite absval_swapsign.
    by move: ineq0 => /[swap] <-; rewrite jeq0.
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

End Generators.

Section FromPermutations.

Variable (n : nat).

Implicit Type (p q : {perm 'I_n}) (r s t : 'RB_n).

Definition perm2B_fun p := [fun i : 'SI_n => Some (i.1, p i.2)].
Lemma perm2B_funM p q :
  perm2B_fun (p * q) =1 obind (perm2B_fun q) \o (perm2B_fun p).
Proof. by case=> [[]i]/=; rewrite permM. Qed.
Lemma perm2B_fun2 : perm2B_fun 1 =1 Some.
Proof. by case=> [[]i]/=; rewrite perm1. Qed.
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
by case: i => [[]i] /=; rewrite !ppermE /perm2B_fun /=.
Qed.
Definition perm2B p := mkRennerB (perm2B_subproof p).
Lemma perm2B_monoid_morphism : monoid_morphism perm2B.
Proof.
by split => [| /= f g]; apply/val_inj/ppermP => -[[]i];
  rewrite ?ppermE ?pperm1E ?ppermME /= !(perm1, permM) //= ppermE /= ppermE.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {perm 'I_n} 'RB_n perm2B perm2B_monoid_morphism.
Lemma perm2B_inj : injective perm2B.
Proof.
move=> p q eqpq; apply/permP => i.
move/(congr1 (fun r => renval r (true, i))) : eqpq.
by rewrite /= !ppermE /= => -[].
Qed.

Section PermSign.

Variables (p : {perm 'I_n}) (sgn : n.-tuple bool).

Definition RB_of_perm_sign_fun :=
  [fun i => if tnth sgn (absval i)
            then (perm2B p i)
            else omap swapsign (perm2B p i)].
Lemma RB_of_perm_sign_inj : {on isSome &, injective RB_of_perm_sign_fun}.
Proof.
apply on2W.
by case=> [[]i] [[]j]; rewrite /= !ppermE /=;
   case ti: (tnth _ _); case tj: (tnth sgn j) => -[] // /perm_inj // eqij;
   move: ti; rewrite eqij // tj.
Qed.
Lemma RB_of_perm_sign_subproof : isRennerB (pperm RB_of_perm_sign_inj).
Proof.
apply/orP; left; apply/andP; split.
  apply/pperm_is_permP => /= i; rewrite !ppermE /= ppermE /=.
  by case: i => [[]i]; case: (tnth sgn _).
by apply/antisymmP => -[[]i] /=; rewrite !ppermE /= !ppermE /=; case: (tnth _ _).
Qed.
Definition RB_of_perm_sign := mkRennerB RB_of_perm_sign_subproof.

End PermSign.

Definition perm_of_RB r : {perm 'I_n} :=
  perm_of_transf (of_ptransf [ffun i : 'I_n => omap absval (r (true, i))]).
Definition signs_of_RB r : n.-tuple bool :=
  [tuple if (r (true, i)) is Some (b, _) then b else false | i < n].

Definition RB_of_ps ps := RB_of_perm_sign ps.1 ps.2.
Definition ps_of_RB r := (perm_of_RB r, signs_of_RB r).

Lemma RB_of_psK : cancel RB_of_ps ps_of_RB.
Proof.
rewrite /RB_of_ps /ps_of_RB => -[p s] /=; congr (_, _).
  apply/permP => i; rewrite /perm_of_RB /=.
  rewrite perm_of_transfE => [|{}i j];
    rewrite !ffunE /= !ffunE /= !ppermE /= !ppermE /=.
    by case: (tnth s i).
  by case: (tnth s i) (tnth s j) => -[] /= /perm_inj.
apply: eq_from_tnth => i.
by rewrite tnth_mktuple /= !ppermE /= ppermE /=; case: (tnth s i).
Qed.

Lemma ps_of_RBK :
  {in [pred r : 'RB_n | pperm_is_perm r], cancel ps_of_RB RB_of_ps}.
Proof.
move=> r; rewrite inE => rperm.
have /antisymmP ranti := Renner_perm_anti rperm.
move/pperm_is_permP in rperm.
have r_inj : injective (of_ptransf [ffun i0 => omap absval (r (true, i0))]).
  move=> /= i j; rewrite !ffunE /= !ffunE /=.
  have:= @omap_absvalE _ (r (true, i)) (r (true, j)).
  case Hri : (r (true, i)) (rperm (true, i)) => [ri|//] /= _.
  case Hrj : (r (true, j)) (rperm (true, j)) => [rj|//] /= _ eqabs eqr.
  case: (eqabs (congr1 Some eqr)) => -[] {eqabs}eqr.
    by move: Hri; rewrite {}eqr -{}Hrj => /(pperm_inj (rperm _) (rperm _)) [].
  have := congr1 (fun x => omap swapsign (Some x)) eqr.
  rewrite -Hri [LHS]ranti /= swapsignK -Hrj.
  by move/(pperm_inj (rperm _) (rperm _)).
have req (i : 'I_n) : omap absval (r (true, i)) = Some (perm_of_RB r i).
  rewrite /perm_of_RB /= (perm_of_transfE r_inj) /= ffunE /= ffunE /=.
  by case: (r (true, i)) (rperm (true, i)).
apply/val_inj/ppermP => /= i; rewrite !ppermE /= !ppermE /=.
case: i => [[]i] /=; rewrite tnth_mktuple.
- case H : (r (true, i)) (rperm (true, i)) => [[/= bi ri]|//] /= _.
  transitivity (Some (bi, perm_of_RB r i)); first by case: bi {H}.
  by have:= req i; rewrite {}H /= => -[] <-.
- case H : (r (true, i)) (rperm (true, i)) => [[/= bi ri]|//] /= _.
  transitivity (Some (~~ bi, perm_of_RB r i)); first by case: bi {H}.
  have /= <- := ranti (true, i).
  by have:= req i; rewrite H /= => -[] <-.
Qed.

Lemma RB_of_ps_bij: {on [pred r : 'RB_n | pperm_is_perm r], bijective RB_of_ps}.
Proof.
exists ps_of_RB; first by apply: in1W; exact: RB_of_psK.
by move=> /= r Hr; rewrite ps_of_RBK.
Qed.
Corollary card_pperm_is_perm :
  #|[pred r : 'RB_n | pperm_is_perm r]| = (n`! * 2 ^ n)%N.
Proof.
rewrite -(on_card_preimset RB_of_ps_bij).
transitivity #|[set: {perm 'I_n} * n.-tuple bool]|.
  congr #|pred_of_set _|; apply/eqP; rewrite -subTset /=.
  apply/subsetP => /= p _; rewrite !inE.
  apply/pperm_is_permP => i; rewrite /= ppermE /= ppermE /=.
  by case: (tnth _ _); case: i.
by rewrite cardsT card_prod /= card_tuple /= card_bool card_Sn.
Qed.

End FromPermutations.




Section Cardinality.

Variable n0 : nat.
Notation n := (n0.+1).
Implicit Types (r s t : 'RB_n) (i j : 'SI_n).

Lemma disjjoint_perm_half :
  [disjoint [pred r : 'RB_n | pperm_is_perm r] & [pred r : 'RB_n | halfpperm r]].
Proof.
rewrite disjoint_subset; apply/subsetP => /= r.
rewrite !inE => /pperm_is_permP alls; apply/negP => /halfppermP halfs.
by have /halfs := alls (true, ord0); rewrite alls.
Qed.

Lemma cardRB_permVhalf :
  #|{: 'RB_n}|
  = #|[pred r : 'RB_n | pperm_is_perm r]| + #|[pred r : 'RB_n | halfpperm r]|.
Proof.
rewrite -cardUI (eqP disjjoint_perm_half) addn0.
apply: eq_card => /= r; rewrite !inE.
by case: r => r /= /orP[/andP[-> _] | /andP[-> _ /[!orbT]]].
Qed.

End Cardinality.

Definition cardRB n :=
  n`! * 2 ^ n + \sum_(k < n.+1) 4 ^ k * 'C(n, k) ^ 2 * k`!.
Definition cardRB_comp n :=
  n`! * 2 ^ n + sumn [seq 4 ^ k * 'C(n, k) ^ 2 * k`! | k <- iota 0 n.+1]%N.
Lemma cardRBE n :
  cardRB n =
    n`! * 2 ^ n + sumn [seq 4 ^ k * 'C(n, k) ^ 2 * k`! | k <- iota 0 n.+1]%N.
Proof.
congr (_ + _); rewrite sumnE big_map big_mknat /index_iota subn0 !big_seq.
apply: eq_bigr => i; rewrite mem_iota /= add0n => lti.
by rewrite inordK.
Qed.

Goal cardRB 1 = 7.     Proof. by rewrite cardRBE; compute. Qed.
Goal cardRB 2 = 57.    Proof. by rewrite cardRBE; compute. Qed.
Goal cardRB 3 = 757.   Proof. by rewrite cardRBE; compute. Qed.
#[warning="-abstract-large-number"]
Goal cardRB 4 = 13889. Proof. by rewrite cardRBE; compute. Qed.
