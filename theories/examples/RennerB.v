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

Hint Resolve Some_inj : core.

Lemma isSome_omapK (T1 T2 T3 : Type) (f : T1 -> option T2) (g : T2 -> T3) i :
  omap g (f i) -> f i.
Proof. by case: (f i). Qed.


Notation "''BI_' n" := (bool * 'I_n)%type
  (at level 0, n at level 2, format "''BI_' n").

Section SignedInts.

Context {n : nat}.
Implicit Types (bi : 'BI_n) (S T : {set 'BI_n}).

Definition absval bi := bi.2.
Definition swapsign bi : 'BI_n := (~~ bi.1, bi.2).

Lemma absval_swapsign bi : absval (swapsign bi) = absval bi.
Proof. by []. Qed.
Lemma swapsignK : involutive swapsign.
Proof. by rewrite /swapsign => -[i j]; rewrite negbK. Qed.

Lemma omap_absvalE obi obj :
  omap absval obi = omap absval obj -> obi = obj \/ obi = omap swapsign obj.
Proof.
case: obi obj => [[b0 i0]|]/= [[b1 i1]|]//=; last by move=> _; left.
by move=> [->]; case: b0 b1 => [] [] /=; [left|right|right|left].
Qed.

Lemma enum_bool : enum {: bool} = [:: true; false].
Proof. by rewrite enumT /= unlock /=. Qed.


Lemma enum_SInE :
  enum {: 'BI_n} =
    [seq (true, i) | i <- enum 'I_n] ++ [seq (false, i) | i <- enum 'I_n].
Proof. by rewrite enumT /= unlock /= /prod_enum /= enum_bool /= cats0. Qed.

Lemma mem_swapsetE bi S :
  (bi \in [set swapsign x | x in S]) = (swapsign bi \in S).
Proof.
case: bi => [b i].
by rewrite -{1}(swapsignK (b, i)) mem_imset //; apply: (can_inj swapsignK).
Qed.

Definition halfset S := S :&: swapsign @: S == set0.
Lemma halfsetPtf S :
  reflect (forall i : 'I_n, ~~ (((true, i) \in S) && ((false, i) \in S)))
          (halfset S).
Proof.
apply (iffP idP) => [halfS i | ntfinS].
  by have /setP/(_ (true, i))/= := eqP halfS; rewrite !inE mem_swapsetE /= => ->.
apply/eqP/setP => /= -[b i]; rewrite !inE mem_swapsetE.
by have:= ntfinS i; apply: contraNF => /andP[]; case: b => /= []-> ->.
Qed.
Lemma halfsetP S :
  reflect (forall bi : 'BI_n, ~~ ((bi \in S) && (swapsign bi \in S)))
          (halfset S).
Proof.
apply (iffP (halfsetPtf S)) => [H [[]i] | H i]; try exact: H.
by rewrite andbC; apply: H.
Qed.
Lemma subhalfset S T : S \subset T -> halfset T -> halfset S.
Proof.
move/subsetP => SsubT /halfsetPtf hS; apply/halfsetPtf => i.
by apply/contra: (hS i) => /andP[/SsubT -> /SsubT ->].
Qed.
Lemma halfset_pos : halfset [set bi | bi.1].
Proof. by apply/halfsetPtf => i; rewrite !inE. Qed.

End SignedInts.


Section Defs.

Variable n : nat.
Implicit Types (f g : {pperm 'BI_n}) (S T : {set 'BI_n}).

(** From monoid.v: pperm_is_perm f := [forall x : T, isSome (f x)]. *)
Definition antisymm f :=
  [forall i : 'BI_n, omap swapsign (f i) == f (swapsign i)].

Lemma antisymmP f :
  reflect (forall bi, omap swapsign (f bi) = f (swapsign bi)) (antisymm f).
Proof.
apply (iffP idP) => /= [/forallP/= Heq i | Heq]; first by apply/eqP => /=.
by apply/forallP => /= i; have /= -> := Heq i.
Qed.

Lemma antisymm_comp f g : antisymm f -> antisymm g -> antisymm (f * g).
Proof.
move=> /antisymmP fanti /antisymmP ganti; apply/antisymmP => bi.
by rewrite !ppermM /= -fanti; case: (f bi).
Qed.

Lemma imset_halfset f S :
  antisymm f -> halfset S -> halfset (Some @^-1: (f @: S)).
Proof.
move=> /antisymmP fanti /halfsetP Shalf; apply/halfsetP => bi.
rewrite !inE; apply/negP=> /andP[/imsetP[bj bjS eqfbi]].
case/imsetP => [bk bkS] /(congr1 (omap swapsign)) /=.
rewrite swapsignK fanti eqfbi => /pperm_inj1.
rewrite -eqfbi => /(_ is_true_true) eqbj.
by have:= Shalf bk; rewrite bkS -eqbj bjS.
Qed.

Lemma preimset_halfset f S :
  antisymm f -> halfset S -> halfset (f @^-1: (Some @: S)).
Proof.
move=> /antisymmP fanti /halfsetP Shalf; apply/halfsetP => bi.
rewrite !inE; apply/negP=> /andP[/imsetP[bj bjS eqfbi]].
rewrite -(fanti bi) eqfbi /= (mem_imset _ _ Some_inj) => sbjS.
by have:= Shalf bj; rewrite bjS sbjS.
Qed.

Definition isRennerB f :=
  pperm_is_perm f && antisymm f || halfset (pdom f) && halfset (pcodom f).

Record RennerB : predArgType :=
  mkRennerB {renval :> {pperm 'BI_n}; _ : isRennerB renval}.

Lemma RennerP (r : RennerB) : isRennerB r.
Proof. by case: r. Qed.

HB.instance Definition _ := [isSub for renval].
HB.instance Definition _ := [Finite of RennerB by <:].

Lemma RennerB_closed : monoid_closed isRennerB.
Proof.
split => [|/= s t]; rewrite !unfold_in.
  apply/orP; left; apply/andP; split.
    by apply/is_Some_permP => i; rewrite pperm1.
  by apply/antisymmP => i /=; rewrite !pperm1.
case/orP=> [/andP[/pperm_is_permP [ps eqps] santi]|].
  case/orP=> [/andP[/pperm_is_permP [pt eqpt] tanti]|].
    apply/orP; left; apply/andP; split.
      by rewrite -eqps -eqpt -gmulfM perm_to_ppermP.
    exact: antisymm_comp.
  case/andP=> domt codomt.
  apply/orP; right; rewrite pdomM preimset_halfset //=.
  exact/(subhalfset _ codomt)/pcodomM_subset.
case/andP=> doms codoms; case/orP=> [/andP[_ santi]|].
  apply/orP; right; rewrite pcodomM imset_halfset // andbT.
  exact/(subhalfset _ doms)/pdomM_subset.
case/andP=> domt codomt.
apply/orP; right; apply/andP; split.
  exact/(subhalfset _ doms)/pdomM_subset.
exact/(subhalfset _ codomt)/pcodomM_subset.
Qed.
HB.instance Definition _ :=
  SubChoice_isSubMonoid.Build {pperm 'BI_n} isRennerB RennerB RennerB_closed.

End Defs.

Notation "''RB_' n" := (RennerB n)
  (at level 8, n at level 2, format "''RB_' n").


Section Theory.

Lemma RB0E : all_equal_to (1 : 'RB_0).
Proof. by move=> /= r; apply/val_inj/ppermP => -[/= b []]. Qed.

Lemma permVhalf n :
  n != 0 -> forall r : 'RB_n, pperm_is_perm r (+) halfset (pdom r).
Proof.
case: n => // n _; case=> r /=; rewrite /isRennerB.
case: (boolP (pperm_is_perm r)) => /= [+ _ |_  /andP[->] //].
rewrite pperm_is_perm_domE => /eqP->.
by apply/negP =>/halfsetPtf/(_ ord0); rewrite !inE.
Qed.

Lemma Renner_perm_anti n (r : 'RB_n) : pperm_is_perm r -> antisymm r.
Proof.
case: n r => [|n] r.
  rewrite {r}RB0E => _; apply/antisymmP => /= -[/= b []] //.
move=> rperm; have:= RennerP r; rewrite /isRennerB.
have:= permVhalf (n := n.+1) is_true_true r.
by rewrite rperm => /= /negbTE->; rewrite orbF.
Qed.

Lemma Renner_half_pcodom n (r : 'RB_n) : halfset (pdom r) -> halfset (pcodom r).
Proof.
case: n r => [|n] r.
  by rewrite {r}RB0E => _; rewrite pcodom1; apply/halfsetP => -[b[]].
move=> halfdom; have:= RennerP r; rewrite /isRennerB.
have:= permVhalf (n := n.+1) is_true_true r.
by rewrite halfdom addbT => /negbTE-> /=.
Qed.

End Theory.


Section Generators.

Variable (n : nat).

Definition pi_pos_fun (i : 'BI_n) : option 'BI_n := if i.1 then Some i else None.
Local Lemma pdom_pi_pos_fun : pdom pi_pos_fun = [set bi | bi.1].
Proof. by apply/setP=> /= -[[]i]; rewrite mem_pdom inE. Qed.
Local Lemma pcodom_pi_pos_fun : pcodom pi_pos_fun = [set bi | bi.1].
Proof.
apply/setP=> /= -[[]i]; rewrite [RHS]inE /=.
  by apply/pcodomP; exists (true, i).
by apply/negP => /pcodomP[/=-[[]]].
Qed.
Lemma pi_pos_fun_inj : {on isSome &, injective pi_pos_fun}.
Proof. by case=> [[]i][[]j] //= _ _ [->]. Qed.
Lemma pi_pos_subproof : isRennerB (pperm pi_pos_fun_inj).
Proof.
apply/orP; right; rewrite (eq_pdom (ppermE _)) (eq_pcodom (ppermE _)).
by rewrite pdom_pi_pos_fun pcodom_pi_pos_fun halfset_pos.
Qed.
Definition pi_pos := mkRennerB pi_pos_subproof.
Lemma pi_pos_idemp : pi_pos * pi_pos = pi_pos.
Proof.
by apply: val_inj => /=; apply/ppermP => /= -[[]i];
  rewrite ppermM /= !ppermE //= ppermE.
Qed.

Definition sB_fun (i : 'BI_n) : option 'BI_n :=
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
apply: val_inj => /=; apply/ppermP => /= i.
rewrite ppermM /= !ppermE /sB_fun.
case: (altP (\val (absval i) =P 0)) => /= [ieq0 | ineq0].
  by rewrite ppermE /sB_fun absval_swapsign ieq0 eqxx swapsignK pperm1.
by rewrite ppermE /sB_fun (negbTE ineq0) pperm1.
Qed.

End Generators.

Section FromPermutations.

Variable (n : nat).

Implicit Type (p q : {perm 'I_n}) (r s t : 'RB_n).

Definition perm2B_fun p := [fun i : 'BI_n => Some (i.1, p i.2)].
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
  rewrite ?ppermE ?pperm1 ?ppermM /= !(perm1, permM) //= ppermE /= ppermE.
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
  apply/is_Some_permP => /= i; rewrite !ppermE /= ppermE /=.
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
move/is_Some_permP in rperm.
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
  apply/is_Some_permP => i; rewrite /= ppermE /= ppermE /=.
  by case: (tnth _ _); case: i.
by rewrite cardsT card_prod /= card_tuple /= card_bool card_Sn.
Qed.

End FromPermutations.




Section Cardinality.

Variable n0 : nat.
Notation n := (n0.+1).
Implicit Types (r s t : 'RB_n) (i j : 'BI_n).

Lemma disjjoint_perm_half :
  [disjoint
     [pred r : 'RB_n | pperm_is_perm r] & [pred r : 'RB_n | halfset (pdom r)]].
Proof.
rewrite disjoint_subset; apply/subsetP => /= r.
by rewrite !inE; have /(_ is_true_true) := permVhalf _ r => /[swap] ->.
Qed.

Lemma cardRB_permVhalf :
  #|{: 'RB_n}|
  = #|[pred r : 'RB_n | pperm_is_perm r]| + #|[pred r : 'RB_n | halfset (pdom r)]|.
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
