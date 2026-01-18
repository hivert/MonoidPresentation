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
Lemma halfset_absvalP S : reflect {in S &, injective absval} (halfset S).
Proof.
apply (iffP (halfsetPtf S)) => [H | inj i].
  by move=> [[]i] [[]j] iS jS /= eqij; subst i => //; have:= H j; rewrite iS jS.
apply/negP => /andP[tS fS].
by have /= /(_ (erefl i)) [] := inj _ _ tS fS.
Qed.
Lemma subhalfset S T : S \subset T -> halfset T -> halfset S.
Proof.
move/subsetP => SsubT /halfsetPtf hS; apply/halfsetPtf => i.
by apply/contra: (hS i) => /andP[/SsubT -> /SsubT ->].
Qed.
Lemma halfset_pos : halfset [set bi | bi.1].
Proof. by apply/halfsetPtf => i; rewrite !inE. Qed.

Lemma card_halfset_le S : halfset S -> #|S| <= n.
Proof.
move=> /halfset_absvalP/card_in_imset <-.
by rewrite -[X in _ <= X](card_ord n) subset_leq_card // subset_predT.
Qed.

Lemma card_halfset (k : nat) :
  #|[set S : {set 'BI_n} | #|S| == k & halfset S]| = (2 ^ k * 'C(n, k))%N.
Proof.
rewrite -sum1dep_card.
rewrite [LHS](partition_big_idem _ _ (p := fun S : {set 'BI_n} => absval @: S)
                (Q := fun S : {set 'I_n} => #|S| == k)) => //=; first last.
  by move=> S /andP[cS /halfset_absvalP/card_in_imset ->].
transitivity (\sum_(S  : {set 'I_n} | #|S| == k) 2 ^ k); first last.
  rewrite sum_nat_const /= mulnC; congr(_ * _)%N.
  rewrite -[in RHS](card_ord n) -card_draws.
  by apply: eq_card => S; rewrite inE unfold_in.
apply: eq_bigr => /= S /eqP CS.
rewrite sum1dep_card -[in RHS]CS -card_powerset.
rewrite -(card_in_imset
            (f := fun S => [set i : 'I_n | (true, i) \in S])); first last.
  have mem_setabs T (i : 'I_n) : halfset T ->
      (i \in [set absval x | x in T]) = ((true, i) \in T) (+) ((false, i) \in T).
    move=> /halfsetPtf/(_ i) H.
    apply/imsetP/idP => /= [[[[]j] /[swap] /= <-] |].
    * by move: H=> /[swap] ->.
    * by move: H=> /[swap] ->; rewrite andbT addbT.
    case: (boolP (_ \in T)) H => /= [tinT _ _| _ _ finT].
    * by exists (true, i).
    * by exists (false, i).
  move=> /= T1 T2 /[!inE].
  case/andP => /andP[_ /mem_setabs hT1] /eqP <-.
  case/andP => /andP[_ {}/mem_setabs hT2] /eqP /setP eqabsT /setP eqT.
  apply/setP => [[[]/= i]]; first by have:= eqT i; rewrite !inE.
  move/(_ i): hT1; move/(_ i): hT2; move/(_ i): eqabsT; move/(_ i): eqT.
  rewrite !inE.
  by case: (i \in absval @: _); case: (i \in absval @: _) => //= -> _;
    repeat case: (_ \in _) => //=.
apply eq_card => /= T; rewrite inE.
apply/imsetP/idP => /= [[U /[swap]] {T}-> | /subsetP TsubS].
  rewrite inE => /andP[_ /eqP<-{S CS}].
  by apply/subsetP => i /[!inE] iU; apply/imsetP; exists (true, i).
pose A : {set 'BI_n} := [set bi | (bi.2 \in S) && (bi.1 == (bi.2 \in T))].
exists A; first last.
  rewrite {}/A; apply/setP => i; rewrite !inE /= andbC.
  by case: (boolP (i \in T)) => // /TsubS ->.
have absA : [set absval x | x in A] = S.
  rewrite {}/A /=; apply/setP => i.
  apply/imsetP/idP => /= [[bi /[!inE]/andP[biS _ {i}->] //] | iS].
  by exists (i \in T, i) => //; rewrite inE /= iS /=.
rewrite inE absA eqxx andbT andbC.
have : halfset A.
  rewrite {absA}/A; apply/halfsetPtf => i; rewrite !inE /=.
  by case: (boolP (i \in T)) => [/TsubS -> |] //=; rewrite andbF.
move=> /[dup]/halfset_absvalP/card_in_imset <- -> /=.
by rewrite -CS absA.
Qed.

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

Lemma RennerB0E : all_equal_to (1 : 'RB_0).
Proof. by move=> /= r; apply/val_inj/ppermP => -[/= b []]. Qed.

Lemma card_card_RennerB0 : #|'RB_0| = 1%N.
Proof. by apply/eqP/fintype1P; exists 1; exact RennerB0E. Qed.

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
  rewrite {r}RennerB0E => _; apply/antisymmP => /= -[/= b []] //.
move=> rperm; have:= RennerP r; rewrite /isRennerB.
have:= permVhalf (n := n.+1) is_true_true r.
by rewrite rperm => /= /negbTE->; rewrite orbF.
Qed.

Lemma Renner_half_pcodom n (r : 'RB_n) : halfset (pdom r) -> halfset (pcodom r).
Proof.
case: n r => [|n] r.
  by rewrite {r}RennerB0E => _; rewrite pcodom1; apply/halfsetP => -[b[]].
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
  {in [set r : 'RB_n | pperm_is_perm r], cancel ps_of_RB RB_of_ps}.
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

Lemma RB_of_ps_bij: {on [set r : 'RB_n | pperm_is_perm r], bijective RB_of_ps}.
Proof.
exists ps_of_RB; first by apply: in1W; exact: RB_of_psK.
by move=> /= r Hr; rewrite ps_of_RBK.
Qed.
Corollary card_pperm_is_perm :
  #|[set r : 'RB_n | pperm_is_perm r]| = (n`! * 2 ^ n)%N.
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

From Stdlib Require Import Ring.


Section HalfPerm.

Variable n : nat.
Implicit Types (r s t : 'RB_n) (i j : 'BI_n).

Theorem card_halfRennerB :
  #|[set r : 'RB_n | halfset (pdom r)]| =
     \sum_(k < n.+1) 4 ^ k * 'C(n, k) ^ 2 * k`!.
Proof.
transitivity #|[set tr : pptriple 'BI_n |
                 [&& #|tag tr.1| == #|tr.2|, halfset (tag tr.1) & halfset tr.2]]|.
  rewrite -(card_imset _ (inj_comp (can_inj (@to_pptripleK _)) val_inj)).
  apply eq_card => /= tr; rewrite !inE.
  apply/imsetP/idP => /= => [[x /[!inE] hdomx] {tr}-> /= | Htr].
    by rewrite card_pcodomE eqxx Renner_half_pcodom hdomx.
  case eqtr : tr Htr => [[doms p] codoms] /= /and3P[/eqP eqtag hdom hcodom].
  have rRB : isRennerB (of_pptriple tr).
    apply/orP; right.
    by rewrite eqtr pdom_of_doms_perm ?pcodom_of_doms_perm // hdom hcodom.
  exists (mkRennerB rRB); last by rewrite of_pptripleK eqtr.
  by rewrite inE /= /of_pptriple eqtr /= pdom_of_doms_perm.
rewrite -sum1dep_card.
have cdom_subproof (tr : pptriple 'BI_n) :
  (if #|tag tr.1| <= n then #|tag tr.1| else 0) < n.+1.
  by rewrite ltnS; case: (leqP #|_| _).
pose cdom tr := Ordinal (cdom_subproof tr).
rewrite [LHS](partition_big_idem _ _ (p := cdom) (Q := xpredT)) //=.
apply: eq_bigr => k _; rewrite sum1dep_card.
transitivity ((2 ^ k * 'C(n, k)  * k`!) * (2 ^ k * 'C(n, k)))%N; first last.
  rewrite -!mulnn mulnC !mulnA; congr (_ * _ * _)%N.
  by rewrite mulnC mulnA -expnMn.
transitivity
  #|setX [set pdoms : {x : {set 'BI_n} & 'S_#|x|} |
           (#|tag pdoms| == k) && (halfset (tag pdoms))]
         [set codoms : {set 'BI_n} | (#|codoms| == k) && (halfset codoms)]|.
  rewrite !cardsE /=; apply: eq_card => /= -[[doms p codoms]] /=.
  rewrite unfold_in [RHS]unfold_in !in_set /= -(inj_eq val_inj) /=.
  case: (boolP (halfset doms)) => /= hdoms; last by rewrite !andbF.
  case: (boolP (halfset codoms)) => /= _; last by rewrite !andbF.
  rewrite !andbT andbC (card_halfset_le hdoms).
  by case: eqP => //= ->; rewrite eq_sym.
rewrite {cdom_subproof cdom} cardsX card_halfset; congr (_ * _)%N.
rewrite -(card_in_imset (f := set_perm_of_card k)); first last.
  move=> /= S T /[!inE] => /andP[cS _]/andP[cT _].
  by apply: set_perm_of_card_inj; rewrite inE.
transitivity #|setX [set pdoms : {set 'BI_n} | (#|pdoms| == k) && (halfset pdoms)]
                    [set: 'S_k]|; first last.
  by rewrite cardsX card_halfset cardsE card_Sn.
apply eq_card => -[/= S p].
rewrite !inE /= andbT; apply/imsetP/andP => /= [[[T q]] | [/eqP cs hS]].
  by rewrite inE /= => /andP[cs1 hT] [{S}-> _].
exists (existT _ S (cast_perm (esym cs) p)); first by rewrite inE /= cs eqxx hS.
congr (_, _); case (altP (#|S| =P k)) => [cds|]; last by rewrite cs eqxx.
by rewrite cast_perm_comp cast_perm_id.
Qed.

End HalfPerm.


Section Cardinality.

Variable n0 : nat.
Notation n := (n0.+1).
Implicit Types (r s t : 'RB_n) (i j : 'BI_n).

Lemma disjjoint_perm_half :
  [disjoint
     [set r : 'RB_n | pperm_is_perm r] & [set r : 'RB_n | halfset (pdom r)]].
Proof.
rewrite disjoint_subset; apply/subsetP => /= r.
by rewrite !inE; have /(_ is_true_true) := permVhalf _ r => /[swap] ->.
Qed.

Lemma cardRB_permVhalf :
  #|'RB_n| = #|[set r : 'RB_n | pperm_is_perm r]|
           + #|[set r : 'RB_n | halfset (pdom r)]|.
Proof.
rewrite -cardUI (eqP disjjoint_perm_half) addn0.
apply: eq_card => /= r; rewrite !inE.
by case: r => r /= /orP[/andP[-> _] | /andP[-> _ /[!orbT]]].
Qed.

Theorem card_RennerB :
  #|'RB_n| =   n`! * 2 ^ n + \sum_(k < n.+1) 4 ^ k * 'C(n, k) ^ 2 * k`!.
Proof. by rewrite cardRB_permVhalf card_pperm_is_perm card_halfRennerB. Qed.

End Cardinality.

Definition cardRB_nat n :=
  n`! * 2 ^ n + sumn [seq 4 ^ k * 'C(n, k) ^ 2 * k`! | k <- iota 0 n.+1]%N.

Lemma cardRB_natE n : #|'RB_n.+1| = cardRB_nat n.+1.
Proof.
rewrite card_RennerB.
congr (_ + _); rewrite sumnE big_map big_mknat /index_iota subn0 !big_seq.
apply: eq_bigr => i; rewrite mem_iota /= add0n => lti.
by rewrite inordK.
Qed.

(* [1, 7, 57, 757, 13889, 322021, 8962225, 289928549] *)
Goal #|'RB_1| = 7.     Proof. by rewrite cardRB_natE; compute. Qed.
Goal #|'RB_2| = 57.    Proof. by rewrite cardRB_natE; compute. Qed.
Goal #|'RB_3| = 757.   Proof. by rewrite cardRB_natE; compute. Qed.
#[warning="-abstract-large-number"]
Goal #|'RB_4| = 13889. Proof. by rewrite cardRB_natE; compute. Qed.
