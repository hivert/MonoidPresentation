(** * Monoids *)
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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice bigop fintype finfun finset ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "'{' 'mmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'mmorphism'  U  ->  V }").
Reserved Notation "{ 'freemon' T }"  (at level 0, format "{ 'freemon'  T }").
Reserved Notation "[fmon x ]" (at level 0, format "[fmon  x ]").
Reserved Notation "{ 'transf' T }" (at level 0, format "{ 'transf'  T }").
Reserved Notation "{ 'relat' T }" (at level 0, format "{ 'relat'  T }").


Declare Scope monoid_scope.
Delimit Scope monoid_scope with M.
Local Open Scope monoid_scope.


HB.mixin Record isMonoid V := {
  one : V;
  mul : V -> V -> V;
  mulmA : associative mul;
  mul1m : left_id one mul;
  mulm1 : right_id one mul;
}.
#[short(type="monoidType")]
HB.structure Definition Monoid := {V of isMonoid V & Choice V}.

Arguments mulmA {V} : rename.
Arguments mul1m {V} : rename.
Arguments mulm1 {V} : rename.

Bind Scope monoid_scope with Monoid.sort.


Notation "1" := (@one _) : monoid_scope.
Notation "1%M" := (@one _) : monoid_scope.
Notation "*%M" := (@mul _) : function_scope.

#[export]
HB.instance Definition _ (V : monoidType) :=
  Monoid.isLaw.Build V 1 *%M mulmA mul1m mulm1.

Definition exp M x n := iterop n (@mul M) x (@one M).
Arguments exp : simpl never.
Definition comm M x y := @mul M x y = mul y x.

Notation "x * y" := (mul x y) : monoid_scope.
Notation "x ^+ n" := (exp x n) : monoid_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%M/1%M]_(i <- r | P%B) F%M) : monoid_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%M/1%M]_(i <- r) F%M) : monoid_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%M/1%M]_(m <= i < n | P%B) F%M) : monoid_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%M/1%M]_(m <= i < n) F%M) : monoid_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%M/1%M]_(i | P%B) F%M) : monoid_scope.
Notation "\prod_ i F" :=
  (\big[*%M/1%M]_i F%M) : monoid_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%M/1%M]_(i : t | P%B) F%M) (only parsing) : monoid_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%M/1%M]_(i : t) F%M) (only parsing) : monoid_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%M/1%M]_(i < n | P%B) F%M) : monoid_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%M/1%M]_(i < n) F%M) : monoid_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%M/1%M]_(i in A | P%B) F%M) : monoid_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%M/1%M]_(i in A) F%M) : monoid_scope.

Section MonoidTheory.

Variable M : monoidType.
Implicit Types x y : M.

Lemma expm0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expm1 x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expm2 x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma expmS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulm1. Qed.

Lemma expm1n n : 1 ^+ n = 1 :> M.
Proof. by elim: n => // n IHn; rewrite expmS mul1m. Qed.

Lemma expmD x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof. by elim: m => [|m IHm]; rewrite ?mul1m // !expmS -mulmA -IHm. Qed.

Lemma expmSm x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 expmD expm1. Qed.

Lemma expm_sum x (I : Type) (s : seq I) (P : pred I) F :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ F i :> M.
Proof. exact: (big_morph _ (expmD _)). Qed.

Lemma commm_sym x y : comm x y -> comm y x. Proof. by []. Qed.
Lemma commm_refl x : comm x x. Proof. by []. Qed.

Lemma commm1 x : comm x 1.
Proof. by rewrite /comm mulm1 mul1m. Qed.

Lemma commmM x y z : comm x y -> comm x z -> comm x (y * z).
Proof. by move=> com_xy; rewrite /comm mulmA com_xy -!mulmA => ->. Qed.

Lemma commm_prod (I : Type) (s : seq I) (P : pred I) (F : I -> M) x :
  (forall i, P i -> comm x (F i)) -> comm x (\prod_(i <- s | P i) F i).
Proof. exact: (big_ind _ (commm1 x) (@commmM x)). Qed.

Lemma commmX x y n : comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commm1 // expmS commmM.
Qed.

Lemma expmMn_comm x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> com_xy; elim: n => /= [|n IHn]; first by rewrite mulm1.
by rewrite !expmS IHn !mulmA; congr (_ * _); rewrite -!mulmA -commmX.
Qed.

Lemma expmM x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite expm1n.
by rewrite mulSn expmD IHm expmS expmMn_comm //; apply: commmX.
Qed.

Lemma expmAC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Proof. by rewrite -!expmM mulnC. Qed.

Lemma iter_mulm n x y : iter n ( *%M x) y = x ^+ n * y.
Proof. by elim: n => [|n ih]; rewrite ?expm0 ?mul1m //= ih expmS -mulmA. Qed.

Lemma iter_mulm_1 n x : iter n ( *%M x) 1 = x ^+ n.
Proof. by rewrite iter_mulm mulm1. Qed.

End MonoidTheory.


HB.mixin Record Monoid_hasCommutativeMul M of Monoid M := {
  mulmC : commutative (@mul M)
}.
#[short(type="comMonoidType")]
HB.structure Definition ComMonoid :=
  {M of Monoid M & Monoid_hasCommutativeMul M}.

Bind Scope monoid_scope with ComMonoid.sort.

HB.factory Record isComMonoid V & Choice V := {
  one : V;
  mul : V -> V -> V;
  mulmA : associative mul;
  mulmC : commutative mul;
  mul1m : left_id one mul;
}.
HB.builders Context V of isComMonoid V.
Let mulm1_fromC : right_id one mul.
Proof. by move=> x; rewrite mulmC mul1m. Qed.
HB.instance Definition _ := isMonoid.Build V mulmA mul1m mulm1_fromC.
HB.instance Definition _ := Monoid_hasCommutativeMul.Build V mulmC.
HB.end.


Definition monmorphism (R S : monoidType) (f : R -> S) : Prop :=
  (f 1 = 1) * {morph f : x y / x * y}.

HB.mixin Record isMonMorphism (R S : monoidType) (f : R -> S) := {
  monmorphism_subproof : monmorphism f
}.

HB.structure Definition MonMorphism (R S : monoidType) :=
  {f of isMonMorphism R S f}.

Module MonMorphismExports.
Notation "{ 'mmorphism' U -> V }" := (MonMorphism.type U%type V%type)
  : type_scope.
End MonMorphismExports.
HB.export MonMorphismExports.


Section MonMorphismTheory.

Section Properties.

Variables (R S : monoidType) (f : {mmorphism R -> S}).

Lemma mmorphismMP : monmorphism f. Proof. exact: monmorphism_subproof. Qed.
Lemma mmorph1 : f 1 = 1. Proof. by case: mmorphismMP. Qed.
Lemma mmorphM : {morph f: x y  / x * y}. Proof. by case: mmorphismMP. Qed.

Lemma mmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Proof. exact: (big_morph f mmorphM mmorph1). Qed.

Lemma mmorphXn n : {morph f : x / x ^+ n}.
Proof. by elim: n => [|n IHn] x; rewrite ?mmorph1 // !expmS mmorphM IHn. Qed.

Lemma can2_mmorphism f' : cancel f f' -> cancel f' f -> monmorphism f'.
Proof.
move=> fK f'K.
by split=> [|x y]; apply: (canLR fK); rewrite /= (mmorphM, mmorph1) ?f'K.
Qed.

End Properties.

Section Projections.

Variables (R S T : monoidType).
Variables (f : {mmorphism S -> T}) (g : {mmorphism R -> S}).

Fact idfun_is_monmorphism : monmorphism (@idfun R).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMonMorphism.Build R R idfun
  idfun_is_monmorphism.

Fact comp_is_monmorphism : monmorphism (f \o g).
Proof. by split=> [|x y] /=; rewrite ?mmorph1 ?mmorphM. Qed.
#[export]
HB.instance Definition _ := isMonMorphism.Build R T (f \o g)
  comp_is_monmorphism.

End Projections.

End MonMorphismTheory.


Section Predicates.
Variable (R : monoidType) (S : {pred R}).

Definition mulm_2closed := {in S &, forall u v, u * v \in S}.
Definition mulm_closed := 1 \in S /\ mulm_2closed.

End Predicates.

HB.mixin Record isMulm2Closed (R : monoidType) (S : {pred R}) := {
  mpredM : mulm_2closed S
}.

HB.mixin Record isMulm1Closed (R : monoidType) (S : {pred R}) := {
  mpred1 : 1 \in S
}.

(* Structures for stability properties *)

#[short(type="mulm2Closed")]
HB.structure Definition Mulm2Closed R := {S of isMulm2Closed R S}.

#[short(type="mulmClosed")]
HB.structure Definition MulmClosed R := {S of Mulm2Closed R S & isMulm1Closed R S}.

HB.factory Record isMulmClosed (R : monoidType) (S : {pred R}) := {
  mpred1M : mulm_closed S
}.

HB.builders Context R S of isMulmClosed R S.
HB.instance Definition _ := isMulm2Closed.Build R S (proj2 mpred1M).
HB.instance Definition _ := isMulm1Closed.Build R S (proj1 mpred1M).
HB.end.


Section MonoidPred.

Variables (R : monoidType).

Variable S : mulmClosed R.

Lemma mpred1M : mulm_closed S.
Proof. exact: (conj mpred1 mpredM). Qed.

Lemma mpred_prod I r (P : pred I) F :
  (forall i, P i -> F i \in S) -> \prod_(i <- r | P i) F i \in S.
Proof. by move=> IH; elim/big_ind: _; [apply: mpred1 | apply: mpredM |]. Qed.

Lemma mpredX n : {in S, forall u, u ^+ n \in S}.
Proof.
move=> u Su; rewrite -iter_mulm_1.
by elim: n => [|n IHn]; [exact: mpred1 | exact: mpredM].
Qed.

End MonoidPred.


HB.mixin Record isSubMonoid (R : monoidType) (S : pred R) U
    of SubChoice R S U & Monoid U := {
  valM_subproof : monmorphism (val : U -> R);
}.
#[short(type="subMonoidType")]
HB.structure Definition SubMonoid (R : monoidType) (S : pred R) :=
  { U of SubChoice R S U & Monoid U & isSubMonoid R S U }.

Section multiplicative.
Context (R : monoidType) (S : pred R) (U : SubMonoid.type S).
Notation val := (val : U -> R).
#[export]
HB.instance Definition _ := isMonMorphism.Build U R val valM_subproof.
Lemma val1 : val 1 = 1. Proof. exact: mmorph1. Qed.
Lemma valM : {morph val : x y / x * y}. Proof. exact: mmorphM. Qed.
Lemma valM1 : monmorphism val. Proof. exact: valM_subproof. Qed.
End multiplicative.

HB.factory Record SubChoice_isSubMonoid (R : monoidType) S U
    of SubChoice R S U := {
  mulm_closed_subproof : mulm_closed S
}.
HB.builders Context R S U of SubChoice_isSubMonoid R S U.

HB.instance Definition _ := isMulmClosed.Build R S mulm_closed_subproof.

Let inU v Sv : U := Sub v Sv.
Let oneU : U := inU (@mpred1 _ (MulmClosed.clone R S _)).
Let mulU (u1 u2 : U) := inU (mpredM _ _ (valP u1) (valP u2)).

Lemma mulrA : associative mulU.
Proof. by move=> x y z; apply: val_inj; rewrite !SubK mulmA. Qed.
Lemma mul1r : left_id oneU mulU.
Proof. by move=> x; apply: val_inj; rewrite !SubK mul1m. Qed.
Lemma mulr1 : right_id oneU mulU.
Proof. by move=> x; apply: val_inj; rewrite !SubK mulm1. Qed.
HB.instance Definition _ := isMonoid.Build U mulrA mul1r mulr1.

Lemma valM : monmorphism (val : U -> R).
Proof. by split=> [|x y] /=; rewrite !SubK. Qed.
HB.instance Definition _ := isSubMonoid.Build R S U valM.
HB.end.

                                                           
#[short(type="subComMonoidType")]
HB.structure Definition SubComMonoid (R : monoidType) S :=
  {U of SubMonoid R S U & ComMonoid U}.

HB.factory Record SubMonoid_isSubComMonoid (R : comMonoidType) S U
    of SubMonoid R S U := {}.

HB.builders Context R S U of SubMonoid_isSubComMonoid R S U.
Lemma mulmC : @commutative U U *%M.
Proof. by move=> x y; apply: val_inj; rewrite !mmorphM mulmC. Qed.
HB.instance Definition _ := Monoid_hasCommutativeMul.Build U mulmC.
HB.end.


Definition FreeMonoidT (a : choiceType) := seq a.
HB.instance Definition _ (a : choiceType) := Choice.on (FreeMonoidT a).
HB.instance Definition _ (a : choiceType) :=
  isMonoid.Build (FreeMonoidT a) (@catA a) (@cat0s a) (@cats0 a).

Notation "{ 'freemon' T }" := (FreeMonoidT T).
Notation "[fmon x ]" := ([:: x] : {freemon _}).

Lemma FreeMonoidE (a : choiceType) (x : {freemon a}) :
  x = \prod_(i <- x) [fmon i].
Proof.
by elim: x => [|s s0 {1}->]; rewrite ?big_nil // big_cons [RHS]cat1s.
Qed.

Section UniversalProperty.

Variables (A : choiceType) (M : monoidType) (f : A -> M).

Definition univmap (m : {freemon A}) : M := \prod_(i <- m) f i.

Lemma univmap_is_monmorphism : monmorphism univmap.
Proof. rewrite /univmap; by split => [|x y]; rewrite -?big_cat ?big_nil. Qed.
#[export]
HB.instance Definition _ := isMonMorphism.Build {freemon A} M univmap
  univmap_is_monmorphism.
Lemma univmapE x : univmap [fmon x] = f x.
Proof. by rewrite /univmap big_seq1. Qed.
Lemma univmap_uniq (g : {mmorphism {freemon A} -> M}) :
  (forall a : A, g [fmon a] = f a) -> g =1 univmap.
Proof.
move=> eq m; rewrite (FreeMonoidE m) !mmorph_prod; apply: eq_bigr => i _ {m} /=.
by rewrite eq univmapE.
Qed.

End UniversalProperty.


Module Transformation.
Section Transformation.

Variable (T : finType).
Definition type := {ffun T -> T}.
Implicit Types (f g h : type).
#[export]
HB.instance Definition _ := Finite.on type.

Let multr f g : type := finfun (f \o g).
Lemma multrE f g x : (multr f g) x = f (g x).
Proof. by rewrite ffunE. Qed.
Lemma multrA : associative multr.
Proof. by move=> f g h; apply/ffunP => x; rewrite !multrE. Qed.
Lemma mul1tr : left_id (finfun id) multr.
Proof. by move=> f; apply/ffunP => x; rewrite !(multrE, ffunE). Qed.
Lemma multr1 : right_id (finfun id) multr.
Proof. by move=> f; apply/ffunP => x; rewrite !(multrE, ffunE). Qed.
#[export]
HB.instance Definition _ := isMonoid.Build type multrA mul1tr multr1.

End Transformation.

Module Exports.
HB.reexport Transformation.
Section Theory.
Variable (T : finType).
Implicit Types (f g h : type T).
Lemma multrP f g : f * g = finfun (f \o g).
Proof. by []. Qed.
Lemma multrE f g x : (f * g) x = f (g x).
Proof. exact: multrE. Qed.
Lemma onetrP : (1 : type T) = finfun id.
Proof. by []. Qed.
End Theory.
End Exports.
End Transformation.
HB.export Transformation.Exports.
Notation "{ 'transf' T }" := (Transformation.type T).


Module Relation.
Section Relation.

Variable (T : finType).
Definition type := {set T * T}.
Implicit Types (f g h : type).
#[export]
HB.instance Definition _ := Finite.on type.

Let onerel : type := [set p | p.1 == p.2].
Let mulrel f g : type :=
      [set p | [exists (y | (p.1, y) \in f), (y, p.2) \in g]].
Lemma onerelE x y : (x, y) \in onerel = (x == y).
Proof. by rewrite inE. Qed.
Lemma mulrelP f g x y :
  reflect (exists2 z : T, (x, z) \in f & (z, y) \in g) ((x, y) \in mulrel f g).
Proof. by rewrite /mulrel inE; apply (iffP exists_inP). Qed.
Lemma mulrelA : associative mulrel.
Proof.
move=> f g h; apply/setP => [[x y]].
apply/mulrelP/mulrelP => [[z xz_in_f /mulrelP[t zt_in_g ty_in_h]]|].
  by exists t => //; apply/mulrelP; exists z.
move=> [t/mulrelP[z xz_in_f zt_in_g ty_in_h]].
by exists z => //; apply/mulrelP; exists t.
Qed.
Lemma mul1rel : left_id onerel mulrel.
Proof.
move=> f; apply/setP => [[x y]]; rewrite inE.
apply/existsP/idP => [[z /= /andP[/[!onerelE] /eqP ->]] // | xy_in_f /=].
by exists x; rewrite onerelE eqxx.
Qed.
Lemma mulrel1 : right_id onerel mulrel.
Proof.
move=> f; apply/setP => [[x y]]; rewrite inE.
apply/existsP/idP => [[z /andP[/[swap]/[!onerelE] /eqP ->]] // | xy_in_f /=].
by exists y; rewrite onerelE eqxx andbT.
Qed.
#[export]
HB.instance Definition _ := isMonoid.Build type mulrelA mul1rel mulrel1.

End Relation.

Module Exports.
HB.reexport Relation.
Section Theory.
Variable (T : finType).
Implicit Types (f g h : type T).

Lemma onerelE x y : (x, y) \in (1 : type T) = (x == y).
Proof. exact: onerelE. Qed.
Lemma mulrelP f g x y :
  reflect (exists2 z : T, (x, z) \in f & (z, y) \in g) ((x, y) \in f * g).
Proof. exact: mulrelP. Qed.

End Theory.
End Exports.
End Relation.
HB.export Relation.Exports.
Notation "{ 'relat' T }" := (Relation.type T).


Section RelatTheory.
Variable (T : finType).
Implicit Types (f g h : {relat T}).

Definition dualrel f : {relat T} := [set p | (p.2, p.1) \in f].
Lemma dualrelE f x y : ((x, y) \in dualrel f) = ((y, x) \in f).
Proof. by rewrite inE. Qed.
Lemma dualrelK : involutive dualrel.
Proof. by move=> f; apply/setP => [[x y]]; rewrite !dualrelE. Qed.
Lemma dualrel1 : dualrel 1 = 1 :> {relat T}.
Proof. by apply/setP=> [[x y]]; rewrite dualrelE !onerelE eq_sym. Qed.
Lemma dualrelM f g : dualrel (f * g) = dualrel g * dualrel f.
Proof.
apply/setP => [[x y]]; rewrite dualrelE.
apply/mulrelP/mulrelP => [[z yz_in_f zx_in_g] | [z]].
  by exists z; rewrite dualrelE.
by rewrite !dualrelE => [zx_in_g yz_in_f]; exists z.
Qed.
End RelatTheory.


Import GRing.Theory.

Local Open Scope ring_scope.

Record multMon (R : semiRingType) := MkMultMon { multmonval : R }.
Coercion to_multMon (R : semiRingType) (x : R) := MkMultMon x.
Lemma to_multMonK R : cancel (@MkMultMon R) (@multmonval R).
Proof. by []. Qed.
HB.instance Definition _ R := [isNew of multMon R for @multmonval R].
HB.instance Definition _ R := [Choice of multMon R by <:].

Module Monoid_of_SemiRing.

Section CanonicalSR.

Variable R : semiRingType.
Implicit Type (x y : multMon R).

Let one : multMon R := 1%R.
Let mul x y : multMon R := (\val x * \val y)%R.
Fact mulmA : associative mul.
Proof. move=> x y z; apply val_inj; exact: mulrA. Qed.
Fact mul1m : left_id one mul.
Proof. move=> x; apply val_inj; exact: mul1r. Qed.
Fact mulm1 : right_id one mul.
Proof. move=> x; apply val_inj; exact: mulr1. Qed.
#[export]
HB.instance Definition _ := isMonoid.Build (multMon R) mulmA mul1m mulm1.

End CanonicalSR.

Section CanonicalCSR.

Variable R : comSemiRingType.
Implicit Type (x y : multMon R).

Fact mulmC : commutative (@mul (multMon R)).
Proof. move=> x y; apply val_inj; exact: mulrC. Qed.
#[export]
HB.instance Definition _ :=
  Monoid_hasCommutativeMul.Build (multMon R) mulmC.

End CanonicalCSR.

Module Exports.
HB.reexport Monoid_of_SemiRing.
Notation multMon R := (multMon R).

Section Theory.

Variable R : semiRingType.
Implicit Type (x y : multMon R).

Lemma monE : (1%M : multMon R) = 1%R. Proof. by []. Qed.
Lemma monME x y : (x * y)%M = (\val x * \val y)%R. Proof. by []. Qed.
Lemma tomonE (x : R) : (to_multMon x) = x. Proof. by []. Qed.

End Theory.
End Exports.
End Monoid_of_SemiRing.
HB.export Monoid_of_SemiRing.Exports.


Section Functoriality.

Variable (R S : semiRingType) (f : {rmorphism R -> S}).

Definition multMon_mor (r : multMon R) : multMon S := to_multMon (f (val r)).
Fact multMon_mor_monmorphism : monmorphism multMon_mor.
Proof.
rewrite /multMon_mor; split; first by rewrite !monE /= rmorph1.
by move=> x y; rewrite !monME rmorphM.
Qed.
HB.instance Definition _ :=
  isMonMorphism.Build (multMon R) (multMon S) multMon_mor multMon_mor_monmorphism.

End Functoriality.


Section ConverseMonoid.

HB.instance Definition _ (R : monoidType) :=
  let mul' (x y : R) := (y * x)%M in
  let mulmA' x y z := esym (mulmA z y x) in
  isMonoid.Build R^c (mulmA' : associative mul') mulm1 mul1m.

HB.instance Definition _ (R : comMonoidType) :=
  Monoid_hasCommutativeMul.Build R^c (fun _ _ => mulmC _ _).

End ConverseMonoid.


Section Product.

Variable (U V : monoidType).

Definition mul_pair (x y : U * V) := (x.1 * y.1, x.2 * y.2)%M.

Fact pair_mul1m : left_id (1, 1)%M mul_pair.
Proof. by move=> [x y]; congr (_, _); apply: mul1m. Qed.
Fact pair_mulm1 : right_id (1, 1)%M mul_pair.
Proof. by move=> [x y]; congr (_, _); apply: mulm1. Qed.
Fact pair_mulA : associative mul_pair.
Proof. by move=> x y z; congr (_, _); apply: mulmA. Qed.
HB.instance Definition _ :=
  isMonoid.Build (U * V)%type pair_mulA pair_mul1m pair_mulm1.

End Product.


Section ComProduct.

Variable (U V : comMonoidType).
Fact pair_mulC : @commutative (U * V) (U * V) ( *%M ).
Proof. by move=> [x1 y1][x2 y2]; congr (_, _); rewrite mulmC. Qed.
HB.instance Definition _ :=
  Monoid_hasCommutativeMul.Build (U * V)%type pair_mulC.

End ComProduct.
