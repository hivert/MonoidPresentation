(** * Monoids *)
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
From mathcomp Require Import all_boot ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope group_scope.

Reserved Notation "'{' 'mmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
    format "{ 'mmorphism'  U  ->  V }").

Reserved Notation "{ 'freemon' T }"  (at level 0, format "{ 'freemon'  T }").
Reserved Notation "[fmon x ]" (at level 0, format "[fmon  x ]").
Reserved Notation "{ 'transf' T }" (at level 0, format "{ 'transf'  T }").
Reserved Notation "{ 'ptransf' T }" (at level 0, format "{ 'ptransf'  T }").
Reserved Notation "{ 'relat' T }" (at level 0, format "{ 'relat'  T }").


Notation "{ 'mmorphism' U -> V }" := (UMagmaMorphism.type U%type V%type)
  : type_scope.


(* TODO : contribute to MathComp *)

(* Commutative magma/semigroups/monoids *)
HB.mixin Record Magma_hasCommutativeMul M of Magma M := {
  mulgC : commutative (@mul M)
}.
#[short(type="comMagmaType")]
HB.structure Definition ComMagma :=
  {M of Magma M & Magma_hasCommutativeMul M}.

HB.structure Definition ComChoiceMagma :=
  {M of ChoiceMagma M & Magma_hasCommutativeMul M}.
#[short(type="subComMagmaType")]
HB.structure Definition SubComMagma (R : magmaType) S :=
  {U of SubMagma R S U & Magma_hasCommutativeMul U}.

#[short(type="comSemigroupType")]
HB.structure Definition ComSemigroup :=
  {M of Semigroup M & Magma_hasCommutativeMul M}.
#[short(type="subComSemigroupType")]
HB.structure Definition SubComSemigroup (R : semigroupType) S :=
  {U of SubSemigroup R S U & Magma_hasCommutativeMul U}.


#[short(type="comBaseUMagmaType")]
HB.structure Definition ComBaseUMagma :=
  {M of BaseUMagma M & Magma_hasCommutativeMul M}.

HB.structure Definition ComChoiceBaseUMagma :=
  {M of ChoiceBaseUMagma M & Magma_hasCommutativeMul M}.
#[short(type="subComBaseUMagmaType")]
HB.structure Definition SubComBaseUMagma (R : umagmaType) S :=
  {U of SubBaseUMagma R S U & Magma_hasCommutativeMul U}.

#[short(type="comUMagmaType")]
HB.structure Definition ComUMagma :=
  {M of UMagma M & Magma_hasCommutativeMul M}.
#[short(type="subComUMagmaType")]
HB.structure Definition SubComUMagma (R : umagmaType) S :=
  {U of SubUMagma R S U & ComChoiceMagma U}.

#[short(type="comMonoidType")]
HB.structure Definition ComMonoid :=
  {M of Monoid M & Magma_hasCommutativeMul M}.
#[short(type="subComMonoidType")]
HB.structure Definition SubComMonoid (R : monoidType) S :=
  {U of SubMonoid R S U & ComMonoid U}.

#[short(type="comBaseGroupType")]
HB.structure Definition ComBaseGroup :=
  {M of BaseGroup M & Magma_hasCommutativeMul M}.
#[short(type="comStarMonoidType")]
HB.structure Definition ComStarMonoid :=
  {M of StarMonoid M & Magma_hasCommutativeMul M}.

#[short(type="comGroupType")]
HB.structure Definition ComGroup :=
  {M of Group M & Magma_hasCommutativeMul M}.
#[short(type="subComGroupType")]
HB.structure Definition SubComGroup (R : groupType) S :=
  {U of SubGroup R S U & ComBaseGroup U}.


HB.factory Record isComMonoid V & Choice V := {
  one : V;
  mul : V -> V -> V;
  mulgA : associative mul;
  mulgC : commutative mul;
  mul1g : left_id one mul;
}.
HB.builders Context V of isComMonoid V.
Let mulg1_fromC : right_id one mul.
Proof. by move=> x; rewrite mulgC mul1g. Qed.
HB.instance Definition _ := isMonoid.Build V mulgA mul1g mulg1_fromC.
HB.instance Definition _ := Magma_hasCommutativeMul.Build V mulgC.
HB.end.


HB.factory Record SubMagma_isSubComMagma (R : comMagmaType) S U
    of SubMagma R S U := {}.
HB.builders Context R S U of SubMagma_isSubComMagma R S U.
Lemma mulgC : @commutative U U *%g.
Proof. by move=> x y; apply: val_inj; rewrite !gmulfM mulgC. Qed.
HB.instance Definition _ := Magma_hasCommutativeMul.Build U mulgC.
HB.end.

HB.factory Record SubSemigroup_isSubComSemigroup (R : comSemigroupType) S U
    of SubSemigroup R S U := {}.
HB.builders Context R S U of SubSemigroup_isSubComSemigroup R S U.
HB.instance Definition _ := SubMagma_isSubComMagma.Build R S U.
HB.end.

HB.factory Record SubUMagma_isSubComUMagma (R : comUMagmaType) S U
    of SubUMagma R S U := {}.
HB.builders Context R S U of SubUMagma_isSubComUMagma R S U.
HB.instance Definition _ := SubMagma_isSubComMagma.Build R S U.
HB.end.

HB.factory Record SubMonoid_isSubComMonoid (R : comMonoidType) S U
    of SubMonoid R S U := {}.
HB.builders Context R S U of SubMonoid_isSubComMonoid R S U.
HB.instance Definition _ := SubMagma_isSubComMagma.Build R S U.
HB.end.



(* Converse M* *)
Section Converse.

HB.instance Definition _ (R : magmaType) :=
  let mul' (x y : R) := y * x in hasMul.Build R^c mul'.
HB.instance Definition _ (R : ChoiceMagma.type) := ChoiceMagma.on R^c.
HB.instance Definition _ (R : semigroupType) :=
  let mulgA' x y z := esym (mulgA z y x) in
  Magma_isSemigroup.Build R^c mulgA'.
HB.instance Definition _ (R : baseUMagmaType) := hasOne.Build R^c 1.
HB.instance Definition _ (R : umagmaType) :=
  BaseUMagma_isUMagma.Build R^c mulg1 mul1g.
HB.instance Definition _ (R : monoidType) := Monoid.on R^c.

End Converse.

(* FIXME: HB.saturate *)
HB.instance Definition _ (R : comMagmaType) :=
  Magma_hasCommutativeMul.Build R^c (fun _ _ => mulgC _ _).
HB.instance Definition _ (R : ComChoiceMagma.type) := ComChoiceMagma.on R^c.
HB.instance Definition _ (R : comSemigroupType) := ComSemigroup.on R^c.
HB.instance Definition _ (R : comBaseUMagmaType) := ComBaseUMagma.on R^c.
HB.instance Definition _ (R : comUMagmaType) := ComUMagma.on R^c.
HB.instance Definition _ (R : comMonoidType) := ComMonoid.on R^c.
(* /FIXME *)


Section FinFunMagma.
Variable (aT : finType).

Lemma ffun_mulC  (rT : comMagmaType) : commutative (@mul {ffun aT -> rT}).
Proof. by move=> f1 f2; apply/ffunP=> a; rewrite !ffunE mulgC. Qed.

HB.instance Definition _  (rT : comMagmaType) :=
  Magma_hasCommutativeMul.Build {ffun aT -> rT} (@ffun_mulC rT).


(* FIXME: HB.saturate *)
HB.instance Definition _ (rT : ComChoiceMagma.type) := ChoiceMagma.on {ffun aT -> rT}.
HB.instance Definition _ (rT : comSemigroupType) := Semigroup.on {ffun aT -> rT}.
HB.instance Definition _ (rT : comBaseUMagmaType) := BaseUMagma.on {ffun aT -> rT}.
HB.instance Definition _ (rT : comUMagmaType) := UMagma.on {ffun aT -> rT}.
HB.instance Definition _ (rT : comMonoidType) := Monoid.on {ffun aT -> rT}.
(* /FIXME *)

End FinFunMagma.


(* A product of commutative m* is a canonical instance of comM* *)
Section ComProduct.

Variable (U V : comMagmaType).
Fact pair_mulC : @commutative (U * V) (U * V) *%g.
Proof. by move=> [x1 y1][x2 y2]; congr (_, _); rewrite mulgC. Qed.
HB.instance Definition _ :=
  Magma_hasCommutativeMul.Build (U * V)%type pair_mulC.

End ComProduct.

(* FIXME: HB.saturate *)
HB.instance Definition _ (U V : ComChoiceMagma.type) := ChoiceMagma.on (U * V)%type.
HB.instance Definition _ (U V : comSemigroupType) := Semigroup.on (U * V)%type.
HB.instance Definition _ (U V : comBaseUMagmaType) := BaseUMagma.on (U * V)%type.
HB.instance Definition _ (U V : comUMagmaType) := UMagma.on (U * V)%type.
HB.instance Definition _ (U V : comMonoidType) := Monoid.on (U * V)%type.
(* /FIXME *)



(* Monoid structure on (seq T) for T a choiceType, aka the free monoid *)
Definition FreeMonoidT (T : choiceType) := seq T.
HB.instance Definition _ (T : choiceType) := Choice.on (FreeMonoidT T).
HB.instance Definition _ (T : choiceType) :=
  isMonoid.Build (FreeMonoidT T) (@catA T) (@cat0s T) (@cats0 T).

Notation "{ 'freemon' T }" := (FreeMonoidT T).
Notation "[fmon x ]" := ([:: x] : {freemon _}).

Lemma FreeMonoidE (T : choiceType) (m : {freemon T}) :
  m = \prod_(i <- m) [fmon i].
Proof.
by elim: m => [|s s0 {1}->]; rewrite ?big_nil // big_cons [RHS]cat1s.
Qed.

(* Universal property for the free monoid *)
Section UniversalProperty.

Variables (T : choiceType) (M : monoidType) (f : T -> M).

Definition univmor (m : {freemon T}) : M := \prod_(i <- m) f i.

Lemma univmor_is_monoid_morphism : monoid_morphism univmor.
Proof. rewrite /univmor; by split => [|x y]; rewrite -?big_cat ?big_nil. Qed.
#[export]
HB.instance Definition _ := isUMagmaMorphism.Build {freemon T} M univmor
  univmor_is_monoid_morphism.
Lemma univmorE x : univmor [fmon x] = f x.
Proof. by rewrite /univmor big_seq1. Qed.
Lemma univmor_uniq (g : {mmorphism {freemon T} -> M}) :
  (forall a : T, g [fmon a] = f a) -> g =1 univmor.
Proof.
move=> eq m; rewrite (FreeMonoidE m) !gmulf_prod; apply: eq_bigr => i _ {m} /=.
by rewrite eq univmorE.
Qed.

Lemma univmor_nil : univmor [::] = 1.
Proof. exact: big_nil. Qed.
Lemma univmor1 a : univmor [fmon a] = f a.
Proof. by rewrite /univmor big_seq1. Qed.
Lemma univmor_cat u v : univmor (u ++ v) = univmor u * univmor v.
Proof. exact: big_cat. Qed.
Lemma univmor_cons a u : univmor (a :: u) = f a * univmor u.
Proof. by rewrite -cat1s univmor_cat univmor1. Qed.
Lemma univmor_rcons u b : univmor (rcons u b) = univmor u * f b.
Proof. by rewrite -cats1 univmor_cat univmor1. Qed.
Lemma univmor_nseq n a : univmor (nseq n a) = (f a) ^+ n.
Proof.
elim: n => [| n IHn] /=; first by rewrite univmor_nil expg0.
by rewrite univmor_cons IHn expgS.
Qed.

End UniversalProperty.

Lemma mmorph_univmorE (T : choiceType) (M : monoidType)
  (f : {mmorphism {freemon T} -> M}) :
  f =1 univmor (fun a : T => f [fmon a]).
Proof.
move=> x; rewrite (FreeMonoidE x).
rewrite !gmulf_prod; apply: eq_bigr => a _ /=.
by rewrite univmorE.
Qed.


(* Monoid structure on the type of finite endofunctions *)
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


(* Monoid structure on the type of partial finite endofunctions *)
Module PartialTransformation.
Section PartialTransformation.

Variable (T : finType).
Definition type := {ffun T -> option T}.
Implicit Types (f g h : type).
#[export]
HB.instance Definition _ := Finite.on type.

Let multr f g : type := finfun (obind f \o g).
Lemma multrE f g x : (multr f g) x = obind f (g x).
Proof. by rewrite ffunE. Qed.
Lemma multrA : associative multr.
Proof.
move=> f g h; apply/ffunP => x; rewrite !multrE /=.
by case: (h x) => [{}x|] //=; rewrite multrE.
Qed.
Lemma mul1tr : left_id (finfun Some) multr.
Proof.
move=> f; apply/ffunP => x; rewrite multrE /=.
by case: (f x) => [{}x|] //=; rewrite ffunE.
Qed.
Lemma multr1 : right_id (finfun Some) multr.
Proof. by move=> f; apply/ffunP => x; rewrite multrE ffunE /=. Qed.
#[export]
HB.instance Definition _ := isMonoid.Build type multrA mul1tr multr1.

End PartialTransformation.

Module Exports.
HB.reexport PartialTransformation.
Section Theory.
Variable (T : finType).
Implicit Types (f g h : type T).
Lemma multrP f g : f * g = finfun (obind f \o g).
Proof. by []. Qed.
Lemma multrE f g x : (f * g) x = obind f (g x).
Proof. exact: multrE. Qed.
Lemma onetrP : (1 : type T) = finfun Some.
Proof. by []. Qed.
End Theory.
End Exports.
End PartialTransformation.
HB.export PartialTransformation.Exports.
Notation "{ 'ptransf' T }" := (PartialTransformation.type T).


(* Monoid structure on the type of binary relations on a finType *)
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
Definition dualrel f : type := [set p | (p.2, p.1) \in f].
Lemma dualrelE f x y : ((x, y) \in dualrel f) = ((y, x) \in f).
Proof. by rewrite inE. Qed.
Lemma dualrelK : involutive dualrel.
Proof. by move=> f; apply/setP => [[x y]]; rewrite !dualrelE. Qed.
Lemma dualrelM f g : dualrel (mulrel f g) = mulrel (dualrel g) (dualrel f).
Proof.
apply/setP => [[x y]]; rewrite dualrelE.
apply/mulrelP/mulrelP => [[z yz_in_f zx_in_g] | [z]].
  by exists z; rewrite dualrelE.
by rewrite !dualrelE => [zx_in_g yz_in_f]; exists z.
Qed.
#[export]
HB.instance Definition _ :=
  isStarMonoid.Build type mulrelA mul1rel dualrelK dualrelM.

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



