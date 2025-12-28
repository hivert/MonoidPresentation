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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice bigop fintype finfun finset ssralg monoid.
From mathcomp Require Import fingroup perm.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

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

(* Commutative monoids *)
HB.mixin Record Magma_hasCommutativeMul M of Magma M := {
  mulgC : commutative (@mul M)
}.
#[short(type="comMagmaType")]
HB.structure Definition ComMagma :=
  {M of Magma M & Magma_hasCommutativeMul M}.

#[short(type="comUMagmaType")]
HB.structure Definition ComUMagma :=
  {M of UMagma M & Magma_hasCommutativeMul M}.

#[short(type="comMonoidType")]
HB.structure Definition ComMonoid :=
  {M of Monoid M & Magma_hasCommutativeMul M}.


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


Notation "{ 'mmorphism' U -> V }" := (UMagmaMorphism.type U%type V%type)
  : type_scope.

(*
Notation mmorph1 := gmulf1.
Notation mmorphM := gmulfM.
Notation mmorph_prod := gmulf_prod.
Notation mmorphXn := gmulfXn.
*)

(* Sub commutative monoids *)
#[short(type="subComMonoidType")]
HB.structure Definition SubComMonoid (R : monoidType) S :=
  {U of SubMonoid R S U & ComMonoid U}.

HB.factory Record SubMonoid_isSubComMonoid (R : comMonoidType) S U
    of SubMonoid R S U := {}.

HB.builders Context R S U of SubMonoid_isSubComMonoid R S U.
Lemma mulgC : @commutative U U *%g.
Proof. by move=> x y; apply: val_inj; rewrite !gmulfM mulgC. Qed.
HB.instance Definition _ := Magma_hasCommutativeMul.Build U mulgC.
HB.end.

(* Monoid structure on (seq T) for T a choiceType, aka the free monoid *)
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

(* Universal property for the free monoid *)
Section UniversalProperty.

Variables (A : choiceType) (M : monoidType) (f : A -> M).

Definition univmor (m : {freemon A}) : M := \prod_(i <- m) f i.

Lemma univmor_is_monoid_morphism : monoid_morphism univmor.
Proof. rewrite /univmor; by split => [|x y]; rewrite -?big_cat ?big_nil. Qed.
#[export]
HB.instance Definition _ := isUMagmaMorphism.Build {freemon A} M univmor
  univmor_is_monoid_morphism.
Lemma univmorE x : univmor [fmon x] = f x.
Proof. by rewrite /univmor big_seq1. Qed.
Lemma univmor_uniq (g : {mmorphism {freemon A} -> M}) :
  (forall a : A, g [fmon a] = f a) -> g =1 univmor.
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

Lemma mmorph_univmorE (A : choiceType) (M : monoidType)
  (f : {mmorphism {freemon A} -> M}) :
  f =1 univmor (fun a : A => f [fmon a]).
Proof.
move=> x; rewrite (FreeMonoidE x).
rewrite !gmulf_prod; apply: eq_bigr => a _ /=.
by rewrite univmorE.
Qed.


(* Monoid structure on finite endofunctions *)
Module Transformation.
Section Transformation.

Variable (T : finType).
Definition type := {ffun T -> T}.
Implicit Types (f g h : type).
#[export]
HB.instance Definition _ := Finite.on type.

Let multr f g : type := finfun (g \o f).
Lemma multrE f g x : (multr f g) x = g (f x).
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
Lemma multrP f g : f * g = finfun (g \o f).
Proof. by []. Qed.
Lemma multrE f g x : (f * g) x = g (f x).
Proof. exact: multrE. Qed.
Lemma onetrP : (1 : type T) = finfun id.
Proof. by []. Qed.
End Theory.
End Exports.
End Transformation.
HB.export Transformation.Exports.
Notation "{ 'transf' T }" := (Transformation.type T).


(* Monoid structure on partial finite endofunctions *)
Module PartialTransformation.
Section PartialTransformation.

Variable (T : finType).
Definition type := {ffun T -> option T}.
Implicit Types (f g h : type).
#[export]
HB.instance Definition _ := Finite.on type.

Let multr f g : type := finfun (obind g \o f).
Lemma multrE f g x : (multr f g) x = obind g (f x).
Proof. by rewrite ffunE. Qed.
Lemma multrA : associative multr.
Proof.
move=> f g h; apply/ffunP => x; rewrite !multrE /=.
by case: (f x) => [{}x|] //=; rewrite multrE.
Qed.
Lemma mul1tr : left_id (finfun Some) multr.
Proof.
by move=> f; apply/ffunP => x; rewrite multrE /= ffunE.
Qed.
Lemma multr1 : right_id (finfun Some) multr.
Proof.
move=> f; apply/ffunP => x; rewrite multrE /= /obind /oapp.
by case: (f x) => // {}x; rewrite ffunE.
Qed.
#[export]
HB.instance Definition _ := isMonoid.Build type multrA mul1tr multr1.

End PartialTransformation.

Module Exports.
HB.reexport PartialTransformation.
Section Theory.
Variable (T : finType).
Implicit Types (f g h : type T).
Lemma multrP f g : f * g = finfun (obind g \o f).
Proof. by []. Qed.
Lemma multrE f g x : (f * g) x = obind g (f x).
Proof. exact: multrE. Qed.
Lemma onetrP : (1 : type T) = finfun Some.
Proof. by []. Qed.
End Theory.
End Exports.
End PartialTransformation.
HB.export PartialTransformation.Exports.
Notation "{ 'ptransf' T }" := (PartialTransformation.type T).


(** The transformation monoid over T is a submonoid *)
(** of the partial tranformation monoid over T      *)
Section TranfToPTransf.

Context {T : finType}.
Implicit Types (f g h : {transf T}) (p q : {ptransf T}).

Definition to_ptransf f : {ptransf T} := finfun (olift f).
Definition of_ptransf p : {transf T} :=
  finfun [fun x => if p x is Some y then y else x].
Lemma to_ptransfE f x : to_ptransf f x = Some (f x).
Proof. by rewrite ffunE. Qed.
Lemma to_ptransf_is_monoid_morphism : monoid_morphism to_ptransf.
Proof.
split=> [| /= f g].
- by apply/ffunP=> x; rewrite !ffunE /olift ffunE.
- apply/ffunP=> x; rewrite !ffunE /= /olift.
  by rewrite /obind /oapp /= !to_ptransfE ffunE /=.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {transf T} {ptransf T}
    to_ptransf to_ptransf_is_monoid_morphism.
Lemma to_ptransfK : cancel to_ptransf of_ptransf.
Proof. by move=> f; apply/ffunP => x; rewrite !ffunE /= to_ptransfE. Qed.

End TranfToPTransf.


(** The partial transformation monoid over T is a submonoid *)
(** of the monoid of tranformation over option T            *)
Section PTranfToTransfOpt.

Context {T : finType}.
Implicit Types (f g h : {ptransf T}) (p q : {transf option T}).

Definition to_transfopt f : {transf option T} := finfun (oapp f None).
Definition of_transfopt p : {ptransf T } := finfun (fun x => p (Some x)).
Lemma to_transfoptN f : to_transfopt f None = None.
Proof. by rewrite ffunE. Qed.
Lemma to_transfoptE f x : to_transfopt f (Some x) = f x.
Proof. by rewrite ffunE. Qed.
Lemma to_transfopt_is_monoid_morphism : monoid_morphism to_transfopt.
Proof.
split=> [| /= f g]; apply/ffunP => -[x|]; rewrite !ffunE //= ffunE //=.
- by rewrite !to_transfoptE; case: (f x) => [{}x|] /=; rewrite !ffunE /=.
- by rewrite to_transfoptN.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {ptransf T} {transf option T}
    to_transfopt to_transfopt_is_monoid_morphism.
Lemma to_transfoptK : cancel to_transfopt of_transfopt.
Proof. by move=> f; apply/ffunP => x /=; rewrite !ffunE /=. Qed.

End PTranfToTransfOpt.


(** The symmetric group is a submonoid of the tranformation monoid *)
Section PermToTransf.

Local Open Scope group_scope.

Context {T : finType}.
Implicit Types (f g h : {transf T}) (p q : {perm T}).

Definition perm_to_transf p : {transf T} := \val p.
Definition perm_of_transf f : {perm T} :=
  if boolP (injectiveb f) is AltTrue pf then Perm pf else 1.
Lemma perm_to_transfE p : perm_to_transf p =1 p :> (T -> T).
Proof. by move=> x; rewrite /perm_to_transf /= pvalE. Qed.

Lemma perm_to_transf_is_monoid_morphism : monoid_morphism perm_to_transf.
Proof.
split=> [| /= f g].
- by apply/ffunP=> x; rewrite !(perm_to_transfE, permE, ffunE).
- by apply/ffunP=> x; rewrite !(perm_to_transfE, permE, ffunE) /= !perm_to_transfE.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {perm T} {transf T}
    perm_to_transf perm_to_transf_is_monoid_morphism.
Lemma perm_to_transfK : cancel perm_to_transf perm_of_transf.
Proof.
case=> [/= f pff]; apply/permP=> x /=.
rewrite unlock /= pvalE /perm_of_transf /perm_to_transf /=.
move: pff; case (boolP (injectiveb f)) => // pff _.
by rewrite unlock /=.
Qed.

End PermToTransf.


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


(** The partial transformation monoid over T is a submonoid *)
(** of the relation monoid over T                           *)
Section PtransfToRelat.

Context {T : finType}.
Implicit Types (x y : T) (f g h : {ptransf T}) (r s : {relat T}).

Definition ptransf_to_relat f : {relat T} :=
  [set (x, odflt x (f x)) | x in T & isSome (f x)].
Definition ptransf_of_relat r : {ptransf T} :=
  [ffun x => unset1 [set y : T | (x, y) \in r]].

Lemma ptransf_to_relatE p x y :
  ((x, y) \in ptransf_to_relat p) = (p x == Some y).
Proof.
rewrite /ptransf_to_relat; apply/imsetP/eqP => [[x0 ] | eqpx].
  by rewrite inE /= /odflt /oapp; case Hx0 : (p x0) => [y0 |//] _ [{x}-> {y}->].
exists x; first by rewrite inE eqpx.
by rewrite /odflt /oapp eqpx.
Qed.

Lemma ptransf_to_relat_is_monoid_morphism : monoid_morphism ptransf_to_relat.
Proof.
split=> [| /= f g].
- by apply/setP => -[x y]; rewrite ptransf_to_relatE !inE /= ffunE.
- apply/setP => -[x y]; rewrite !(ptransf_to_relatE, inE) /=.
  rewrite ffunE /obind /= /oapp; case eqfx : (f x) => [z|]; first last.
    apply/eqP/existsP => // -[z].
    by rewrite !ptransf_to_relatE eqfx => /andP[/eqP].
  apply/eqP/existsP => [eqgz | [y0]].
    by exists z; rewrite !ptransf_to_relatE eqfx eqgz !eqxx.
  by rewrite !ptransf_to_relatE eqfx => /andP[/eqP[<-] /eqP].
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {ptransf T} {relat T}
    ptransf_to_relat ptransf_to_relat_is_monoid_morphism.
Lemma ptransf_to_relatK : cancel ptransf_to_relat ptransf_of_relat.
Proof.
rewrite /ptransf_of_relat=> f; apply/ffunP=> x.
rewrite ffunE; case eqfx: (f x) => [y|].
  rewrite [X in unset1 X](_ : _ = set1 y) ?set1K //.
  apply/setP=> z; rewrite !inE ptransf_to_relatE.
  by rewrite eqfx (inj_eq Some_inj) eq_sym.
rewrite [X in unset1 X](_ : _ = set0) ?unset10 //.
by apply/setP=> y; rewrite !inE  ptransf_to_relatE eqfx.
Qed.

End PtransfToRelat.


(* Converse monoid *)
Section ConverseMonoid.

HB.instance Definition _ (R : monoidType) :=
  let mul' (x y : R) := (y * x) in
  let mulgA' x y z := esym (mulgA z y x) in
  isMonoid.Build R^c (mulgA' : associative mul') mulg1 mul1g.

HB.instance Definition _ (R : comMonoidType) :=
  Magma_hasCommutativeMul.Build R^c (fun _ _ => mulgC _ _).

End ConverseMonoid.


(* A product of commutative monoid is a canonical instance of comoid *)
Section ComProduct.

Variable (U V : comMonoidType).
Fact pair_mulC : @commutative (U * V) (U * V) ( *%g ).
Proof. by move=> [x1 y1][x2 y2]; congr (_, _); rewrite mulgC. Qed.
HB.instance Definition _ :=
  Magma_hasCommutativeMul.Build (U * V)%type pair_mulC.

End ComProduct.
