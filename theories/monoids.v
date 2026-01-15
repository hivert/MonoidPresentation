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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
From mathcomp Require Import choice bigop fintype finfun finset ssralg monoid.
From mathcomp Require Import fingroup perm binomial.

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
Lemma mulptrP f g : f * g = finfun (obind g \o f).
Proof. by []. Qed.
Lemma mulptrE f g x : (f * g) x = obind g (f x).
Proof. exact: multrE. Qed.
Lemma oneptrE : (1 : type T) = finfun Some.
Proof. by []. Qed.
End Theory.
End Exports.
End PartialTransformation.
HB.export PartialTransformation.Exports.
Notation "{ 'ptransf' T }" := (PartialTransformation.type T).

Lemma ptrP T (s t : {ptransf T}) : s =1 t <-> s = t.
Proof. by split=> [| -> //] eq_st; apply/ffunP. Qed.


Section PartialFunctionTheory.

Variable (T : finType).
Implicit Type (s : T -> option T).

Definition pcodom s := pmap s (enum T).
Definition pdom s := enum (isSome \o s).

Lemma card_pcodom s : #|pcodom s| = #|image s (isSome \o s)|.
Proof.
rewrite -[LHS](card_image Some_inj).
apply: eq_card => /= -[x|]; first last.
  transitivity false.
    by apply/negP => /imageP[].
  by apply/esym/negP => /imageP[x] ; rewrite unfold_in; case: (s x).
apply/mapP/mapP=> -[y /[!mem_enum]].
  rewrite mem_pmap => /mapP[z _ {y}->] eqsz; exists z => //.
  by rewrite mem_enum unfold_in -eqsz.
move=> _ eqsy; exists x => //.
rewrite mem_enum mem_pmap; apply/mapP; exists y => //.
by rewrite mem_enum inE.
Qed.

Lemma card_pcomdom_le_dom s : #|pcodom s| <= #|pdom s|.
Proof.
rewrite card_pcodom (eq_card (mem_enum _)); apply: (leq_trans (card_size _)).
by rewrite size_map -cardE.
Qed.

Lemma isSome_pperm_enum_val s (i : 'I_#|pdom s|) : s (enum_val i).
Proof. by have:= enum_valP i; rewrite /pdom mem_enum unfold_in. Qed.

Definition psurj_fun s :=
  [fun i : 'I_#|pdom s| => index (s (enum_val i)) [seq Some x | x in pcodom s]].
Lemma psurj_subproof s i : psurj_fun s i < #|pcodom s|.
Proof.
rewrite /= cardE -(size_map Some) /= index_mem; apply/mapP.
case eqx : (s (enum_val i)) (isSome_pperm_enum_val i) => [x | //] _.
exists x => //; rewrite mem_enum mem_pmap -eqx; apply: map_f.
by rewrite mem_enum.
Qed.
Definition psurj s (i : 'I_#|pdom s|) := Ordinal (psurj_subproof (s := s) i).
Lemma enum_val_psurj s (i : 'I_#|pdom s|) :
  s (enum_val i) = Some (enum_val (psurj (s := s) i)).
Proof.
case eqr : (s (enum_val i)) (isSome_pperm_enum_val i) => [r |//] _; congr Some.
rewrite (enum_val_nth r) /= eqr (index_map Some_inj) nth_index //.
by rewrite mem_enum mem_pmap -eqr map_f // mem_enum.
Qed.

End PartialFunctionTheory.


Lemma pfun_dinjectiveP (T1 : finType) (T2 : eqType) (f : T1 -> option T2) :
  reflect {on isSome &, injective f} (dinjectiveb f (isSome \o f)).
Proof. by apply (iffP (dinjectiveP f _)) => inj /= x y; apply: inj. Qed.

(* Monoid structure on partial permutations               *)
(* i.e. injective partically defined finite endofunctions *)
Section PartialPermutationDef.

Variable (T : finType).

Record pperm_type : predArgType :=
  PPerm {ppval : {ptransf T}; _ : dinjectiveb ppval (isSome \o ppval)}.

HB.instance Definition _ := [isSub for ppval].
HB.instance Definition _ := [Finite of pperm_type by <:].

Lemma pinjective_closed :
  monoid_closed (fun p : {ptransf T} => dinjectiveb p (isSome \o p)).
Proof.
split => [|s t]; rewrite !unfold_in.
  (* exact/pfun_dinjectiveP/(on2W (inj_comp Some_inj (@inj_id T))). *)
  by apply/pfun_dinjectiveP=> x y _ _; rewrite !oneptrE !ffunE => /Some_inj.
move=> /pfun_dinjectiveP sinj /pfun_dinjectiveP tinj.
apply/pfun_dinjectiveP => x y; rewrite !mulptrE /=.
case eq_sx : (s x) => [sx |] //= {}/tinj tsx.
case eq_sy : (s y) => [sy |] //= /tsx/[apply] eqsxy.
by apply: sinj; rewrite ?{x}eq_sx ?{y}eq_sy ?eqsxy.
Qed.
HB.instance Definition _ :=
  SubChoice_isSubMonoid.Build {ptransf T}
    (fun p : {ptransf T} => dinjectiveb p (isSome \o p))
    pperm_type pinjective_closed.

Lemma pperm_proof (f : T -> option T) :
  {on isSome &, injective f} -> dinjectiveb (finfun f) (isSome \o (finfun f)).
Proof.
move=> /pfun_dinjectiveP inj.
suff /(eq_dinjectiveb (ffunE f)) -> : isSome \o (finfun f) =i isSome \o f by [].
by move=> x /=; rewrite !unfold_in ffunE.
Qed.

End PartialPermutationDef.
Arguments pperm_type T%_type.

Notation "{ 'pperm' T }" :=
  (pperm_type T) (format "{ 'pperm'  T }", at level 0) : type_scope.
Arguments ppval _ _%_g.

Bind Scope group_scope with pperm_type.


HB.lock Definition pperm T f injf := PPerm (@pperm_proof T f injf).
Canonical perm_unlock := Unlockable pperm.unlock.

HB.lock Definition fun_of_pperm T (u : {pperm T}) : T -> option T := val u.
Canonical fun_of_pperm_unlock := Unlockable fun_of_pperm.unlock.
Coercion fun_of_pperm : pperm_type >-> Funclass.

Section PPermTheory.

Variable T : finType.
Implicit Types (x y : T) (s t : {pperm T}).

Lemma ppermP s t : s =1 t <-> s = t.
Proof. by split=> [| -> //]; rewrite unlock => eq_sv; apply/val_inj/ffunP. Qed.

Lemma ppvalE s : ppval s = s :> (T -> option T).
Proof. by rewrite [@fun_of_pperm]unlock. Qed.

Lemma ppermE f f_inj : @pperm T f f_inj =1 f.
Proof. by move=> x; rewrite -ppvalE [@pperm]unlock ffunE. Qed.

Lemma pperm1E x : (1 : {pperm T}) x = Some x.
Proof. by rewrite -ppvalE /= ffunE. Qed.

Lemma ppermME s t x : (s * t) x = obind t (s x).
Proof. by rewrite -ppvalE /= ffunE /= !ppvalE. Qed.

Lemma pperm_inj {s} : {on isSome &, injective s}.
Proof. by rewrite -!ppvalE; apply/pfun_dinjectiveP/(valP s). Qed.
Hint Resolve pperm_inj : core.

Lemma card_pcomdomE s : #|pcodom s| = #|pdom s|.
Proof.
rewrite card_pcodom (eq_card (mem_enum _)).
suff /card_uniqP -> : uniq [seq s x | x in isSome \o s] by rewrite size_map cardE.
rewrite map_inj_in_uniq ?enum_uniq // => i j.
by rewrite !mem_enum; apply: pperm_inj.
Qed.

Lemma ppsurj_subproof s :
  injective [fun i => cast_ord (card_pcomdomE s) (psurj (s := s) i)].
Proof.
move=> i j /= /cast_ord_inj /(congr1 (Some \o enum_val)) /= H.
apply: enum_val_inj; move: H; rewrite /= -!enum_val_psurj.
by apply: pperm_inj; apply: isSome_pperm_enum_val.
Qed.
Definition perm_pdom s : 'S_#|pdom s| := perm (ppsurj_subproof (s := s)).

Lemma enum_val_perm_dom s (i : 'I_#|pdom s|) :
  s (enum_val i) =
    Some (enum_val (cast_ord (esym (card_pcomdomE s)) (perm_pdom s i))).
Proof.
rewrite enum_val_psurj; congr (Some (enum_val _)); apply val_inj => /=.
by rewrite permE.
Qed.

Section DomPermDef.

Lemma eq_enums (p : pred T) : enum [set x0 in p] = enum p.
Proof. by apply: eq_enum => y; rewrite inE. Qed.

Lemma obindnthP (s : seq T) n :
  obind (onth s) n -> exists2 i : nat, n = Some i & i < size s.
Proof. by case: n => [n|//] /= /[!onthTE] ltn; exists n. Qed.

Context (doms : {set T}) (p : 'S_#|doms|) (codoms : {set T}).
Lemma of_domperm_subproof :
  {on isSome &, injective
     [ffun x : T =>
        obind (onth (enum codoms) \o \val \o p) (insub (index x (enum doms)))]}.
Proof.
move=> x y; rewrite !ffunE /= -compA !obindEapp !oapp_comp /= -!obindEapp /=.
move=> /obindnthP[pi eqpi]; rewrite -cardE => ltpi.
move=> /obindnthP[pj eqpj]; rewrite -cardE => ltpj.
rewrite eqpi eqpj /= => eqpij.
have {}eqpij : pi = pj.
  move/onth_inj: eqpij; apply; first exact: enum_uniq.
  by rewrite -cardE gtn_min ltpj.
case: (boolP (index x (enum doms) < #|doms|)) => indx; first last.
  by move: eqpi; rewrite insubN.
have {eqpij} := congr1 Some eqpij; rewrite -{pi ltpi}eqpi -{pj ltpj}eqpj.
have /inj_omap/[apply] /= : injective (nat_of_ord (n := #|doms|) \o p).
  by move=> i j /= /val_inj/perm_inj.
rewrite insubT.
case: (boolP (index y (enum doms) < #|doms|)) => indy; last by rewrite insubN.
rewrite insubT => -[].
by apply: (index_inj x (s := (enum doms))); rewrite // -index_mem -cardE.
Qed.
Definition of_domperm : {pperm T} := pperm of_domperm_subproof.

Hypothesis eqdoms : #|doms| = #|codoms|.

Lemma pdoms_of_domperm : [set x in pdom of_domperm] = doms.
Proof.
apply/setP=> x; rewrite inE !mem_enum ![LHS]unfold_in /= ppermE ffunE.
case: (boolP (x \in doms)) => [xin | xnotin]; first last.
  by rewrite insubN // cardE index_mem mem_enum.
have ltind : index x (enum doms) < #|doms|.
  by rewrite cardE index_mem mem_enum.
by rewrite insubT /= onthTE -cardE -eqdoms ltn_ord.
Qed.

Lemma pcodoms_of_domperm : [set x in pcodom of_domperm] = codoms.
Proof.
apply/eqP; rewrite eqEcard -eqdoms cardsE card_pcomdomE.
rewrite -(cardsE (mem (pdom _))) /= pdoms_of_domperm leqnn andbT.
apply/subsetP=> x; rewrite inE mem_pmap => /mapP[y _].
rewrite ppermE => /esym/[dup]/(congr1 isSome)/=.
rewrite !ffunE /= -compA !obindEapp !oapp_comp /= -!obindEapp /=.
case/obindnthP => n -> ltn /=.
by rewrite onthE (nth_map x) // -mem_enum => -[<-]; apply: mem_nth.
Qed.

Lemma perm_of_domperm :
  cast_perm (esym (cardsE _)) (perm_pdom of_domperm) =
    cast_perm (esym (congr1 (fun s : {set T} => #|s|) pdoms_of_domperm)) p.
Proof.
apply: (@cast_perm_inj _ _ (cardsE (mem (pdom of_domperm)))) => /=.
rewrite cast_permKV; apply/permP => /= i; rewrite permE /=.
rewrite !cast_permE esymK; apply: val_inj; rewrite /= ppermE ffunE /=.
have -> /= : [seq Some x | x in pcodom of_domperm] = [seq Some x | x in codoms].
  by congr map; apply: eq_enum => x; rewrite -pcodoms_of_domperm inE.
rewrite /= -compA !obindEapp !oapp_comp /= -!obindEapp /=.
set x := (X in p X); set y := (X in omap _ X); suff -> : y = Some x.
  rewrite /= onthE index_uniq //; first last.
    by rewrite (map_inj_uniq Some_inj) enum_uniq.
  by rewrite size_map -cardE -eqdoms ltn_ord.
rewrite {}/x {}/y insubT.
  by rewrite cardE index_mem mem_enum -pdoms_of_domperm inE enum_valP.
move=> Hind; congr Some; apply: val_inj => /=.
rewrite (enum_val_nth (enum_val i)) -eq_enums pdoms_of_domperm.
apply: (index_uniq _ _ (enum_uniq _)).
by have := ltn_ord i; rewrite -{2}cardsE pdoms_of_domperm -cardE.
Qed.

End DomPermDef.

Lemma perm_pdomK s :
  s = @of_domperm [set x in pdom s]
        (cast_perm (esym (cardsE _)) (perm_pdom s)) [set x in pcodom s].
Proof.
apply/ppermP => x /=; rewrite ppermE ffunE /=.
rewrite !eq_enums; case eqsx : (s x) => [sx|]/=; first last.
  rewrite insubN //= cardsE.
  suff /memNindex -> : x \notin enum (pdom s) by rewrite -cardE ltnn.
  by rewrite !mem_enum unfold_in eqsx.
have /[dup] xin : x \in enum (pdom s) by rewrite !mem_enum unfold_in eqsx.
rewrite -index_mem -cardE -{1}cardsE => indx; rewrite insubT /=.
have /= := enum_val_perm_dom (cast_ord (cardsE (mem (pdom s))) (Ordinal indx)).
have -> : enum_val (cast_ord (cardsE (mem (pdom s))) (Ordinal indx)) = x.
  by rewrite (enum_val_nth x) /= nth_index.
rewrite -eqsx => ->; rewrite cast_permE /=.
rewrite (enum_val_nth x) onthE (nth_map x) /=; first last.
  by rewrite -cardE card_pcomdomE.
by congr (Some (nth _ _ (perm_pdom _ _))); apply: val_inj.
Qed.

Definition pptriple := ({x : {set T} & 'S_#|x|} * {set T})%type.
Definition to_pptriple s : pptriple :=
  (existT (fun x : {set T} => 'S_#|x|)
     [set x in pdom s] (cast_perm (esym (cardsE _)) (perm_pdom s)),
    [set x in pcodom s]).
Definition of_pptriple (tr : pptriple) :=
  let: (existT doms p, codoms) := tr in @of_domperm doms p codoms.

Lemma to_pptripleK : cancel to_pptriple of_pptriple.
Proof. by move=> s; rewrite -[LHS](perm_pdomK s). Qed.
Lemma of_pptripleK (tr : pptriple) :
  #|tag tr.1| = #|tr.2| -> to_pptriple (of_pptriple tr) = tr.
Proof.
case: tr => [[doms p] codoms] /= eqdoms.
congr (_, _); last by rewrite pcodoms_of_domperm.
rewrite perm_of_domperm.
move: [set x in pdom (of_domperm _ _)] (pdoms_of_domperm _ _) => d eqd.
by subst d.
Qed.

Lemma imset_to_pptriple :
  to_pptriple @: setT = [set tr : pptriple | #|tag tr.1| == #|tr.2|].
Proof.
apply/setP => /= tr; rewrite !inE.
apply/imsetP/eqP => [[/= pp _ ->] /= | /of_pptripleK <-].
  by rewrite !cardsE card_pcomdomE.
by exists (of_pptriple tr).
Qed.


Theorem card_pperm : #|{pperm T}| = \sum_(k < #|T|.+1) 'C(#|T|, k) ^ 2 * k`!.
Proof.
rewrite -[LHS]cardsT -(card_imset _ (can_inj to_pptripleK)) imset_to_pptriple.
rewrite -sum1dep_card.
have cdom_subproof (tr : pptriple) : #|tag tr.1| < #|T|.+1.
  by rewrite ltnS; apply: max_card.
pose cdom tr := Ordinal (cdom_subproof tr).
rewrite [LHS](partition_big_idem _ _ (p := cdom) (Q := xpredT)) //=.
apply: eq_bigr => k _; rewrite sum1dep_card.
transitivity
  #|setX [set pdoms : {x : {set T} & 'S_#|x|} | #|tag pdoms| == k]
    [set codoms : {set T} | #|codoms| == k]|.
  rewrite !cardsE /=; apply: eq_card => /= -[[doms p codoms]] /=.
  rewrite unfold_in [RHS]unfold_in !in_set /= -(inj_eq val_inj) /= andbC.
  by case: eqP => //= ->; rewrite eq_sym.
rewrite {cdom_subproof cdom} cardsX card_draws.
rewrite -mulnn -mulnA [RHS]mulnC; congr (_ * _)%N.
pose ofcard (pr : {x : {set T} & 'S_#|x|}) := let (doms, p) := pr in
  (doms, if altP (#|doms| =P k) is AltTrue pf then cast_perm pf p else 1).
rewrite -(card_in_imset (f := ofcard)); first last.
  move=> /= [d1 p1][d2 p2].
  rewrite !inE /= => /eqP cd1 /eqP cd2 [eqd]; subst d2.
  case (altP (#|d1| =P k)) => [{}cd1|]; last by rewrite cd1 eqxx.
  by move/cast_perm_inj ->.
transitivity #|setX [set pdoms : {set T} | #|pdoms| == k] [set: 'S_k]|; first last.
  by rewrite cardsX card_draws cardsE card_Sn.
congr #|pred_of_set _|; apply/setP => /= -[s p].
rewrite !inE /= andbT; apply/imsetP/eqP => /= [[[s1 p1]] | cs].
  by rewrite inE /= => /eqP cs1 [->].
exists (existT _ s (cast_perm (esym cs) p)); first by rewrite inE /= cs.
rewrite /ofcard; congr (_, _).
case (altP (#|s| =P k)) => [cds|]; last by rewrite cs eqxx.
by rewrite cast_perm_comp cast_perm_id.
Qed.

End PPermTheory.


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


(** The symmetric group is a submonoid of the transformation monoid *)
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

Lemma perm_of_transfE f : injective f -> perm_of_transf f =1 f.
Proof.
move=> /injectiveP f_inj x.
rewrite unlock /= pvalE /perm_of_transf /perm_to_transf /=.
move: f_inj; case (boolP (injectiveb f)) => // pff _.
by rewrite unlock /=.
Qed.
Lemma perm_to_transfK : cancel perm_to_transf perm_of_transf.
Proof.
case=> [/= f pff]; apply/permP=> x /=.
by rewrite perm_of_transfE ?perm_to_transfE; last exact/injectiveP.
Qed.

End PermToTransf.


(** The symmetric group is a submonoid of the partial permutation monoid *)
Section PermToPPerm.

Local Open Scope group_scope.

Context {T : finType}.
Implicit Types (f g h : {pperm T}) (p q : {perm T}).

Lemma perm_to_pperm_subproof p : {on isSome &, injective (olift p)}.
Proof. by rewrite /olift => x y _ _ [] /perm_inj. Qed.
Definition perm_to_pperm p : {pperm T} := pperm (@perm_to_pperm_subproof p).
Definition perm_of_pperm f : {perm T} := perm_of_transf (of_ptransf (ppval f)).
Lemma perm_to_ppermE p x : perm_to_pperm p x = Some (p x).
Proof. by rewrite ppermE. Qed.

Lemma perm_to_pperm_is_monoid_morphism : monoid_morphism perm_to_pperm.
Proof.
split=> [| /= f g].
- by apply/ppermP=> x; rewrite perm_to_ppermE permE pperm1E.
- apply/ppermP=> x; rewrite perm_to_ppermE.
  by rewrite permE /= ppermME /= !perm_to_ppermE /= perm_to_ppermE.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {perm T} {pperm T}
    perm_to_pperm perm_to_pperm_is_monoid_morphism.
Lemma perm_to_ppermK : cancel perm_to_pperm perm_of_pperm.
Proof.
move=> p; apply/permP => /= x.
rewrite /perm_of_pperm /perm_to_pperm.
rewrite -{3}(perm_to_transfK p); congr (perm_of_transf _ _).
apply/ffunP => {}x.
by rewrite !ffunE perm_to_transfE ppvalE /= ppermE.
Qed.

Definition pperm_is_perm f := [forall x : T, isSome (f x)].
Lemma pperm_is_permP f :
  reflect (forall x : T, isSome (f x)) (pperm_is_perm f).
Proof. exact: forallP. Qed.
Lemma perm_to_pperm_is_perm p : pperm_is_perm (perm_to_pperm p).
Proof. by apply/pperm_is_permP=> x; rewrite perm_to_ppermE. Qed.
Lemma perm_of_ppermK : {in pperm_is_perm, cancel perm_of_pperm perm_to_pperm}.
Proof.
move=> f /pperm_is_permP allSome; apply/ppermP => x.
rewrite perm_to_ppermE /perm_of_pperm perm_of_transfE; first last.
  rewrite /of_ptransf => {}x y /=; rewrite !ffunE ppvalE /= => Heq.
  apply: (pperm_inj (allSome x) (allSome y)).
  by case: (f x) (f y) (allSome x) (allSome y) Heq => [fx | //] [fy | //] _ _ ->.
rewrite /of_ptransf !ffunE ppvalE /=.
by case: (f x) (allSome x).
Qed.

End PermToPPerm.


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
