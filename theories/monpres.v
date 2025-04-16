From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice bigop fintype finfun finset ssralg.
(*From mathcomp Require Import order.
From mathcomp Require Import all_ssreflect. *)

Require Import monoids present enumnf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation "gr \present G" (at level 10).

Section Satisfy.

Variable (gT : monoidType) (I : choiceType).
Implicit Type (gens : I -> gT) (rels : relat I).

Definition satisfy rels gens :=
  all (fun r => \prod_(i <- r.1) gens i == \prod_(i <- r.2) gens i)%M rels.

Lemma satisfyP rels gens :
  reflect (forall r, r \in rels ->
                           \prod_(i <- r.1) gens i = \prod_(i <- r.2) gens i)%M
          (satisfy rels gens).
Proof. by apply: (iffP allP) => /= [H r /H /eqP| H r /H ->]. Qed.

Lemma satisfy_eq_impl gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 -> satisfy rels gens2.
Proof.
move=> Heq /satisfyP Hsat; apply/satisfyP => /= r rin.
transitivity (\prod_(i <- r.1) gens1 i)%M.
  by apply eq_bigr => i _; rewrite Heq.
by rewrite Hsat //; apply eq_bigr => i.
Qed.
Lemma satisfy_eq gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 = satisfy rels gens2.
Proof. by move=> Hgen; apply/idP/idP; apply: satisfy_eq_impl. Qed.

Lemma perm_satisfy rels1 rels2 gens :
  perm_eq rels1 rels2 -> satisfy rels1 gens = satisfy rels2 gens.
Proof. by rewrite/satisfy => /perm_all ->. Qed.

Lemma satisfy_cat rels1 rels2 gens :
  satisfy (rels1 ++ rels2) gens = satisfy rels1 gens && satisfy rels2 gens.
Proof. exact: all_cat. Qed.

End Satisfy.

Lemma morph_satisfy (I : choiceType)
      (gT : monoidType)
      (hT : monoidType)
      (f : {mmorphism gT -> hT}) (gens : I -> gT) rels :
  satisfy rels gens -> satisfy rels (f \o gens).
Proof.
move=> /satisfyP /= sat; apply/satisfyP => s {}/sat /(congr1 f).
by rewrite !mmorph_prod.
Qed.


Import GRing.Theory.

Local Open Scope ring_scope.

Record presentation_of (M : monoidType) (I : choiceType) (P : pres I) : Type
  := Presentation {
         prgen : I -> M;
         prgenP : forall (g : M), exists2 w,
             w \in words_of P & (\prod_(i <- w) prgen i = g)%M;
         prgen_eq : forall (u v : seq I),
           u \in words_of P -> v \in words_of P ->
           (u = v %[mod prelat P] <->
              \prod_(i <- u) prgen i = \prod_(i <- v) prgen i)%M
       }.

Notation "P \present M" := (presentation_of M P).

Section ConverseMonoid.

Context (M : monoidType) {I : choiceType} (P : pres I) (presP : P \present M).

Definition cgen : I -> (M^c)%M := prgen presP.
Let PC := dual_pres P.

Lemma words_of_dual_presE u : (rev u \in words_of PC) = (u \in words_of P).
Proof. by rewrite !unfold_in /= all_rev. Qed.

Lemma prod_dual_presE s :
  (\prod_(i <- rev s) cgen i)%M = (\prod_(i <- s) prgen presP i)%M.
Proof.
elim: s => [| s0 s IHs] /=; first by rewrite /rev /= !big_nil.
by rewrite rev_cons big_cons big_rcons /= IHs.
Qed.

Fact cgenP (g : M^c) :
  exists2 w, w \in words_of PC & (\prod_(i <- w) cgen i = g)%M.
Proof.
have [s sin eqs]:= prgenP presP (g : M).
exists (rev s); first by have := sin; rewrite words_of_dual_presE.
by rewrite -{}eqs prod_dual_presE.
Qed.
Fact cgen_eq (u v : seq I) :
  u \in words_of PC -> v \in words_of PC ->
  (u = v %[mod prelat PC] <-> \prod_(i <- u) cgen i = \prod_(i <- v) cgen i)%M.
Proof.
rewrite -(words_of_dual_presE u) -(words_of_dual_presE v) => uP vP.
rewrite -dual_pres_equivE /PC dual_presK (prgen_eq presP) //.
by rewrite -!prod_dual_presE !revK.
Qed.
Definition converse_presentation : PC \present M^c :=
  Presentation cgenP cgen_eq.

End ConverseMonoid.


Section MorphPresentation.

Context (M N : monoidType) {I J : choiceType}
  (P : pres I) (presP : P \present M)
  (Q : pres J) (presQ : Q \present N) (phi : {mmorphism M -> N}).

End MorphPresentation.
