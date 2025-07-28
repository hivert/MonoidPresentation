From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
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
Implicit Type (gens : I -> gT) (rels : relat I) (u v w : word I).

Definition satisfy rels gens :=
  all (fun r => univmor gens r.1 == univmor gens r.2) rels.

Lemma satisfyP rels gens :
  reflect (forall r, r \in rels -> univmor gens r.1 = univmor gens r.2)
          (satisfy rels gens).
Proof. by apply: (iffP allP) => /= [H r /H /eqP| H r /H ->]. Qed.

Lemma satisfy_eq_impl gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 -> satisfy rels gens2.
Proof.
move=> Heq /satisfyP /= Hsat; apply/satisfyP => /= r rin.
transitivity (univmor gens1 r.1).
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


Section SatisfyUnivMor.

Variable (gT : monoidType) (I : choiceType) (P : pres I) (gens : I -> gT).
Hypothesis gens_sat : satisfy P gens.

Lemma satisfy_univmor u v : u = v %[mod P] -> univmor gens u = univmor gens v.
Proof.
move: u v; apply: equiv_min; first exact/satisfyP.
split=> [| u v w -> ->| u v1 v2 w|]//.
by rewrite !univmor_cat => ->.
Qed.

End SatisfyUnivMor.

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
         mgen : I -> M;
         mgenP : forall (m : M), { w | w \in words_of P & univmor mgen w = m};
         mgen_eq : forall (u v : seq I),
           u \in words_of P -> v \in words_of P ->
           (u = v %[mod P] <-> univmor mgen u = univmor mgen v)
       }.

Notation "P \present M" := (presentation_of M P).


Section MorphFromPres.

Context (M : monoidType) {I : choiceType} (P : pres I) (presP : P \present M).
Variable (N : monoidType) (f : I -> N).
Hypothesis (fmor : satisfy P f).

Definition presmor (m : M) : N :=
  let: exist2 u _ _ := (mgenP presP m) in univmor f u.

Lemma presmor_mgenE i : i \in pgen P -> presmor (mgen presP i) = f i.
Proof.
move=> iinP.
have i1inP : [:: i] \in words_of P by apply/allP => j /[!inE] /eqP->.
rewrite /presmor; case: mgenP => u uinP.
rewrite -(univmor1 _ i) -mgen_eq // => /(satisfy_univmor fmor) ->.
by rewrite univmor1.
Qed.

Fact presmor_monmorphism : monmorphism presmor.
Proof.
rewrite /presmor; split.
  case: mgenP => u uinP.
  rewrite -(univmor_nil (mgen presP)) -mgen_eq //.
  move=> /(satisfy_univmor fmor) ->.
  by rewrite univmor_nil.
move=> m1 m2.
case: mgenP => u12 u12inP eq12.
case: mgenP => u1 u1inP eq1.
case: mgenP => u2 u2inP eq2.
rewrite -mmorphM /=; apply: (satisfy_univmor fmor).
move: eq12; rewrite -eq1 -eq2 -mmorphM /= -mgen_eq //.
by rewrite words_of_cat u1inP u2inP.
Qed.
HB.instance Definition _ := isMonMorphism.Build M N presmor presmor_monmorphism.

End MorphFromPres.


Section IsoPresMorph.

Context (M : monoidType) {I J : choiceType}
  (P : pres I) (Q : pres J) (presQ : Q \present M).
Hypothesis isoPQ : isopres P Q.

Definition isomgen (i : I) := univmor (mgen presQ) (isoPQ [:: i]).

Lemma isomgenE u : univmor isomgen u = univmor (mgen presQ) (isoPQ u).
Proof.
rewrite (FreeMonoidE u) !mmorph_prod /=; apply: eq_bigr => i _ /=.
by rewrite univmor1.
Qed.

Fact isomgenP (m : M) : { w | w \in words_of P & univmor isomgen w = m}.
Proof.
have [s sinQ eqs]:= mgenP presQ m.
have inv_inP := isopres_words_of (isopres_sym isoPQ) sinQ.
exists (inv isoPQ s); first exact: inv_inP.
have iso_inQ : isoPQ (inv isoPQ s) \in words_of Q by apply: isopres_words_of.
rewrite isomgenE -{}eqs -(mgen_eq presQ iso_inQ sinQ).
exact: caninv.
Qed.
Fact isomgen_eq (u v : seq I) :
  u \in words_of P -> v \in words_of P ->
  (u = v %[mod P] <-> univmor isomgen u = univmor isomgen v).
Proof.
rewrite !isomgenE => uinP vinP.
rewrite -(mgen_eq presQ) ?isopres_words_of //.
by symmetry; apply: isopresP.
Qed.
Definition isopresent : P \present M := Presentation isomgenP isomgen_eq.

End IsoPresMorph.


Section MorphPresentation.

Context (M : monoidType) {I J : choiceType}
  (P : pres I) (presP : P \present M)
  (Q : pres J) (presQ : Q \present M).

Definition isomon_gen (i : I) : {freemon J} :=
  let: exist2 x _ _ := (mgenP presQ (mgen presP i)) in x.
Definition isomon : {freemon I} -> {freemon J} := univmor isomon_gen.

Lemma isomon_gen_word i : isomon_gen i \in words_of Q.
Proof. by rewrite /isomon_gen; case: mgenP => x. Qed.
Lemma isomon_genE i : univmor (mgen presQ) (isomon_gen i) = mgen presP i.
Proof. by rewrite /isomon_gen; case: mgenP => x. Qed.

Lemma isomonE : univmor (mgen presQ) \o isomon =1 univmor (mgen presP).
Proof. by apply: univmor_uniq => i /=; rewrite univmor1 isomon_genE. Qed.

Fact isomon_word_of u : u \in words_of P -> isomon u \in words_of Q.
Proof.
rewrite /isomon /= /univmor /= => uinP.
rewrite -(big_map_id _ _ isomon_gen u xpredT) -flatten_prodE.
apply/allP => j /flatten_mapP[i inu].
by have/allP/[apply] := isomon_gen_word i.
Qed.
Fact isomon_eq u v : u \in words_of P -> v \in words_of P ->
  u = v %[mod P] -> isomon u = isomon v %[mod Q].
Proof.
rewrite /isomon => uinP vinP.
rewrite (mgen_eq presP uinP vinP) -!isomonE /=.
by rewrite (mgen_eq presQ) // isomon_word_of.
Qed.

HB.instance Definition _ := MonMorphism.on isomon.
HB.instance Definition _ := isRewMorphismTo.Build I J
    (undirected_pres P) (undirected_pres Q) isomon isomon_eq isomon_word_of.

End MorphPresentation.


Section IsoMorphCancel.

Context (M : monoidType) {I J : choiceType}
  (P : pres I) (presP : P \present M)
  (Q : pres J) (presQ : Q \present M).

Let mormorph : {presmorph _ -> _} := isomon presP presQ.
Let invmorph : {presmorph _ -> _} := isomon presQ presP.

Lemma isomonK (u : word I) :
  u \in words_of P -> invmorph (mormorph u) = u %[mod P].
Proof.
by move=> uinP; rewrite (mgen_eq presP) // ?isomon_word_of // ![LHS]isomonE.
Qed.

End IsoMorphCancel.

Definition present_mon_isopres (M : monoidType) {I J : choiceType}
  (P : pres I) (presP : P \present M) (Q : pres J) (presQ : Q \present M)
  : isopres P Q := IsoPres (isomonK presP presQ) (isomonK presQ presP).


Section ConverseMonoid.

Context (M : monoidType) {I : choiceType} (P : pres I) (presP : P \present M).

Let cgen : I -> (M^c)%M := mgen presP.
Let PC := dual_pres P.

Lemma words_of_dual_presE u : (rev u \in words_of PC) = (u \in words_of P).
Proof. by rewrite !unfold_in /= all_rev. Qed.

Lemma prod_dual_presE s : univmor cgen (rev s) = univmor (mgen presP) s.
Proof.
elim: s => [| s0 s IHs] /=.
  by rewrite /rev /= !univmor_nil.
by rewrite rev_cons univmor_rcons univmor_cons -!IHs.
Qed.

Fact converse_genP (m : M^c) : {w | w \in words_of PC & univmor cgen w = m}.
Proof.
have [s sin eqs]:= mgenP presP (m : M).
exists (rev s); first by have := sin; rewrite words_of_dual_presE.
by rewrite -{}eqs prod_dual_presE.
Qed.
Fact converse_gen_eq (u v : seq I) :
  u \in words_of PC -> v \in words_of PC ->
  (u = v %[mod PC] <-> univmor cgen u = univmor cgen v).
Proof.
rewrite -(words_of_dual_presE u) -(words_of_dual_presE v) => uP vP.
rewrite -dual_pres_equivE /PC dual_presK (mgen_eq presP) //.
by rewrite -!prod_dual_presE !revK.
Qed.
Definition converse_presentation : PC \present M^c :=
  Presentation converse_genP converse_gen_eq.

End ConverseMonoid.
