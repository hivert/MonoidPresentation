From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice bigop fintype finfun finset ssralg tuple.

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
         mgenP : forall m, exists2 w, w \in words_of P & univmor mgen w = m;
         mgen_eq : forall (u v : seq I),
           u \in words_of P -> v \in words_of P ->
           (u = v %[mod P] <-> univmor mgen u = univmor mgen v)
       }.
Notation "P \present M" := (presentation_of M P).


Section MorphFromPres.

Context {M : monoidType} {I : choiceType} (P : pres I) (presP : P \present M).
Variable (N : monoidType) (f : I -> N).
Hypothesis (fmor : satisfy P f).

Definition presmor (m : M) : N :=
  let: exist2 u _ _ := (sig2_eqW (mgenP presP m)) in univmor f u.

Lemma presmor_mgenE i : i \in pgen P -> presmor (mgen presP i) = f i.
Proof.
move=> iinP.
have i1inP : [:: i] \in words_of P by apply/allP => j /[!inE] /eqP->.
rewrite /presmor; case: sig2_eqW => u uinP.
rewrite -(univmor1 _ i) -mgen_eq // => /(satisfy_univmor fmor) ->.
by rewrite univmor1.
Qed.

Fact presmor_monmorphism : monmorphism presmor.
Proof.
rewrite /presmor; split.
  case: sig2_eqW => u uinP.
  rewrite -(univmor_nil (mgen presP)) -mgen_eq //.
  move=> /(satisfy_univmor fmor) ->.
  by rewrite univmor_nil.
move=> m1 m2.
case: sig2_eqW => /= u12 u12inP eq12.
case: sig2_eqW => /= u1 u1inP eq1.
case: sig2_eqW => /= u2 u2inP eq2.
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

Fact isomgenP m : exists2 w, w \in words_of P & univmor isomgen w = m.
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
  let: exist2 x _ _ := sig2_eqW (mgenP presQ (mgen presP i)) in x.
Definition isomon : {freemon I} -> {freemon J} := univmor isomon_gen.

Lemma isomon_gen_word i : isomon_gen i \in words_of Q.
Proof. by rewrite /isomon_gen; case: sig2_eqW => x. Qed.
Lemma isomon_genE i : univmor (mgen presQ) (isomon_gen i) = mgen presP i.
Proof. by rewrite /isomon_gen; case: sig2_eqW => x. Qed.

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

Fact converse_genP (m : M^c) : exists2 w, w \in words_of PC & univmor cgen w = m.
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


Section NatAdd.

Definition natadd := nat.

HB.instance Definition _ := Countable.on natadd.
HB.instance Definition _ := isComMonoid.Build natadd addnA addnC add0n.

Definition natadd_pres : pres nat := make_pres [:: 0] [::].

Let natadd_mgen := fun _ : nat => 1%N : natadd.

Lemma natadd_morE w : univmor natadd_mgen w = size w.
Proof.
elim: w => /= [| w0 w IHw]; first by rewrite univmor_nil.
by rewrite univmor_cons IHw.
Qed.
Lemma words_of_natadd_presP (u : seq nat) :
  reflect (u = nseq (size u) 0) (u \in words_of natadd_pres).
Proof.
apply (iffP allP) => /= [inu | ->].
  by apply/all_pred1P/allP => /= i {}/inu /[!inE].
move=> i /[!mem_nseq] /andP[_ /eqP->].
by rewrite inE.
Qed.
Fact natadd_mgenP (n : natadd) :
  exists2 w, w \in words_of natadd_pres & univmor natadd_mgen w = n.
Proof.
exists (nseq n 0); first by rewrite unfold_in /= all_nseq !inE eqxx orbT.
by rewrite natadd_morE size_nseq.
Qed.
Fact natadd_mgen_eq (u v : seq nat) :
  u \in words_of natadd_pres -> v \in words_of natadd_pres ->
  (u = v %[mod natadd_pres] <-> univmor natadd_mgen u = univmor natadd_mgen v).
Proof.
rewrite !natadd_morE => /words_of_natadd_presP -> /words_of_natadd_presP ->.
rewrite !size_nseq; split => [[[_| p0 p]] /= |->].
- by move/(congr1 size); rewrite !size_nseq => ->.
- rewrite /undirected /= => /andP[/rewritesP[/= pre suf rule _ _]].
  by rewrite in_nil.
- exact: equiv_refl.
Qed.
Definition natadd_presP : natadd_pres \present natadd :=
  Presentation natadd_mgenP natadd_mgen_eq.

End NatAdd.


Section TNthZipTuple.

Variables (n : nat) (T : Type).
Implicit Type t : n.-tuple T.

Lemma tnth_zip t1 t2 i :
  tnth [tuple of zip t1 t2] i = (tnth t1 i, tnth t2 i).
Proof.
case: n t1 t2 i => [|m] t1 t2 i; first by case: i.
case: t1 t2 => [[|h1 v1] sv1]// [[|h2 v2] sv2] //.
by rewrite (tnth_nth (h1, h2)) nth_zip ?size_tuple // (tnth_nth h1) (tnth_nth h2).
Qed.

End TNthZipTuple.


Section FreeCommutativeMonoid.

Variable n : nat.

Definition FCM := n.-tuple nat.

Implicit Types (x y z : FCM).

Let FCM1 : FCM := [tuple 0%N  | _ < n].
Let FCMmul x y : FCM := [tuple of map (fun p => p.1 + p.2)%N (zip x y)].

Fact FCMmulA : associative FCMmul.
Proof.
move => x y z; apply: eq_from_tnth => i /=.
by rewrite !(tnth_map, tnth_zip) /= addnA.
Qed.
Fact FCMmulC : commutative FCMmul.
Proof.
move => x y; apply: eq_from_tnth => i /=.
by rewrite !(tnth_map, tnth_zip) /= addnC.
Qed.
Fact FCMmul1m : left_id FCM1 FCMmul.
Proof.
move => x; apply: eq_from_tnth => i /=.
by rewrite !(tnth_map, tnth_zip).
Qed.

HB.instance Definition _ := Countable.on FCM.
HB.instance Definition _ := isComMonoid.Build FCM FCMmulA FCMmulC FCMmul1m.

Lemma tnth1 i : tnth (1%M%M : FCM) i = 0%N.
Proof. by rewrite tnth_mktuple. Qed.
Lemma tnthM x y i : tnth (x * y)%M i = tnth x i + tnth y i.
Proof. by rewrite tnth_map tnth_zip. Qed.
Lemma tnth_morph i :
  {morph (fun m : FCM => tnth m i) : x y / (x * y)%M >-> x + y}.
Proof. by move=> x y; rewrite tnthM. Qed.
Lemma tnth_prod [I : Type] (s : seq I) [P : pred I] [F : I -> FCM] i :
  tnth (\prod_(x <- s | P x) F x)%M i = (\sum_(x <- s | P x) tnth (F x) i)%N.
Proof. by apply: (big_morph _ (tnth_morph i)); rewrite tnth1. Qed.
Lemma tnthX x k i : tnth (x ^+ k)%M i = (tnth x i * k)%N.
Proof.
elim: k => [|k IHk]; first by rewrite expm0 tnth1 muln0.
by rewrite expmS tnthM mulnS IHk.
Qed.


Let comrel m := [seq ([:: i; j], [:: j; i]) | i <- iota 0 m, j <- iota 0 i].

Lemma subset_comrel m : {subset comrel m <= comrel m.+1}.
Proof.
move=> /= [a b] /allpairsPdep[i [j]][].
rewrite !mem_iota !add0n /= => /ltnW eim ltjm [{a}-> {b}->].
apply/allpairsPdep; exists i; exists j.
by rewrite !mem_iota /= !add0n !ltnS.
Qed.

Lemma all_relwords_comrel : all_relwords (comrel n) (mem (iota 0 n)).
Proof.
apply/all_allpairsP => [/= i j /=].
rewrite !mem_iota !add0n /= => /[dup] + ->.
by move=> /(ltn_trans _)/[apply] ->.
Qed.
Definition FCM_pres : pres nat :=
  Pres (iota 0 n) (comrel n) (iota_uniq 0 n) all_relwords_comrel.

Lemma mem_words_FCM_presP u :
  reflect  {in u, forall i, i < n} (u \in words_of FCM_pres).
Proof. by apply (iffP allP) => /= /[swap] i /[apply]; rewrite mem_iota. Qed.


Let FCM_mgen (i : nat) : FCM := [tuple j == i :> nat : nat  | j < n].

Lemma FCM_morE w :
  univmor FCM_mgen w = [tuple count_mem (\val i) (w : seq nat)  | i < n].
Proof.
elim: w => /= [| w0 w IHw]; first by rewrite univmor_nil.
apply eq_from_tnth => i.
rewrite univmor_cons !(tnth_map, tnth_zip) /= IHw.
by rewrite !tnth_mktuple tnth_ord_tuple eq_sym.
Qed.

Lemma equiv_comrel_rem m (w : word nat) :
  m \in w -> {in w, forall i : nat, i < m.+1} ->
      w = m :: (rem m w) %[mod comrel m.+1].
Proof.
rewrite remE -index_mem.
move: {2 3 4 5}(index m w) (erefl (index m w)) => i Hind Hsz.
elim: i w Hsz Hind => [| i IHi] w.
  rewrite take0 cat0s => + /eqP + _.
  rewrite -leqn0 -[_ <= 0]ltnS => /in_take_leq <-.
  rewrite -{2}(cat_take_drop 1 w).
  case: w => [| w0 w] //=; rewrite take0 drop0 cat0s inE => /eqP->.
  exact: equiv_refl.
case: w => [// | w0 w] /= {}/IHi Hrec.
case: eqP => // /eqP neqw0m []{}/Hrec Hrec Hin.
have ltw0m : w0 < m.+1.
  have /Hin : w0 \in w0 :: w by rewrite inE eqxx.
  by rewrite ltnS leq_eqVlt (negbTE neqw0m).
have {}/Hrec eqw : {in w, forall i : nat, i < m.+1}.
  by move=> j jinw; apply: Hin; rewrite inE jinw orbT.
move/(equiv_stable (R := comrel m.+1) [:: w0] [::]): eqw.
rewrite !cat1s !cats0 => /equiv_trans; apply.
move: (_ ++ _) => suf {i}; apply: rewrites_to1; apply/rewritesP;
exists [::] suf ([:: w0; m], [:: m; w0]); try by rewrite cat0s.
rewrite mem_undirected; apply/orP.
move: neqw0m; rewrite neq_ltn => /orP[] lt; [right|left].
- apply/allpairsPdep; exists m; exists w0.
  by split => //; rewrite !mem_iota /= add0n.
- apply/allpairsPdep; exists w0; exists m.
  by split => //; rewrite !mem_iota /= add0n.
Qed.

Fact FCM_mgenP (m : FCM) :
  exists2 w, w \in words_of FCM_pres & univmor FCM_mgen w = m.
Proof.
have tnth_nseq k (i : 'I_n) (j : nat) :
    tnth (univmor FCM_mgen (nseq k j)) i = ((i == j :> nat) * k)%N.
  by rewrite univmor_nseq tnthX tnth_mktuple.
exists (flatten [seq nseq (nth 0 m i) i | i <- iota 0 n]).
  by apply/allP=> i /flatten_mapP[/= j] iin /nseqP[-> _].
rewrite flatten_prodE big_map mmorph_prod /=.
apply: eq_from_tnth => i; rewrite tnth_prod.
have iin : \val i \in iota 0 n by rewrite mem_iota /= add0n ltn_ord.
rewrite (bigD1_seq (\val i) iin) /= ?iota_uniq //.
rewrite big1 ?addn0 => [|j /negbTE neqij]; first last.
  by rewrite tnth_nseq eq_sym neqij mul0n.
by rewrite tnth_nseq eqxx mul1n -tnth_nth.
Qed.
Fact FCM_mgen_eq (u v : seq nat) :
  u \in words_of FCM_pres -> v \in words_of FCM_pres ->
  (u = v %[mod FCM_pres] <-> univmor FCM_mgen u = univmor FCM_mgen v).
Proof.
rewrite !FCM_morE => uin vin; split=> [equv|].
  move: u v equv {uin vin}; apply: equiv_min => /= [[]|].
    rewrite /comrel => /= u v /allpairsPdep[i][j].
    rewrite !mem_iota /= add0n => -[_ _][{u}-> {v}->] /=.
    by apply eq_from_tnth => k; rewrite !tnth_mktuple !addn0 addnC.
  split=> [// | u v w -> -> //| pre u v suf Heq | u v -> //].
  apply eq_from_tnth => k; move/(congr1 (fun t => tnth t k)): Heq.
  by rewrite !tnth_mktuple !count_cat => ->.
move: uin vin => /mem_words_FCM_presP uin /mem_words_FCM_presP vin.
move=> Heq; have {}Heq (i : nat) : count_mem i u = count_mem i v.
case: (ltnP i n) => [ltin | leni] /=.
- move/(congr1 (fun t => tnth t (Ordinal ltin))): Heq.
  by rewrite !tnth_mktuple.
- suff wcnt w : {in w, forall i : nat, i < n} -> count_mem i w = 0.
    by rewrite !wcnt.
  by move=> Hin; apply/count_memPn/negP => /Hin; rewrite ltnNge leni.
rewrite /FCM_pres /=.
elim : n u v uin vin Heq => [|m IHm] u v.
  case: u v => [|u0 u] v; first last.
    by move=> H; have /H : u0 \in u0 :: u by rewrite inE eqxx.
  case: v => [|v0 v _]; first last.
    by move=> H; have /H : v0 \in v0 :: v by rewrite inE eqxx.
  by move=> _ _ _; apply: equiv_refl.
move Hc : (count_mem m u) => c.
elim: c u v Hc => [| c IHc {IHm}] u v Hc uin vin eqcount.
  have {}/IHm Hrec : {in u, forall i : nat, i < m}.
    move=> i /[dup] iin /uin; rewrite ltnS leq_eqVlt => /orP[/eqP eqi |//].
    by subst i; move/count_memPn: Hc; rewrite iin.
  have {}/Hrec : {in v, forall i : nat, i < m}.
    move=> i /[dup] iin /vin; rewrite ltnS leq_eqVlt => /orP[/eqP eqi |//].
    by subst i; move: Hc; rewrite eqcount => /count_memPn; rewrite iin.
  move/(_ eqcount); move: u v {uin vin eqcount Hc}.
  exact/sub_equiv/subset_comrel.
have minu : m \in u by apply/count_memPn; rewrite Hc.
have minv : m \in v by apply/count_memPn; rewrite -eqcount Hc.
have {c Hc}/IHc Hrec : count_mem m (rem m u) = c.
  by rewrite count_mem_rem Hc eqxx subSS subn0.
have {}/Hrec Hrec: {in rem m u, forall i : nat, i < m.+1}.
  by move=> i /mem_rem/uin.
have {}/Hrec Hrec : {in rem m v, forall i : nat, i < m.+1}.
  by move=> i /mem_rem/vin.
have {eqcount}/Hrec Hrec : forall i, count_mem i (rem m u) = count_mem i (rem m v).
  by move=> i; rewrite !count_mem_rem eqcount.
apply: (equiv_trans (equiv_comrel_rem minu uin) (equiv_sym _)).
apply: (equiv_trans (equiv_comrel_rem minv vin) (equiv_sym _)).
move/(equiv_stable (R := comrel m.+1) [:: m] [::]): Hrec.
by rewrite !cat1s !cats0.
Qed.
Definition FCM_presP : FCM_pres \present FCM :=
  Presentation FCM_mgenP FCM_mgen_eq.

End FreeCommutativeMonoid.

