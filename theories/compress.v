From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.

Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import int_seq present rewcert fastcert homogeneous factor.


Section AllWords.

Context {Alph : choiceType}.

Fixpoint allwords (letters : seq Alph) (k : nat) :=
  if k is k'.+1 then [seq l :: w | l <- letters, w <- allwords letters k']
  else [:: [::]].
Lemma size_allwords l k : seq.size (allwords l k) = (seq.size l) ^ k.
Proof. by elim: k => [// | n IHn] /=; rewrite size_allpairs {}IHn. Qed.
Lemma allwordsP l k w :
  (w \in allwords l k) = (seq.size w == k) && all (mem l) w.
Proof.
elim: k w => [|k IHk] /=; first by case.
case=> [| w0 w]/=; first by apply/negP => /allpairsP[[/= w0 w] []].
apply/allpairsP/idP => [/= [[u0 u]]/= [u0inl] | /and3P[/eqP[eqsz w0in allmemw]]].
  rewrite {}IHk => /[swap] -[{w0}-> {w}->] /andP[/eqP-> ->].
  by rewrite eqxx u0inl.
by exists (w0, w); split => //=; rewrite {}IHk eqsz eqxx allmemw.
Qed.
Lemma allwords_uniq l k : uniq l -> uniq (allwords l k).
Proof.
move=> uniql; elim: k => [| k IHk] //=.
by apply: allpairs_uniq => // -/= [u0 u][v0 v] /= _ _ [-> ->].
Qed.

End AllWords.


Section Special.

Context {Alph : choiceType}.

Definition is_special (R : relat Alph) :=
  match R with
  | [:: (r1, r2)] => (r1 == [::]) || (r2 == [::])
  | _ => false
  end.
Lemma is_specialP R :
  reflect (exists u, R = [:: (u, [::])] \/ R = [:: ([::], u)])
          (is_special R).
Proof.
rewrite /is_special; apply (iffP idP).
- case: R => //= [[r1 r2] [|tl]] //.
  by case/orP=> /eqP ->; [exists r2; right| exists r1; left].
- by move=> [u] []->; rewrite eqxx // orbC.
Qed.

(* The word problem in special monoids reduces to the corresponding problem in
  groups. This is Corollary 2.8 in "The word problem for one-relation monoids: a
  survey" by Carl-Fredrik Nyberg-Brodda.

   https://arxiv.org/abs/2102.00745 Makanin, G.S.: On the identity problem for
   finitely presented groups and semigroups. PhD thesis, Steklov Mathematical
   Institute, Moscow (1966) *)
Theorem special_dec P : is_special (prelat P) -> WPdecidable P.
Admitted.

End Special.


Section StrongCompress.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Fixpoint strong_compress k u :=
  if u is u0 :: u' then
    if seq.size u < k then [::]
    else take k u :: strong_compress k u'
  else [::].

Lemma strong_compress_in gen k u :
  all (mem gen) u -> all (mem (allwords gen k)) (strong_compress k u).
Proof.
elim: u => [| u0 u IHu] //= /andP[u0gen /[dup] allu {}/IHu Hrec].
case: ltnP => //= /minn_idPl eqk; rewrite {}Hrec andbT.
rewrite allwordsP /= size_take_min eqk eqxx /=.
apply/allP => x /mem_take; rewrite inE => /orP[/eqP -> //|].
by move/(allP allu).
Qed.
Lemma correctrelat_strong_compress P k :
  correctrelat
    [seq (strong_compress k r.1, strong_compress k r.2) | r <- prelat P]
    (mem (allwords (pgen P) k)).
Proof.
have /allP/= Hall := wf_relat P.
apply/allP => /= -[s1 s2] /mapP[/=[r1 r2] /[swap]] /= -[{s1}-> {s2}->].
move/Hall => /= /andP[allr1 allr2].
by rewrite !strong_compress_in.
Qed.
Definition strong_compress_pres P k : pres (word Alph) :=
  Pres
    (allwords (pgen P) k)
    [seq (strong_compress k r.1, strong_compress k r.2) | r <- prelat P]
    (allwords_uniq k (uniq_pgen P))
    (correctrelat_strong_compress P k).

(* The assumption that both side of the relation starts with a implies
   that k >= 1, which in turn implies that there is a non trivial common suffix *)
Theorem strong_compress_dec (P : pres Alph) :
  forall a b u v,
    pgen P = [:: a; b] -> prelat P = [:: (a :: u, a :: v)] -> u != v ->
    let k := seq.size (long_cprefix (a :: u) (a :: v)) in
    k <= seq.size (long_csuffix (a :: u) (a :: v)) ->
    WPdecidable (strong_compress_pres P k.+1) -> WPdecidable P.
Admitted.

End StrongCompress.


Section ReduceTo2letters.

Context {Alph Beta : choiceType}.

Implicit Type (u v w : word Alph).

(* map A to a and all other to b *)
Variables (P : pres Alph) (A : Alph) (a b : Beta).
Hypothesis neqab : a != b.

Definition word_to2letters U :=
  [seq if l == A then a else b | l <- U].
Definition rel2letters :=
  [seq (word_to2letters r.1, word_to2letters r.2) | r <- prelat P].

Fact uniq_ab : uniq [:: a; b].
Proof. by rewrite /= inE neqab. Qed.
Fact correct_rel2letters : correctrelat rel2letters (mem [:: a; b]).
Proof.
apply/allP => /= -[s1 s2] /= /mapP[/= [r1 r2] _ [{s1}-> {s2}->]].
by apply/andP; split; apply/allP => y /mapP[x _] /=; case: eqP => _ ->;
  rewrite !inE eqxx //= orbT.
Qed.
Definition reduce2letters :=
  Pres [:: a; b] rel2letters uniq_ab correct_rel2letters.

Theorem reduce2letters_dec :
  forall B U V,
    A != B -> prelat P = [:: (A :: U, B :: V)] ->
    WPdecidable reduce2letters -> WPdecidable P.
Admitted.

End ReduceTo2letters.


Section FastCompressReduce.

Context {Alph Beta : choiceType} (w : word Alph) (x y : Beta).
Implicit Types (a b : Alph) (u v : word Alph).

Fixpoint compressreduce k u :=
  if u is u0 :: u' then
    if seq.size u < k then [::]
    else (if take k u == w then x else y) :: compressreduce k u'
  else [::].
Lemma compressreduceE k u :
  compressreduce k u = word_to2letters w x y (strong_compress k u).
Proof. by rewrite /word_to2letters; elim: u => //= u0 u ->; case: ltnP. Qed.

End FastCompressReduce.


Section StrongCompressAndReduce.

Context {Alph : choiceType}.
Variable (P : pres Alph).
Variable (a b : Alph) (u v : word Alph).
Hypotheses
  (Hgen : pgen P = [:: a; b])
  (Hrel : prelat P = [:: (a :: u, a :: v)])
  (NonSpecial : ~~ prefix (a :: u) (a :: v) && ~~ prefix (a :: v) (a :: u))
  (Hleft : seq.size (long_cprefix (a :: u) (a :: v)) <=
             seq.size (long_csuffix (a :: u) (a :: v))).

Lemma nequv : u != v.
Proof.
by apply/negP => /eqP equv; move: NonSpecial; rewrite equv !prefix_refl.
Qed.

Let k := seq.size (long_cprefix (a :: u) (a :: v)).
Let strcA := take k.+1 (a :: u).
Let strcB := take k.+1 (a :: v).

Lemma kneq0 : k > 0.
Proof. by rewrite /k /= eqxx. Qed.
Lemma strcAneqB : strcA != strcB.
Proof.
rewrite /strcA /strcB /k /= eqxx /= eqseq_cons eqxx /=.
move: nequv; apply contra => /eqP eq.
have := prefix_take u (seq.size (long_cprefix u v)).+1.
have := prefix_take v (seq.size (long_cprefix u v)).+1.
rewrite -eq => pru prv.
have /size_prefix := long_cprefixP pru prv.
rewrite size_take; case: ltnP => [|_]; first by rewrite long_cprefixC ltnn.
move/(prefix_sizeE (long_cprefixr v u)) <-.
rewrite eq in pru prv.
have /size_prefix := long_cprefixP pru prv.
rewrite size_take; case: ltnP => [|_]; first by rewrite long_cprefixC ltnn.
by move/(prefix_sizeE (long_cprefixl v u)) => {2}<-.
Qed.

Context {B : choiceType} (x y : B) (neqxy : x != y).

Definition reduced_compressed_pres : pres B :=
  reduce2letters (strong_compress_pres P k.+1) strcA neqxy.

(* TODO : De duplicate *)
Local Lemma ltkszu : k <= seq.size u.
Proof.
rewrite leqNgt; apply/negP => Habs.
have {}Habs : long_cprefix (a :: u) (a :: v) = a :: u.
   by apply: (prefix_sizeE (long_cprefixl _ _)); rewrite -/k /=.
move: NonSpecial.
by have:= (long_cprefixr (a :: u) (a :: v)); rewrite Habs => ->.
Qed.
Local Lemma ltkszv : k <= seq.size v.
Proof.
rewrite leqNgt; apply/negP => Habs.
have {}Habs : long_cprefix (a :: u) (a :: v) = a :: v.
  by apply: (prefix_sizeE (long_cprefixr _ _)); rewrite -/k /=.
move: NonSpecial.
by have:= (long_cprefixl (a :: u) (a :: v)); rewrite Habs andbC => ->.
Qed.

Theorem compress_reduce_dec :
  WPdecidable reduced_compressed_pres -> WPdecidable P.
Proof.
move=> Hdec.
have: WPdecidable (strong_compress_pres P k.+1).
  pose U := strong_compress k.+1 u.
  pose V := strong_compress k.+1 v.
  move/(reduce2letters_dec (U := U) (V := V) strcAneqB): Hdec; apply.
  by rewrite /= Hrel /= !ltnS !ltnNge ltkszu ltkszv /=.
exact: (strong_compress_dec Hgen Hrel nequv).
Qed.

Lemma reduced_compressed_presE :
  prelat reduced_compressed_pres =
    [:: (compressreduce strcA x y k.+1 (a :: u),
         compressreduce strcA x y k.+1 (a :: v))].
Proof.
rewrite /= /rel2letters /strong_compress_pres /= Hrel /=.
by rewrite !compressreduceE //= !ltnS !ltnNge ltkszu ltkszv /=.
Qed.
Fact wf_fast_compressreduce :
  correctrelat [:: (compressreduce strcA x y k.+1 (a :: u),
                    compressreduce strcA x y k.+1 (a :: v))] (mem [:: x; y]).
Proof. by rewrite -reduced_compressed_presE wf_relat. Qed.
Definition fast_reduced_compressed_pres : pres B :=
  Pres [:: x; y] _ (uniq_ab neqxy) wf_fast_compressreduce.

Lemma fast_reduced_compressed_presE :
  fast_reduced_compressed_pres = reduced_compressed_pres.
Proof. by apply/eqP; rewrite -eqpresE reduced_compressed_presE //= !eqxx. Qed.

Theorem fast_compress_reduce_dec :
  WPdecidable fast_reduced_compressed_pres -> WPdecidable P.
Proof. by rewrite fast_reduced_compressed_presE => /compress_reduce_dec. Qed.

End StrongCompressAndReduce.

Definition testpres :=
  make_pres [:: 1; 0] [:: ([:: 0;0;1;1;1], [:: 0;1;0;1;1;1])].
Definition compressed := strong_compress_pres testpres 2.

Definition reduced := @reduce2letters _ _ compressed [:: 0; 0] 0 1 is_true_true.
Definition fast_reduced :=
  @fast_reduced_compressed_pres int testpres 0 [::0;1;1;1] [::1;0;1;1;1]
    erefl is_true_true int 0 1 is_true_true.

(* Reduce to  = [:: ([:: 0; 1; 1; 1], [:: 1; 1; 1; 1; 1])] which is Watier *)
Goal prelat reduced = [:: ([:: 0; 1; 1; 1], [:: 1; 1; 1; 1; 1])]. by []. Qed.
Goal prelat fast_reduced = [:: ([:: 0; 1; 1; 1], [:: 1; 1; 1; 1; 1])]. by []. Qed.

