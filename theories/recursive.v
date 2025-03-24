From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.

Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import present rewcert fastcert criteria homogeneous batchchecker factor.


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
  Pres (allwords (pgen P) k) _ (allwords_uniq k (uniq_pgen P))
    (correctrelat_strong_compress P k).

Theorem StrongCompress_dec (P : pres Alph) :
  forall a b u v,
    pgen P = [:: a; b] -> prelat P = [:: (a :: u, a :: v)] ->
    let k := seq.size (long_cprefix (a :: u) (a :: v)) in
    k <= seq.size (long_csuffix (a :: u) (a :: v)) ->
    WPdecidable (strong_compress_pres P k) -> WPdecidable P.
Admitted.


(* strong compress and subtitute *)
Fixpoint StCS k w u :=
  if u is u0 :: u' then
    if seq.size u < k then [::]
    else (take k u == w) :: StCS k w u'
  else [::].

Definition StCSubs k w (subs : bool -> Alph) u :=
  [seq subs i | i <- StCS k w u].

End StrongCompress.

Eval compute in StCSubs 3 [:: 1; 0; 1] (fun x => if x then 1 else 0)
                  [:: 1; 1; 0; 1; 0; 1; 1; 1; 0; 0; 1; 0].
