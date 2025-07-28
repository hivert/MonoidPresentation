(* The goal of this file is to prove that if all the relation preserve lenght
   the equality is decidable since we are confined in a finite set *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq
  eqtype choice fintype path tuple fingraph.
Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section Homogeneous.

Context {A : choiceType}.
Implicit Type (u v : word A) (R : relat A).

Definition homogeneous R := forall r, r \in R -> size r.1 = size r.2.
Definition is_homogeneous R := all (fun r => size r.1 == size r.2) R.

Lemma is_homogeneousP R : reflect (homogeneous R) (is_homogeneous R).
Proof. by apply (iffP allP) => /= H [r1 r2] /= /H/eqP /=. Qed.

Section Rewrite.

Variable R : relat A.
Hypothesis Rhomog : is_homogeneous R.

Lemma size_rewrites u v : v \in rewrites R u -> size v = size u.
Proof.
case/rewritesP => pre suf r {u}->{v}-> /(allP Rhomog)/eqP eqsz.
by rewrite !size_cat eqsz.
Qed.
Lemma size_rewrites_to u v : rewrites_to R u v -> size v = size u.
Proof.
case=> pth; elim: pth u => [/= u _ -> // | p0 pth IHpth /= u /andP[]].
by move=> /size_rewrites <- /IHpth/[apply].
Qed.

End Rewrite.

Lemma homog_undirected R : is_homogeneous R -> is_homogeneous (undirected R).
Proof.
move/allP => /= hom; apply/allP => /= [[r1 r2]].
by rewrite mem_undirected => /orP[] /hom/= /eqP ->.
Qed.

Lemma size_equiv R u v : is_homogeneous R -> u = v %[mod R] -> size v = size u.
Proof. by move/homog_undirected => /[swap] /size_rewrites_to. Qed.


Section WordOfSize.

Variable R : pres A.
Hypothesis Rhomog : is_homogeneous R.

Variable n : nat.

Record wsize := WordOfSize {
     wval :> seq A;
     wval_of_size : (wval \in words_of R) && (size wval == n)
  }.

HB.instance Definition _ := [isSub of wsize for wval].
HB.instance Definition _ := [Choice of wsize by <:].

Implicit Type (w : wsize).
Lemma wsizeE w : size w = n.
Proof. by case: w => /= w /andP[_ /eqP]. Qed.
Lemma wsizeP w : val w \in words_of R.
Proof. by case: w => /= w /andP[]. Qed.

Definition wtuple := n.-tuple (seq_sub (pgen R)).
Definition wtuple_of_wsize_val w : seq (seq_sub (pgen R)) := pmap insub w.
Lemma wtuple_of_wsize_valE w : map val (wtuple_of_wsize_val w) = w.
Proof.
rewrite (pmap_filter (insubK _)) /words_of /=.
case: w => [/= w /andP[+ _]].
elim: w => [// | w0 w IHw] /= /andP[w0in {}/IHw->].
rewrite isSome_insub /=.
by suff -> : w0 \in pgen R by [].
Qed.
Fact wtuple_of_wsize_subproof w : size (wtuple_of_wsize_val w) == n.
Proof. by rewrite -(size_map val) wtuple_of_wsize_valE wsizeE. Qed.
Definition wtuple_of_wsize w : wtuple := Tuple (wtuple_of_wsize_subproof w).

Fact wsize_of_wtuple_subproof (t : wtuple) :
  let w := map val (val t) in (w \in words_of R) && (size w == n).
Proof.
case: t => [t szt]; rewrite /= size_map szt andbT.
by apply/allP => a /mapP[/= [b /= Hb _ {a}->]].
Qed.
Definition wsize_of_wtuple (t : wtuple) :=
  WordOfSize (wsize_of_wtuple_subproof t).

Fact wtuple_of_wsizeK : cancel wtuple_of_wsize wsize_of_wtuple.
Proof. by move=> w; apply val_inj; rewrite /= wtuple_of_wsize_valE. Qed.
HB.instance Definition _ := Countable.copy wsize (can_type wtuple_of_wsizeK).
HB.instance Definition _ :=
  isFinite.Build wsize (pcan_enumP (can_pcan wtuple_of_wsizeK)).

Lemma wsize_rewrites_wsize (u : wsize) (v : seq A) :
  v \in rewrites (undirected R) u -> {w : wsize | val w = v}.
Proof.
move=> Ruv.
suff Hv : (v \in words_of R) && (size v == n) by exists (WordOfSize Hv).
rewrite (size_rewrites (homog_undirected Rhomog) Ruv) wsizeE eqxx andbT.
move: Ruv => /rewrites_to1/equiv_words_ofE <-.
exact: wsizeP.
Qed.


Definition rewclass (u : wsize) : seq wsize :=
  dfs (fun v : wsize => pmap insub (rewrites (undirected R) v))
    #|(wsize : finType)| [::] u.

Lemma rewclassP (u v : wsize) : reflect (u = v %[mod R]) (v \in rewclass u).
Proof.
apply: (iffP dfsP) => /=[[pth Hpth {v}->] |].
  exists (map val pth) => //=; last by rewrite last_map.
  by apply: homo_path Hpth => {}u v /=; rewrite mem_pmap_sub.
case=> pth Hpth eqv; exists (pmap insub pth); first last.
  apply: val_inj; rewrite [LHS]/= {v}eqv.
  rewrite -[RHS]last_map (pmap_filter (insubK _)) /=; congr last.
  elim: pth u Hpth => [// | p0 p IHp u] /= /andP[Hp0].
  case: (wsize_rewrites_wsize Hp0) => w <-.
  by rewrite isSome_insub wval_of_size /= => /IHp <-.
elim: pth u Hpth {v eqv} => [// | p0 p IHp u] /= /andP[Hp0].
case: (wsize_rewrites_wsize Hp0) => w /[dup] Hw <- /IHp.
by rewrite valK /= => ->; rewrite andbT mem_pmap_sub Hw.
Qed.

End WordOfSize.

Theorem homog_dec (R : pres A) : is_homogeneous R -> WPdecidable R.
Proof.
move=> homog u v uin vin.
case: (boolP (size v == size u)) => [eqsz|neqsz].
  have {}uin : (u \in words_of R) && (size u == size u) by rewrite uin eqxx.
  have {}vin : (v \in words_of R) && (size v == size u) by rewrite vin eqsz.
  case: (boolP (WordOfSize vin \in rewclass (WordOfSize uin))) =>
        /(rewclassP homog) Ruv; [left|right]; exact: Ruv.
right; move: neqsz => /[swap]/(size_equiv homog) ->.
by rewrite eqxx.
Qed.

End Homogeneous.
