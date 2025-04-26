(** Native int is a well founded choice and type **)
From Coq Require Import Znat BinIntDef Uint63 PArray.
From mathcomp Require Import all_ssreflect.

Require Import int_seq wfsizelexi present rewcert inttrie.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.


Implicit Types (u v w : word int)
  (P : pres int) (R : relat int) (tr : @trie (word int)).

Definition is_reduced R :=
  all (fun rel => (size (rewrites R rel.1) == 1%N)
                  && (size (rewrites R rel.2) == 0%N)) R.

Fixpoint prefixes_trie_rec pre tr : seq (word int) :=
  match tr with
  | Trie x a =>
      if length a == 0 then [::]
      else pre :: flatten (
               [seq prefixes_trie_rec (g :: pre)
                  a.[g] | g <- [seq of_nat n | n <- iota 0 (to_nat (length a))]])
  | Empty => [::]
  end.
Definition prefixes_trie tr := [seq rev s | s <- prefixes_trie_rec [::] tr].

Lemma mem_prefixes_trie_rec pre tr u :
  u \in prefixes_trie_rec pre tr -> suffix pre u.
Proof.
move: tr pre; apply: indtrie => //= a HE IH _ pre.
case eqP => //= _; rewrite inE => /orP[/eqP ->|]; first exact: suffix_refl.
case/flatten_mapP=> /= i /mapP[/= n].
rewrite mem_iota add0n /= => ltn {i}->.
have {}/IH/[apply] : (of_nat n < length a)%O.
  by rewrite ltintE of_natK //; exact/(ltn_trans ltn)/lt_lenght_wB.
by rewrite -cat1s => /catl_suffix.
Qed.

Lemma prefixes_trie_rec_uniq pre tr : uniq (prefixes_trie_rec pre tr).
Proof.
move: tr pre; apply: indtrie => //= a HE IH _ pre.
case eqP => //= _; apply/andP; split.
  apply/negP => /flatten_mapP[/= i] /mapP[/= n].
  rewrite mem_iota add0n => /= ltn {i}->.
  move/mem_prefixes_trie_rec => /size_suffix /=.
  by rewrite ltnn.
have := leqnn (to_nat (length a)).
elim: {1 3}(to_nat (length a)) => [//| n IHn] ltn.
rewrite -(addn1) iotaD /= add0n !map_cat flatten_cat cat_uniq.
rewrite {}IHn /=; last exact: ltnW.
rewrite cats0 andbC {}IH /=; first last.
  rewrite ltintE of_natK //; exact/(ltn_trans ltn)/lt_lenght_wB.
apply/negP => /hasP/=[u] /mem_prefixes_trie_rec sufnu.
case/flatten_mapP => /= i /mapP[/= m].
rewrite mem_iota /= add0n => ltmn {i}-> /mem_prefixes_trie_rec sufmu.
move: sufnu sufmu; rewrite !suffixE /= => /eqP ->.
rewrite eqseq_cons => /andP[+ _] => /eqP/(congr1 (fun i => to_nat i))/eqP.
rewrite !of_natK; first last.
  exact/(ltn_trans ltn)/lt_lenght_wB.
  exact/(ltn_trans ltmn)/(ltn_trans ltn)/lt_lenght_wB.
by rewrite gtn_eqF.
Qed.
Lemma prefixes_trie_uniq tr : uniq (prefixes_trie tr).
Proof.
rewrite (map_inj_uniq (can_inj revK)).
exact: prefixes_trie_rec_uniq.
Qed.

Lemma mem_prefixes_addpair sz tr r1 r2 u :
  (0 < sz <= max_length)%O ->
  is_fltrie sz tr -> all (<%O^~ sz) r1 ->
  u \in prefixes_trie (addpair sz (r1, r2) tr) ->
  (u != r1) && prefix u r1 || (u \in prefixes_trie tr).
Proof.
move=> Hsz; rewrite /prefixes_trie; move: [::] => pre.
rewrite -{1}(revK u) !(mem_map (can_inj revK)).
move: tr u pre; rewrite /addpair /addtrie; apply: indtrie => /=.
- move=> u pre _; rewrite in_nil orbF.
  elim: r1 u pre => [//| l1 r1 IHr1] u pre /= /andP[ltl1 {}/IHr1 Hrec].
  rewrite length_set length_make.
  have -> : sz ≤? max_length by move: Hsz => /andP[_].
  rewrite -(inj_eq (can_inj to_natK)) to_nat0 gtn_eqF; first last.
    by move: Hsz => /andP[+ _]; rewrite ltintE.
  case: u => // u0 u.


Qed.


Lemma mem_prefixes_mktrie_cat sz R1 R2 u :
  (u \in prefixes_trie (mktrie sz (R1 ++ R2))) =
  (u \in prefixes_trie (mktrie sz R1)) || (u \in prefixes_trie (mktrie sz R2)).
Proof.
rewrite /prefixes_trie; move: [::] => pre.
rewrite -(revK u) !(mem_map (can_inj revK)).
elim: R1 pre (rev u) => [ // | [r1 r2] R1 IHR1] /= pre {}u.
rewrite /addpair /addtrie /=.
  


                
Lemma mem_prefixes_addpair sz tr r1 r2 u :
  is_fltrie sz tr -> all (<%O^~ sz) r1 ->
  u \in prefixes_trie (addpair sz (r1, r2) tr) ->
  (u != r1) && prefix u r1 || (u \in prefixes_trie tr).
Proof.
Admitted.

Lemma prefixes_mktrieP sz R u :
  (0 < sz <= max_length)%O ->
  correctrelat R (<%O^~ sz) ->
  (u \in prefixes_trie (mktrie sz R)) =
    has (fun w => (u != w) && prefix u w) [seq r.1 | r <- R].
Proof.
move=> Hsz Hall; apply/idP/idP.
  elim: R Hall u => [|[r1 r2] R IHR] //=.
  rewrite -andbA; case/and3P => allr1 _ /[dup] {}/IHR Hrec Hall u Hu.
  suff {Hrec} : ((u != r1) && prefix u r1) || (u \in prefixes_trie (mktrie sz R)).
    by case/orP => [-> //| /Hrec ->]; rewrite orbT.
  exact: (mem_prefixes_addpair (is_flmktrie Hsz _) allr1 Hu).
elim: R Hall u => [|[r1 r2] R IHR] //=.
rewrite -andbA; case/and3P => allr1 _ /[dup] {}/IHR Hrec Hall u Hu.


  
  rewrite /addpair /addtrie /prefixes_trie in Hu.
  elim: r1 allr1 u Hu => [/= _| r0 r IHr allr] [|u] /=.
    case: (mktrie sz R) => [|] //=.
    
Module Example.

Section Example.

Definition P := make_pres [::0; 1]
  [::
   ([::1;0], [::0;1]);
   ([::0;0;0], [::0;1]);
   ([::1;1], [::1])
  ].

Let tr := mktrie (pres_trielen P) (prelat P).
Eval compute in (prefixes_trie tr).

Definition AB_AAAAAA_ABAABA :=
  make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])].
Definition cert :=
  [::
       add_rel [::0;1;0;0;1;0] [::0;0;0;0;0;0]
         [:: RTriple 0 0 false];
       add_rel [::0;1;0;0;0;0;0;0;0] [::0;0;0;0;0;0;0;1;0]
         [:: RTriple 0 3 true;
             RTriple 1 0 true];
       rm_rel 0
         [:: RTriple 0 0 false]].
Definition Pres := @Pres _
                     (gen_cert (pgen AB_AAAAAA_ABAABA) cert)
                     (rel_cert (prelat AB_AAAAAA_ABAABA) cert)
                     is_true_true is_true_true.

Let tr2 := mktrie (pres_trielen Pres) (prelat Pres).

Eval compute in (prelat Pres).
(* [:: ([:: 0; 1; 0; 0; 1; 0], [:: 0; 0; 0; 0; 0; 0]);
       ([:: 0; 1; 0; 0; 0; 0; 0; 0; 0], [:: 0; 0; 0; 0; 0; 0; 0; 1; 0])] *)

Eval compute in (prefixes_trie tr2).

