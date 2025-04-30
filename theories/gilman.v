From Coq Require Import Znat BinIntDef Uint63 PArray.
From mathcomp Require Import all_ssreflect.

Require Import factor int_seq wfsizelexi present rewcert inttrie.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.



Lemma cons_nnil (T : eqType) (i : T) (u : seq T) : (i :: u == rev [::]) = false.
Proof. by apply/negP => /eqP. Qed.


Section LHSPrefix.

Variable trielen : int.
Hypothesis (maxlen : (0 < trielen <= max_length)%O).

Implicit Type (R : relat int) (t : rewtrie) (u v w : seq int).

Lemma getsub_mktrie R v :
  correctrelat R (<%O^~ trielen) ->
  getsubtrie (mktrie trielen R) v =
    mktrie trielen [seq (drop (size v) r.1, r.2) | r <- R & prefix v r.1].
Proof.
case: v => [corr | v0 v] /=.
  suff -> : [seq (drop 0 r.1, r.2) | r <- R & prefix [::] r.1] = R.
    by case: mktrie.
  rewrite (eq_filter (a2 := xpredT)); last by move=> [r1 r2]; apply: prefix0s.
  rewrite filter_predT (eq_map (g := id)) ?map_id // => -[r1 r2] /=.
  by rewrite drop0.
elim: R => [| [r1 r2] R IHR] //=.
case/andP => /andP[allr1 allr2 corrR].
rewrite /addpair /addtrie /= getsub_updatetrie //; last exact: is_flmktrie.
case (boolP (prefix (v0 :: v) r1)) => [pref | _] /=; last exact: IHR.
by rewrite /addpair /addtrie /= IHR.
Qed.


Variable (R : relat int).
Hypothesis genRlen : correctrelat R (<%O^~ trielen).


Let Ptrie := mktrie trielen R.

Definition islhsprefix u :=
  if getsubtrie Ptrie u is Trie x a then length a != 0 else false.


Lemma islhsprefixP u :
  reflect (exists r, [&& r \in R, prefix u r.1 & u != r.1])
    (islhsprefix u).
Proof.
rewrite /islhsprefix /Ptrie getsub_mktrie //.
apply (iffP idP).
  have : all (fun r => (r \in R) && (prefix u r.1)) [seq r <- R | prefix u r.1].
    by apply/allP => [/= [r1 r2]]; rewrite mem_filter /= => /andP[-> ->].
  elim: (filter _ _) => [//| /= [r1 r2] R' IHR] /=.
  case/andP => /andP[inR pref] {}/IHR; case: mktrie => [//= _| x a Hrec].
    case Hdrop : (drop (size u) r1) (prefix_drop_nil pref) => [// | i v] /= Heq.
    by move=> _; exists (r1, r2); rewrite /= inR pref /= Heq.
  rewrite /addpair /addtrie /=.
  case Hdrop : (drop (size u) r1) (prefix_drop_nil pref) => [// | i v] /= Heq.
  case: eqP Hrec => [_ _ _| /= _ /(_ is_true_true) + _ //].
  by exists (r1, r2); rewrite /= inR pref /= Heq.
case=> [[r1 r2] /and3P[/= rinR pref nequr1]].
elim: R rinR => [// |[s1 s2] R' IHR] /=.
  rewrite inE => /orP[/eqP[{s1}<- {s2}<- {IHR}] | ] /=.
  rewrite pref /= /addpair /addtrie /=.
  case Hdrop : (drop (size u) r1) (prefix_drop_nil pref) => [| i v] /= Heq.
    exfalso; move: Heq nequr1; rewrite eq_refl => /eqP ->.
    by rewrite eqxx.
  move=> {Heq}; case: mktrie => [| x a]/=.
    by rewrite length_set length_make_trielen // (negbTE (len_neq0 _)).
  case: eqP => [lena | /eqP/negbTE].
    by rewrite  !length_set length_make_trielen // (negbTE (len_neq0 _)).
  by rewrite length_set => ->.
move=> {}/IHR IHR; case: (prefix u s1) => //=.
rewrite /addpair /addtrie /=.
case Hdrop : (drop (size u) s1) => [// | i v] /=.
  by case: mktrie IHR.
case: mktrie {IHR} => [| x a]/=.
  by rewrite length_set length_make_trielen // (negbTE (len_neq0 _)).
case: eqP => [lena | /eqP/negbTE].
  by rewrite  !length_set length_make_trielen // (negbTE (len_neq0 _)).
by rewrite length_set => ->.
Qed.

End LHSPrefix.

Implicit Types (i j : int) (u v w : word int) (r : word int * word int)
  (P : pres int) (R : relat int) (tr : @trie (word int)).


Fixpoint prefixes_trie_rec rpre tr : seq (word int) :=
  match tr with
  | Trie x a =>
      if length a == 0 then [::]
      else rpre :: flatten (
               [seq prefixes_trie_rec (g :: rpre)
                  a.[g] | g <- [seq of_nat n | n <- iota 0 (to_nat (length a))]])
  | Empty => [::]
  end.
Definition prefixes_trie tr := [seq rev s | s <- prefixes_trie_rec [::] tr].

Lemma nil_in_prefixes_trie x a :
  (length a != 0) = ([::] \in prefixes_trie (Trie x a)).
Proof.
rewrite /prefixes_trie /=; apply/idP/idP => [/negbTE -> /= |].
  by rewrite inE eqxx.
by case: eqP.
Qed.

Lemma prefixes_trie_recE rpre tr :
  prefixes_trie_rec rpre tr = [seq rev u ++ rpre| u <- prefixes_trie tr].
Proof.
rewrite /prefixes_trie; move: tr rpre.
apply: indtrie => [|a Hdef IHtr x] rpre //=.
case: eqP => // _; rewrite !map_cons revK /=; congr cons.
rewrite -!map_comp map_flatten; congr flatten.
rewrite -map_comp; apply eq_in_map => /= n; rewrite mem_iota add0n /= => ltn.
have /of_natK Hn : n < BinInt.Z.to_nat wB.
  exact: (ltn_trans ltn (lt_lenght_wB _)).
move: ltn; rewrite -{1}Hn -ltintE; move: (of_nat n) {Hn} => {}n ltn.
rewrite IHtr // (IHtr _ _ [:: n]) //.
rewrite -!map_comp; apply eq_map => u /=.
by rewrite !revK -catA cat1s.
Qed.

Lemma suffix_prefixes_trie_rec rpre tr u :
  u \in prefixes_trie_rec rpre tr -> suffix rpre u.
Proof.
by rewrite prefixes_trie_recE => /mapP[/= v _ ->]; apply: suffix_suffix.
Qed.


Lemma mem_prefixes_trieE x a (i : int) u :
  default a = Empty ->
  (i :: u \in prefixes_trie (Trie x a)) = (u \in prefixes_trie a.[i]).
Proof.
move=> defa.
rewrite {1}/prefixes_trie /=; case: (boolP (length a == 0)) => [/eqP|] lena /=.
  rewrite get_out_of_bounds; first last.
    by rewrite lena; apply: (Order.BPOrderTheory.ltx0 i).
  by rewrite /prefixes_trie defa.
rewrite inE cons_nnil /=.
rewrite -(revK (i :: u)) rev_cons (mem_map (can_inj revK)).
apply/flatten_mapP/idP => [[ /= j /mapP[/= n]] | uin].
  rewrite mem_iota /= add0n => ltnl eqi.
  have /of_natK : n < BinInt.Z.to_nat wB.
    exact: (ltn_trans ltnl (lt_lenght_wB _)).
  rewrite -eqi => Hn; subst n => {eqi}.
  rewrite -cats1 prefixes_trie_recE => /mapP[/= v /[swap]].
  by move/(congr1 rev); rewrite !rev_cat /= !revK => [[-> ->]].
exists i.
  apply/mapP; exists (to_nat i); last by rewrite to_natK.
  rewrite mem_iota /= add0n -ltintE.
  apply/contraLR: uin => /negbTE/get_out_of_bounds => ->.
  by rewrite /prefixes_trie defa.
rewrite -cats1 prefixes_trie_recE.
by apply/mapP; exists u.
Qed.

Lemma prefixes_trie_rec_uniq rpre tr : uniq (prefixes_trie_rec rpre tr).
Proof.
move: tr rpre; apply: indtrie => //= a HE IH _ rpre.
case eqP => //= _; apply/andP; split.
  apply/negP => /flatten_mapP[/= i] /mapP[/= n].
  rewrite mem_iota add0n => /= ltn {i}->.
  move/suffix_prefixes_trie_rec => /size_suffix /=.
  by rewrite ltnn.
have := leqnn (to_nat (length a)).
elim: {1 3}(to_nat (length a)) => [//| n IHn] ltn.
rewrite -(addn1) iotaD /= add0n !map_cat flatten_cat cat_uniq.
rewrite {}IHn /=; last exact: ltnW.
rewrite cats0 andbC {}IH /=; first last.
  rewrite ltintE of_natK //; exact/(ltn_trans ltn)/lt_lenght_wB.
apply/negP => /hasP/=[u] /suffix_prefixes_trie_rec sufnu.
case/flatten_mapP => /= i /mapP[/= m].
rewrite mem_iota /= add0n => ltmn {i}-> /suffix_prefixes_trie_rec sufmu.
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

Section Mktrie.

Variable trielen : int.
Hypothesis le_trielen : (0 < trielen <= max_length)%O.

(*
Lemma prefixes_trie_len u :
  u \in prefixes_trie (mktrie trielen R) -> all (<%O^~ trielen) u.
Proof.
move: (mktrie trielen R) (is_flmktrie le_trielen R) u.
apply: indtrie => [//|a _ IHtr x] /= fla u.
case: u => [// | u0 u].
*)

Variable R : relat int.
Hypothesis Rcorr : correctrelat R (<%O^~ trielen).

Lemma prefixes_mktrieE u :
  (islhsprefix trielen R u) = (u \in prefixes_trie (mktrie trielen R)).
Proof.
rewrite /islhsprefix.
move: (mktrie trielen R) (is_flmktrie le_trielen R) u.
apply: indtrie => [|a _ IHtr x] /= fla [|u0 u] //=.
  exact: nil_in_prefixes_trie.
case/(flarrayP le_trielen): fla => /= lena defa flta.
rewrite mem_prefixes_trieE //.
case: (boolP (u0 < length a)%O) => [ltu0 | /negbTE]; first last.
  move/get_out_of_bounds ->; rewrite defa /= /prefixes_trie /=.
  by case u.
apply: (IHtr u0 ltu0); apply: flta.
apply: (Order.POrderTheory.lt_le_trans ltu0).
move: lena => []-> //; apply: Order.POrderTheory.ltW.
by case/andP : le_trielen.
Qed.

Lemma prefixes_mktrieP u :
  reflect (exists r, [&& r \in R, prefix u r.1 & u != r.1])
    (u \in prefixes_trie (mktrie trielen R)).
Proof. by rewrite -prefixes_mktrieE; exact/(islhsprefixP le_trielen Rcorr). Qed.

End Mktrie.


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

End Example.
End Example.

Definition is_reduced R :=
  all (fun rel => (size (rewrites R rel.1) == 1%N)
                  && (size (rewrites R rel.2) == 0%N)) R.

