From Coq Require Import Znat BinIntDef Uint63 PArray.
From mathcomp Require Import all_ssreflect.

Require Import factor int_seq present rewcert inttrie.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Import Order.TTheory.


Lemma cons_nnil (T : eqType) (i : T) (u : seq T) : (i :: u == rev [::]) = false.
Proof. by apply/negP => /eqP. Qed.


Section LHSPrefixes.

Variable trielen : int.
Hypothesis (maxlen : (0 < trielen <= max_length)%O).

Implicit Types (i j : int) (u v w : word int) (r : word int * word int)
  (P : pres int) (R : relat int) (tr : rewtrie).

Variable (R : relat int).
Hypothesis Rcorr : correctrelat R (<%O^~ trielen).

Lemma getsub_mktrie v :
  getsubtrie (mktrie trielen R) v =
    mktrie trielen [seq (drop (size v) r.1, r.2) | r <- R & prefix v r.1].
Proof.
case: v => [| v0 v] /=.
  suff -> : [seq (drop 0 r.1, r.2) | r <- R & prefix [::] r.1] = R.
    by case: mktrie.
  rewrite (eq_filter (a2 := xpredT)); last by move=> [r1 r2]; apply: prefix0s.
  rewrite filter_predT (eq_map (g := id)) ?map_id // => -[r1 r2] /=.
  by rewrite drop0.
elim: R Rcorr => [| [r1 r2] R' IHR] //=.
case/andP => /andP[allr1 allr2 corrR].
rewrite /addpair /addtrie /= getsub_updatetrie //; last exact: is_flmktrie.
case (boolP (prefix (v0 :: v) r1)) => [pref | _] /=; last exact: IHR.
by rewrite /addpair /addtrie /= IHR.
Qed.

Definition islhsprefix tr u :=
  if getsubtrie tr u is Trie x a then length a != 0 else false.

Lemma islhsprefixP u :
  reflect (exists r, [&& r \in R, prefix u r.1 & u != r.1])
    (islhsprefix (mktrie trielen R) u).
Proof.
rewrite /islhsprefix getsub_mktrie //.
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
    by rewrite lena; apply: (ltx0 i).
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
  apply: get_not_default_lt; apply/eqP; rewrite defa.
  by case: eqP uin => // ->.
rewrite -cats1 prefixes_trie_recE.
by apply/mapP; exists u.
Qed.

Section Sorted.

Import DefaultSeqLexiOrder.

Lemma catl_ltxiE u v w : (u ++ v < u ++ w)%O = (v < w)%O.
Proof.
elim: u => [| u0 u]; first by rewrite !cat0s.
by rewrite /= eqhead_ltxiE.
Qed.

Lemma ltxirev_trans : transitive (fun u v => rev u < rev v)%O.
Proof. by move=> y x z; apply: lt_trans. Qed.

Lemma prefixes_trie_rec_sorted rpre tr :
  sorted (fun u v => rev u < rev v)%O (prefixes_trie_rec rpre tr).
Proof.
move: tr rpre; apply: indtrie => //= a _ IH _ rpre.
case eqP => //= _.
have := leqnn (to_nat (length a)).
elim: {1 3}(to_nat (length a)) => [//| n IHn] ltn.
rewrite -(addn1) iotaD /= add0n !map_cat flatten_cat cat_path /= cats0.
rewrite {}IHn ?(ltnW ltn) //=.
rewrite (path_sortedE ltxirev_trans) {}IH; first last.
  rewrite ltintE of_natK //.
  exact/(ltn_trans ltn)/lt_lenght_wB.
rewrite andbT; apply/allP => /= u /suffix_prefixes_trie_rec.
rewrite -prefix_rev rev_cons -cats1 => /prefixP[/= suf ->].
case/lastP Hflat : (flatten _) => [|f fn] /=.
  by rewrite -{1}(cats0 (rev rpre)) -catA catl_ltxiE ltxi0s.
have : fn \in rcons f fn by rewrite mem_rcons inE eqxx.
rewrite last_rcons -{}Hflat => /flatten_mapP[/= i] /mapP[/= m].
rewrite mem_iota /= add0n => ltmn {i}->.
have {}ltmn : (of_nat m < of_nat n)%O.
  rewrite ltintE !of_natK //.
  exact/(ltn_trans ltn)/lt_lenght_wB.
  exact/(ltn_trans ltmn)/(ltn_trans ltn)/lt_lenght_wB.
move/suffix_prefixes_trie_rec.
rewrite -prefix_rev rev_cons -cats1 => /prefixP[/= s2] ->.
rewrite -!catA catl_ltxiE neqhead_ltxiE //.
by move: ltmn; rewrite lt_neqAle => /andP[].
Qed.
Lemma prefixes_trie_sorted tr : sorted <%O (prefixes_trie tr).
Proof. by rewrite /prefixes_trie sorted_map (prefixes_trie_rec_sorted _ _). Qed.
End Sorted.

Lemma prefixes_trie_uniq tr : uniq (prefixes_trie tr).
Proof.
exact: (sorted_uniq lt_trans lt_irreflexive (prefixes_trie_sorted _)).
Qed.


Lemma prefixes_mktrieE u :
  (islhsprefix (mktrie trielen R) u) = (u \in prefixes_trie (mktrie trielen R)).
Proof.
rewrite /islhsprefix.
move: (mktrie trielen R) (is_flmktrie maxlen R) u.
apply: indtrie => [|a _ IHtr x] /= fla [|u0 u] //=.
  exact: nil_in_prefixes_trie.
case/(flarrayP maxlen): fla => /= lena defa flta.
rewrite mem_prefixes_trieE //.
case: (boolP (u0 < length a)%O) => [ltu0 | /negbTE]; first last.
  move/get_out_of_bounds ->; rewrite defa /= /prefixes_trie /=.
  by case u.
apply: (IHtr u0 ltu0); apply: flta.
apply: (Order.POrderTheory.lt_le_trans ltu0).
move: lena => []-> //; apply: Order.POrderTheory.ltW.
by case/andP : maxlen.
Qed.

Lemma prefixes_mktrieP u :
  reflect (exists r, [&& r \in R, prefix u r.1 & u != r.1])
    (u \in prefixes_trie (mktrie trielen R)).
Proof. by rewrite -prefixes_mktrieE; exact/islhsprefixP. Qed.

End LHSPrefixes.


Module Example.

Section Example.

Definition P := make_pres [::0; 1]
  [::
   ([::1;0], [::0;1]);
   ([::0;0;0], [::0;1]);
   ([::1;1], [::1])
  ].

Let tr := mktrie (pres_trielen P) (prelat P).
Goal (prefixes_trie tr) = [:: [::]; [:: 0]; [:: 0; 0]; [:: 1]].
Proof. by []. Qed.

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

Goal (prelat Pres) =
       [:: ([:: 0; 1; 0; 0; 1; 0], [:: 0; 0; 0; 0; 0; 0]);
        ([:: 0; 1; 0; 0; 0; 0; 0; 0; 0], [:: 0; 0; 0; 0; 0; 0; 0; 1; 0])].
Proof. by []. Qed.


Goal (prefixes_trie tr2) =
       [:: [::]; [:: 0]; [:: 0; 1]; [:: 0; 1; 0]; [:: 0; 1; 0; 0];
        [:: 0; 1; 0; 0; 0]; [:: 0; 1; 0; 0; 0; 0];
        [:: 0; 1; 0; 0; 0; 0; 0]; [:: 0; 1; 0; 0; 0; 0; 0; 0];
        [:: 0; 1; 0; 0; 1]].
Proof. by []. Qed.

Goal sorted <%O (prefixes_trie tr2 : seq (seqlexi _)).
Proof. by []. Qed.

End Example.

End Example.

Module Example2.

Section Largest.

Load "largest.v".

Let Ptrie := mktrie (pres_trielen present_final) (prelat present_final).

Goal sorted <%O (prefixes_trie Ptrie : seq (seqlexi _)).
Proof. by vm_compute. Qed.

Goal size (prefixes_trie Ptrie : seq (seqlexi _)) = 465%N.
Proof. by []. Qed.

End Largest.

End Example2.

(*
Definition is_reduced R :=
  all (fun rel => (size (rewrites R rel.1) == 1%N)
                  && (size (rewrites R rel.2) == 0%N)) R.
*)
