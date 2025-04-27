From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Potential PRs to MathComp *)
Section Compl.
Context {T : Type}.
Definition swap (p : T * T) := (p.2, p.1).
Lemma swapK : involutive swap. Proof. by move => [i j]. Qed.
Lemma swap_inj : injective swap. Proof. exact: (can_inj swapK). Qed.
Implicit Type u v : seq T.
Lemma catl_inj u : injective (cat u).
Proof. by elim: u => [|a u IHu] //= v1 v2 []; exact: IHu. Qed.
Lemma catr_inj u : injective (cat^~ u).
Proof.
move=> v1 v2 /(congr1 rev) /[!rev_cat] /catl_inj.
exact: (can_inj revK).
Qed.
End Compl.

Lemma cat_eq0 (T : eqType) (u v : seq T) :
  (u ++ v == [::]) = (u == [::]) && (v == [::]).
Proof. by case: u. Qed.
Lemma map_eq0 (T1 T2 : eqType) (u : seq T1) (f : T1 -> T2):
  (map f u == [::]) = (u == [::]).
Proof. by case: u. Qed.


Section LongestPrefix.

Context {Alph : eqType}.

Implicit Type (u v w : seq Alph).

Lemma prefix_drop_nil (u v : seq Alph) :
  prefix u v -> (u == v) = (drop (size u) v == [::]).
Proof.
case/prefixP=> w {v}->.
by rewrite -{1}(cats0 u) drop_size_cat // (inj_eq (@catl_inj _ u)) eq_sym.
Qed.

Lemma prefix_sizeE u v : prefix u v -> size u >= size v -> u = v.
Proof. by rewrite prefixE => /eqP {2}<- /take_oversize. Qed.

Lemma suffix_sizeE u v : suffix u v -> size u >= size v -> u = v.
Proof.
rewrite -prefix_rev => /prefix_sizeE; rewrite !size_rev => /[apply].
exact: (can_inj revK).
Qed.

Fixpoint long_cprefix u v :=
  if (u, v) is (u0 :: u', v0 :: v') then
    if u0 == v0 then u0 :: long_cprefix u' v'
    else [::]
  else [::].
Definition long_csuffix u v :=
  rev (long_cprefix (rev u) (rev v)).

Lemma long_cprefixC u v : long_cprefix u v = long_cprefix v u.
Proof.
elim: u v => [|u0 u IHu] [|v0 v] //=; rewrite {}IHu eq_sym.
by case: eqP => [->|].
Qed.

Lemma long_cprefixl u v : prefix (long_cprefix u v) u.
Proof.
elim: u v => [|u0 u IHu] [|v0 v] //=.
by case: eqP => [->|//]; rewrite eqxx IHu.
Qed.
Lemma long_cprefixr u v : prefix (long_cprefix u v) v.
Proof. by rewrite long_cprefixC long_cprefixl. Qed.
Lemma long_cprefixP u v w :
  prefix w u -> prefix w v -> prefix w (long_cprefix u v).
Proof.
elim: u v w => [|u0 u IHu] [|v0 v] [|w0 w] //=.
  by move=> _ _; exact: prefix0s.
case/andP => /eqP -> {}/IHu IH; case/andP => /eqP -> {}/IH /=.
by rewrite eqxx /= eqxx /=.
Qed.

Lemma long_csuffixC u v : long_csuffix u v = long_csuffix v u.
Proof. by rewrite /long_csuffix long_cprefixC. Qed.
Lemma long_csuffixl u v : suffix (long_csuffix u v) u.
Proof. by rewrite /long_csuffix suffix_revLR long_cprefixl. Qed.
Lemma long_csuffixr u v : suffix (long_csuffix u v) v.
Proof. by rewrite /long_csuffix suffix_revLR long_cprefixr. Qed.
Lemma long_csuffixP u v w :
  suffix w u -> suffix w v -> suffix w (long_csuffix u v).
Proof.
rewrite /long_csuffix -prefix_revLR => pru prv.
by apply: long_cprefixP; rewrite prefix_rev.
Qed.

End LongestPrefix.


Section Infixes.

Context {Alph : choiceType}.

Implicit Type (u v w : seq Alph).

Definition prefixes u := [seq take i u | i <- iota 0 (size u).+1].
Definition non_empty_prefixes u := behead (prefixes u).

Lemma head_prefixes x0 u : head x0 (prefixes u) = [::].
Proof. by rewrite -nth0 (nth_map 0) ?size_iota //= take0. Qed.

Lemma uniq_prefixes u : uniq (prefixes u).
Proof.
rewrite map_inj_in_uniq ?iota_uniq // => i j.
rewrite !mem_iota /= add0n !ltnS => lti ltj /(congr1 size).
by rewrite !size_take_min (minn_idPl lti) (minn_idPl ltj) => ->.
Qed.

Lemma non_empty_prefixes0 u : [::] \notin (non_empty_prefixes u).
Proof.
case: u => [// | u0 u].
rewrite /non_empty_prefixes /prefixes /=.
by apply/negP=> /mapP[/= [|i]]; rewrite mem_iota.
Qed.
Lemma prefixes_non_emtpyE u : prefixes u = [::] :: (non_empty_prefixes u).
Proof. by rewrite /non_empty_prefixes; case: u. Qed.

Lemma prefixesP u v : (prefix u v) = (u \in prefixes v).
Proof.
rewrite /prefixes; apply/prefixP/idP => [[w {v}->] | /mapP[i]].
- rewrite -{1}(take_size_cat w (erefl (size u))).
  apply: (map_f (fun i => take i (u ++ w))).
  by rewrite mem_iota /= add0n ltnS size_cat leq_addr.
- rewrite mem_iota /= add0n ltnS => leisz {u}->.
  by exists (drop i v); rewrite cat_take_drop.
Qed.
Lemma non_empty_prefixesP u v :
  ((u != [::]) && prefix u v) = (u \in non_empty_prefixes v).
Proof.
rewrite prefixesP prefixes_non_emtpyE.
by case: u => //=; rewrite (negbTE (non_empty_prefixes0 _)).
Qed.

Fixpoint infixes u :=
  prefixes u ++ if u is _ :: u' then behead (infixes u') else [::].
Definition non_empty_infixes u := behead (infixes u).

Lemma infixe0s u : [::] \in infixes u.
Proof. by case: u. Qed.
Lemma head_infixes x0 u : head x0 (infixes u) = [::].
Proof. by case: u. Qed.
Lemma infixes_cons (u0 : Alph) u :
  infixes (u0 :: u) = prefixes (u0 :: u) ++ behead (infixes u).
Proof. by []. Qed.

Lemma non_empty_infixes0 u : [::] \notin non_empty_infixes u.
Proof.
rewrite /non_empty_infixes; elim: u => [|u0 u IHu] //.
rewrite infixes_cons prefixes_non_emtpyE [non_empty_prefixes _]lock /=.
by unlock; rewrite mem_cat (negbTE (non_empty_prefixes0 _)) IHu.
Qed.

Lemma infixes_non_emtpyE u : infixes u = [::] :: (non_empty_infixes u).
Proof. by rewrite /non_empty_infixes; case: u. Qed.

Lemma infixesP u v : (infix u v) = (u \in infixes v).
Proof.
apply/infixP/idP => [[pre][suf] {v}-> | ].
- elim: pre => [| p0 p IHp].
    case: u => [| u0 u]; first exact: infixe0s.
    rewrite cat0s [_ ++ _]/= infixes_cons mem_cat /=.
    by rewrite -prefixesP /= eqxx /= prefix_prefix.
  rewrite [_ ++ _]/= infixes_cons mem_cat;
  move: IHp; rewrite infixes_non_emtpyE /=.
  by case: u => [|u0 u] //=; rewrite inE => /orP[/eqP// | ->] /[!orbT].
- elim: v u => [| v0 v IHv] u.
    by rewrite /= inE => /eqP ->; exists [::]; exists [::].
  case: u => [_ | u0 u]; first by exists [::]; exists (v0 :: v).
  rewrite infixes_cons mem_cat => /orP[{IHv} |].
    rewrite -prefixesP => /= /andP[/eqP {v0}<-] /prefixP[w {v}->].
    by exists [::]; exists w.
  move=> /mem_behead {}/IHv [pre][suf]{v}->.
  by exists (v0 :: pre); exists suf.
Qed.

Lemma non_empty_infixesP u v :
  ((u != [::]) && infix u v) = (u \in non_empty_infixes v).
Proof.
rewrite infixesP infixes_non_emtpyE.
by case: u => //=; rewrite (negbTE (non_empty_infixes0 _)).
Qed.

End Infixes.

