From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section LongestPrefix.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).

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

Section Factor.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

(* u is an factor of w *)
Fixpoint factor u w :=
  if w is w0 :: w' then prefix u w || factor u w' else u == [::].

Lemma factor0w w : factor [::] w.
Proof. by case: w. Qed.
Lemma factor_catl u v : factor u (u ++ v).
Proof.
elim: u => [|u0 u IHu] /=; first exact: factor0w.
by rewrite eqxx prefix_prefix.
Qed.
Lemma factorP u w :
  reflect (exists pre suf, w = pre ++ u ++ suf) (factor u w).
Proof.
apply (iffP idP).
- elim: w u => [| w0 w IHw] u.
    by case: u => [| u0 u] //= _; exists [::]; exists [::].
  move=>/orP[/prefixP[v ->] |]; first by exists [::]; exists v.
  move/IHw => [pre][suf] eq; exists (w0 :: pre); exists suf.
  by rewrite eq.
- elim: w u => [| w0 w IHw] u [pre][suf].
    move/(congr1 size); rewrite /= !size_cat addnC -addnA => /esym eq.
    by apply/eqP/nilP; rewrite /nilp -leqn0 -eq leq_addr.
  case: pre => [-> | p0 pre /= [_ eq]]; first by rewrite factor_catl.
  by apply/orP; right; apply IHw; exists pre; exists suf.
Qed.

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

Fixpoint factors u :=
  prefixes u ++ if u is _ :: u' then behead (factors u') else [::].
Definition non_empty_factors u := behead (factors u).

Lemma factor0s u : [::] \in factors u.
Proof. by case: u. Qed.
Lemma head_factors x0 u : head x0 (factors u) = [::].
Proof. by case: u. Qed.
Lemma factors_cons (u0 : Alph) u :
  factors (u0 :: u) = prefixes (u0 :: u) ++ behead (factors u).
Proof. by []. Qed.

Lemma non_empty_factors0 u : [::] \notin non_empty_factors u.
Proof.
rewrite /non_empty_factors; elim: u => [|u0 u IHu] //.
rewrite factors_cons prefixes_non_emtpyE [non_empty_prefixes _]lock /=.
by unlock; rewrite mem_cat (negbTE (non_empty_prefixes0 _)) IHu.
Qed.

Lemma factors_non_emtpyE u : factors u = [::] :: (non_empty_factors u).
Proof. by rewrite /non_empty_factors; case: u. Qed.

Lemma factorsP u v : (factor u v) = (u \in factors v).
Proof.
apply/factorP/idP => [[pre][suf] {v}-> | ].
- elim: pre => [| p0 p IHp].
    case: u => [| u0 u]; first exact: factor0s.
    rewrite cat0s [_ ++ _]/= factors_cons mem_cat /=.
    by rewrite -prefixesP /= eqxx /= prefix_prefix.
  rewrite [_ ++ _]/= factors_cons mem_cat;
  move: IHp; rewrite factors_non_emtpyE /=.
  by case: u => [|u0 u] //=; rewrite inE => /orP[/eqP// | ->] /[!orbT].
- elim: v u => [| v0 v IHv] u.
    by rewrite /= inE => /eqP ->; exists [::]; exists [::].
  case: u => [_ | u0 u]; first by exists [::]; exists (v0 :: v).
  rewrite factors_cons mem_cat => /orP[{IHv} |].
    rewrite -prefixesP => /= /andP[/eqP {v0}<-] /prefixP[w {v}->].
    by exists [::]; exists w.
  move=> /mem_behead {}/IHv [pre][suf]{v}->.
  by exists (v0 :: pre); exists suf.
Qed.

Lemma non_empty_factorsP u v :
  ((u != [::]) && factor u v) = (u \in non_empty_factors v).
Proof.
rewrite factorsP factors_non_emtpyE.
by case: u => //=; rewrite (negbTE (non_empty_factors0 _)).
Qed.

End Factor.

