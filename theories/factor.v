From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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

Lemma head_prefixes x0 u : head x0 (prefixes u) = [::].
Proof. by rewrite -nth0 (nth_map 0) ?size_iota //= take0. Qed.

Lemma uniq_prefixes u : uniq (prefixes u).
Proof.
rewrite map_inj_in_uniq ?iota_uniq // => i j.
rewrite !mem_iota /= add0n !ltnS => lti ltj /(congr1 size).
by rewrite !size_take_min (minn_idPl lti) (minn_idPl ltj) => ->.
Qed.

Lemma prefixesP u v : (prefix u v) = (u \in prefixes v).
Proof.
rewrite /prefixes; apply/prefixP/idP => [[w {v}->] | /mapP[i]].
- rewrite -{1}(take_size_cat w (erefl (size u))).
  apply: (map_f (fun i => take i (u ++ w))).
  by rewrite mem_iota /= add0n ltnS size_cat leq_addr.
- rewrite mem_iota /= add0n ltnS => leisz {u}->.
  by exists (drop i v); rewrite cat_take_drop.
Qed.

Fixpoint factors u :=
  prefixes u ++ if u is _ :: u' then behead (factors u') else [::].

Lemma factor0s u : [::] \in factors u.
Proof. by case: u. Qed.
Lemma head_factors x0 u : head x0 (factors u) = [::].
Proof. by case: u. Qed.
Lemma factors_cons (u0 : Alph) u :
  factors (u0 :: u) = prefixes (u0 :: u) ++ behead (factors u).
Proof. by []. Qed.

Lemma factorsP u v : (factor u v) = (u \in factors v).
Proof.
apply/factorP/idP => [[pre][suf] {v}-> | ].
- elim: pre => [| p0 p IHp].
    case: u => [| u0 u]; first exact: factor0s.
    rewrite cat0s [_ ++ _]/= factors_cons mem_cat /=.
    by rewrite -prefixesP /= eqxx /= prefix_prefix.
  rewrite [_ ++ _]/= factors_cons mem_cat. IHp orbT.

    by rewrite [_ ++ _]/= factors_cons mem_cat IHp orbT.
- elim: v u => [| v0 v IHv] u.
    by rewrite /= inE => /eqP ->; exists [::]; exists [::].
  case: u => [_ | u0 u]; first by exists [::]; exists (v0 :: v).
  rewrite factors_cons mem_cat => /orP[{IHv} | {}/IHv[pre][suf]{v}->].
    rewrite -prefixesP => /= /andP[/eqP {v0}<-] /prefixP[w {v}->].
    by exists [::]; exists w.
  by exists (v0 :: pre); exists suf.
Qed.



(*
Definition non_empty_factors u :=
  [seq drop i (take j u) | j <- iota 0 (size u).+1,
    i <- iota 0 j].
 *)

Lemma non_empty_factorsP w u :
  reflect (u != [::] /\ factor w u)
    (u \in non_empty_factors w).
Proof.
apply (iffP idP).
- elim: w u => [| w0 w IHw] //= u.
    rewrite mem_cat inE => /or3P[].
    + move/IHw => [un0 [pre suf ->]]; split => //.
      by exists (w0 :: pre) suf.
    + move/eqP ->; split => //.
      by exists [::] w.
    + case: u => [| u0 u] /mapP[] //= v {}/IHw[vn0 [pre suf {w}->]].
      move=> [{u0}-> {u}->]; split => //.
      exosts 

      elim/last_ind: w u => [| w wl IHw] u.
    by rewrite /non_empty_factors //.
  rewrite /non_empty_factors size_rcons.
  admit.
Admitted.
