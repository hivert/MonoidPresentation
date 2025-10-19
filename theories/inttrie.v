(** * Trie for seq int using primitive arrays *)
(******************************************************************************)
(*      Copyright (C) 2025      Florent Hivert <florent.hivert@lri.fr>        *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
From HB Require Import structures.
From Stdlib Require Import Znat BinIntDef Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot all_order.


(* Workaround for MathComp / PArray notation incompatibilities *)
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").
Notation "t .[ i ]" := (get t i).
Notation "t .[ i <- a ]" := (set t i a).

Require Import factor int_seq present fastcert enumnf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope uint63_scope.


Local Notation wBnat := (BinInt.Z.to_nat wB).


Lemma lt_lenght_wB (T : Type) (a : array T) : to_nat (length a) < wBnat.
Proof.
have /leq_ltn_trans : to_nat (length a) <= to_nat max_length.
  by rewrite -leEint; exact: leb_length.
by apply; apply/ltP/Z2Nat.inj_lt.
Qed.


(** Data structure for tries *)
Section Defs.

Context {T : eqType} (trielen : int).

Unset Elimination Schemes.
Inductive trie := Empty | Trie : option T -> array trie -> trie.
Set Elimination Schemes.

Definition isEmpty t := if t is Empty then true else false.
Lemma isEmptyP t : reflect (t = Empty) (isEmpty t).
Proof. by case: t => [| x a] /=; apply (iffP idP). Qed.

(** Induction scheme for tries *)
Section Recursion.

Variables (P : trie -> Type).
Hypothesis HEmpty : P Empty.
Hypothesis IHtrie :
  forall a : array trie,
    P (default a) -> (forall i : int, (i < length a)%O -> P a.[i]) ->
             forall x, P (Trie x a).

Fixpoint rectrie t : P t :=
  if t is Trie x a
  then IHtrie (rectrie (default a)) (fun i _ => rectrie a.[i]) x
  else HEmpty.

End Recursion.
Definition indtrie (P : trie -> Prop) := @rectrie P.


(** eqType structure for tries *)
Definition eq_trarray (eqtrie : trie -> trie -> bool) (a b : array trie) :=
  [&& length a == length b,
    eqtrie (default a) (default b) &
      all (fun i => eqtrie a.[(of_nat i)] b.[(of_nat i)])
        (iota 0 (to_nat (length a)))].
Fixpoint eq_trie s t : bool :=
  match s, t with
  | Trie u a, Trie v b => (u == v) && eq_trarray eq_trie a b
  | Empty, Empty => true
  | _, _ => false
  end.

Lemma eqtrie_subproof : Equality.axiom eq_trie.
Proof.
move=> s t; apply (iffP idP) => [|{s}->].
  elim/rectrie: s t => [[] //|a IHdef IHa] x [//| y] b /= /andP[/eqP {y}<-].
  rewrite /eq_trarray => /and3P[/eqP eqlen {}/IHdef eqdef /allP /= eq].
  congr Trie; apply: array_ext => // i /[dup] {}/IHa Hrec ltil.
  apply: Hrec; rewrite -(to_natK i); apply: eq.
  by rewrite mem_iota /= add0n -ltEint; exact: ltil.
elim/rectrie: t => [//| a IHdef IHa] x; rewrite /= eqxx {x} /=.
rewrite /eq_trarray !eqxx {}IHdef /=.
apply/allP => /= n; rewrite mem_iota /= add0n => ltn.
apply: IHa; rewrite ltEint of_natK //.
move/leq_trans: ltn; apply.
have /leq_trans: to_nat (length a) <= to_nat max_length.
  by rewrite -leEint; exact: leb_length.
by apply; apply/leP; rewrite -Z2Nat.inj_le.
Qed.
HB.instance Definition _ := hasDecEq.Build trie eqtrie_subproof.


Hypothesis (le_trielen : (0 < trielen <= max_length)%O).
Lemma lt0len : 0 <? trielen.
Proof. by case/andP: le_trielen. Qed.
Lemma len_neq0 : trielen != 0.
Proof.
case/andP: le_trielen => /[swap] _.
by apply/contraL => /eqP ->; rewrite Order.POrderTheory.ltxx.
Qed.
Lemma lelenmax : trielen ≤? max_length.
Proof. by case/andP: le_trielen => _. Qed.
Lemma length_make_trielen :
  length (make trielen Empty) = trielen.
Proof. by rewrite length_make lelenmax. Qed.

(** ** Fixed length arrays and tries *)
(** Either a is not allocated of length 0 or of length trielen *)
Definition flarray_tr (istrie : trie -> bool) (a : array trie) :=
  [&& (length a == 0) || (length a == trielen), isEmpty (default a) &
    all (fun i => istrie a.[(of_nat i)]) (iota 0 (to_nat trielen))].
Fixpoint is_fltrie t : bool :=
  if t is Trie v a then flarray_tr is_fltrie a else true.
Notation flarray := (flarray_tr is_fltrie).

Lemma flarrayP (istrie : trie -> bool) (a : array trie) :
  reflect [/\ length a = 0 \/ length a = trielen,
      default a = Empty &
        forall i, (i < trielen)%O -> istrie a.[i]] (flarray_tr istrie a).
Proof.
apply (iffP and3P) => [[ /orP eqlen def0 /allP] | [eqlen def0]] /= trienth.
- split => //; first by case: eqlen => [] /eqP ->; [left| right].
    by case: (default a) def0.
  move=> i ltisz; rewrite -(to_natK i); apply: trienth.
  by rewrite mem_iota /= add0n -ltEint.
- split; first by case: eqlen => ->; rewrite eqxx // orbT.
    by case: (default a) def0.
  apply/allP => n; rewrite mem_iota /= add0n => ltnsz.
  have /of_natK eqn : n < wBnat.
    apply: (ltn_trans ltnsz); apply/ltP; rewrite -Z2Nat.inj_lt; last by [].
    * by case/andP: le_trielen => _ /lebP/(BinInt.Z.le_lt_trans _); apply.
    * by rewrite -to_Z_0; apply/lebP; apply: le0int.
  by move: ltnsz; rewrite -{1}eqn -ltEint => /trienth.
Qed.

Structure fltrie : Type := FLTrie {trval :> trie; _ : is_fltrie trval}.
HB.instance Definition _ := [isSub for trval].
HB.instance Definition _ := [Equality of fltrie by <:].


Implicit Types (t : trie) (e f : T) (x y : option T) (v w : seq int).


Lemma fltrieP (t : fltrie) : is_fltrie t.
Proof. by case: t. Qed.
Hint Resolve fltrieP : core.

Definition mkfltrie (t : fltrie) mktrie : fltrie :=
  mktrie (let: FLTrie _ tP := t return is_fltrie t in tP).
Lemma mkfltrieE (t : fltrie) : mkfltrie (fun sP => @FLTrie t sP) = t.
Proof. by case: t. Qed.
Notation "[ 'fltrie' 'of' s ]" := (mkfltrie (fun sP => @FLTrie s sP))
  (at level 0, format "[ 'fltrie'  'of'  s ]") : form_scope.

Lemma is_fltrie_empty : is_fltrie Empty.
Proof. by []. Qed.
Canonical flEmpty := FLTrie is_fltrie_empty.
Hint Resolve is_fltrie_empty : core.


(** Update the trie t at node v with upd                         *)
(** None means nothing is stored both in input and output of upd *)
Fixpoint updatetrie t v (upd : option T -> option T) :=
  if v is v0 :: v' then
    let: (x, a, sub) := if t is Trie x a then
                          if length a == 0 then (x, make trielen Empty, Empty)
                          else (x, a, a.[v0])
                   else (None, make trielen Empty, Empty)
    in Trie x a.[v0 <- updatetrie sub v' upd]
  else
    let: (x, a) := if t is Trie x a then (x, a)
                   else (None, make 0 Empty)
    in Trie (upd x) a.

Definition addtrie t v e := updatetrie t v (fun => Some e).
Definition deltrie t v := updatetrie t v (fun => None).

(** The subtrie of t at node v *)
Fixpoint getsubtrie t v :=
  match v, t with
  | v0 :: v', Trie x a => getsubtrie a.[v0] v'
  | [::], t => t
  | _, _  => Empty
  end.
(** The value of t at node v *)
Definition gettrie t v := if getsubtrie t v is Trie x a then x else None.

Lemma get_empty i : [| | Empty : trie |].[i] = Empty.
Proof. by rewrite get_out_of_bounds //= ltEintb ltn0. Qed.

Lemma flarray_make0 : flarray (make 0 Empty).
Proof.
apply/flarrayP; split.
- by rewrite length_make; left.
- by rewrite default_make.
- by move=> i _ /=; rewrite get_empty.
Qed.

Lemma flarray_make : flarray (make trielen Empty).
Proof.
apply/flarrayP; split.
- by rewrite length_make_trielen; right.
- by rewrite default_make.
- by move=> /= i lti; rewrite get_make.
Qed.
Lemma fltrie_get a i : flarray a -> is_fltrie a.[i].
Proof.
move/flarrayP => [lena defa /= flt].
case: (boolP (i < trielen)%O) => [| /negbTE H]; first exact: flt.
rewrite get_out_of_bounds ?defa //=; case: lena => [] -> //.
by rewrite ltEintb.
Qed.
Lemma flarray_set a i t :
  flarray a -> is_fltrie t -> flarray a.[i <- t].
Proof.
case/flarrayP => [lena defa /= flta] flt.
apply/flarrayP; split.
- by case: lena => lena; [left | right]; rewrite length_set.
- by rewrite default_set.
- move=> /= j ltj; case: (altP (i =P j)) => [{i}->|/eqP ineqj].
    case: lena => lena; last by rewrite get_set_same // lena.
    rewrite get_out_of_bounds ?default_set ?defa //.
    by rewrite length_set lena ltEintb.
  by rewrite get_set_other // flta.
Qed.

Lemma is_fltrie_updatetrie t v upd :
  is_fltrie t -> is_fltrie (updatetrie t v upd).
Proof.
elim: v t => [|v0 v IHv] [_ |x a] //=; first exact: flarray_make0.
  by apply: flarray_set; [exact: flarray_make | exact: IHv].
move=> /[dup] fla /flarrayP[+ _ _]; case => -> /=.
  by apply: flarray_set; [exact: flarray_make | exact: IHv].
rewrite (negbTE len_neq0) /=.
by apply: flarray_set => //; apply: IHv; apply: fltrie_get.
Qed.
Canonical updatefltrie (t : fltrie) v upd :=
  FLTrie (is_fltrie_updatetrie v upd (fltrieP t)).

Lemma is_fltrie_getsubtrie t v : is_fltrie t -> is_fltrie (getsubtrie t v).
Proof.
by elim: v t => [|v0 v IHv] [_ |x a] //= fla; apply: IHv; apply: fltrie_get.
Qed.
Canonical getsubfltrie (t : fltrie) v :=
  FLTrie (is_fltrie_getsubtrie v (fltrieP t)).

Lemma getsub_updatetrie t v upd w :
  is_fltrie t ->
  all (<%O^~ trielen)%O v ->
  getsubtrie (updatetrie t v upd) w =
    if prefix w v then
      updatetrie (getsubtrie t w) (drop (size w) v) upd else getsubtrie t w.
Proof.
(* Note refactoring leads to a too complicated step lemma *)
rewrite /gettrie /=.
elim: w v t => [| w0 w IHw] [|v0 v] [|x t] //=.
- by move => _ _; case: eqP => //=.
- by move=> _ _; rewrite get_empty; case w.
- move=> _; case/andP=> [ltv0 {}/IHw Hrec].
  (* Duplication here *)
  case: eqP => /= [{w0}-> | neq].
    rewrite get_set_same; last by rewrite length_make_trielen.
    by rewrite {}Hrec /=; case: (w == v) => /=; case w.
  by rewrite (get_set_other _ _ _ _ _ (not_eq_sym neq)) get_make /=; case w.
- case/flarrayP => eqlen eqdef /= fltrec.
  case/andP=> [ltv0 {}/IHw Hrec].
  case: eqlen => [len0 | leneq] /=.
    rewrite len0 /= [t.[w0]]get_out_of_bounds; first last.
      by rewrite len0 ltEintb.
    (* Duplication here *)
    case: eqP => /= [{w0}-> | neq] /=.
      rewrite get_set_same; last by rewrite length_make_trielen; exact: ltv0.
      by rewrite -Hrec eqdef.
    rewrite (get_set_other _ _ _ _ _ (not_eq_sym neq)) get_make /= eqdef.
    by case w.
  rewrite leneq (negbTE len_neq0).
  (* Duplication here *)
  case: eqP => /= [{w0}-> | neq].
    rewrite get_set_same; last by rewrite leneq; exact: ltv0.
    by move/(_ _ ltv0): fltrec => /Hrec.
  by rewrite (get_set_other _ _ _ _ _ (not_eq_sym neq)).
Qed.

Lemma updatetrie_comp t v u1 u2 :
  updatetrie t v (u1 \o u2) = updatetrie (updatetrie t v u2) v u1.
Proof.
have step x a u0 u :
  (forall t, updatetrie t u (u1 \o u2) = updatetrie (updatetrie t u u2) u u1) ->
    Trie x a.[u0<-updatetrie a.[u0] u (u1 \o u2)] =
    Trie x a.[u0<-updatetrie a.[u0] u u2].[
        u0<-updatetrie a.[u0<-updatetrie a.[u0] u u2].[u0] u u1].
  move=> IH; congr Trie.
  apply: array_ext => [|i|]; last 1 first.
  + by rewrite !default_set.
  + by rewrite !length_set.
  rewrite !length_set.
  case: (altP (u0 =P i)) => [{i}<- | /eqP neqv0i] lti.
    by rewrite ?get_set_same ?lena // length_set.
  by rewrite !get_set_other.
elim: v t => [| v0 v IHv] [|x] //=.
  rewrite length_set length_make_trielen (negbTE len_neq0).
  have:= step None (make trielen Empty) v0 v IHv.
  by rewrite !get_make.
move=> a; case: eqP => /= [lena | /eqP lena].
  rewrite length_set length_make_trielen (negbTE len_neq0).
  have:= step x (make trielen Empty) v0 v IHv.
  by rewrite !get_make.
rewrite length_set (negbTE lena).
exact: step.
Qed.


Local Lemma updatetrieC_step x a (v0 w0 : int) v w u1 u2 :
  v0 :: v != w0 :: w ->
  (forall t w', v != w' ->
   updatetrie (updatetrie t v u1) w' u2 = updatetrie (updatetrie t w' u2) v u1) ->
  Trie x a.[v0 <- updatetrie a.[v0] v u1].[
      w0 <- updatetrie a.[v0<-updatetrie a.[v0] v u1].[w0] w u2] =
  Trie x a.[w0 <- updatetrie a.[w0] w u2].[
      v0<-updatetrie a.[w0 <- updatetrie a.[w0] w u2].[v0] v u1].
Proof.
move=> neq IH; congr Trie.
apply: array_ext => [|i|].
- by rewrite !length_set.
- rewrite !length_set.
  case: (altP (v0 =P i)) => [{i}<- | /eqP neqv0i] lti.
    rewrite ?get_set_same ?length_make_trielen //; first last.
      by rewrite length_set.
    case: (altP (w0 =P v0)) => [eqv0w0 | /eqP neqv0w0].
      subst w0; rewrite ?get_set_same ?length_make_trielen //.
        by apply IH => //; move: neq; apply contra => /eqP ->.
      by rewrite length_set.
    rewrite get_set_other // get_set_same ?length_make_trielen //.
    by rewrite get_set_other // get_make.
  rewrite (get_set_other _ _ v0 i) //.
  case: (altP (w0 =P v0)) => [eqv0w0 | /eqP neqv0w0].
    by subst w0; rewrite !get_set_other.
  case: (altP (w0 =P i)) => [eq1 | /eqP neqw0i].
    subst w0; rewrite (get_set_other _ _ v0 i) //.
    by rewrite !get_set_same ?length_set ?length_make_trielen // get_make.
  by rewrite !get_set_other.
- by rewrite !default_set.
Qed.

Lemma updatetrieC t v w u1 u2 :
  v != w ->
  updatetrie (updatetrie t v u1) w u2 = updatetrie (updatetrie t w u2) v u1.
Proof.
elim: v t w => [| v0 v IHv] [|x a] [|w0 w] //=.
- by move=> _; case: eqP.
- move=> neq.
  rewrite !length_set length_make_trielen (negbTE len_neq0).
  have:= updatetrieC_step None (make trielen Empty) neq IHv.
  by rewrite !get_make.
- by move=> _; case: eqP.
- move=> neq; case: eqP => [lena | /eqP/negbTE lena].
    rewrite !length_set length_make_trielen (negbTE len_neq0).
    have:= updatetrieC_step x (make trielen Empty) neq IHv.
    by rewrite !get_make.
  rewrite !length_set lena.
  exact: updatetrieC_step.
Qed.


Lemma get_updatetrie t v upd w :
  is_fltrie t ->
  all (<%O^~ trielen)%O v ->
  gettrie (updatetrie t v upd) w =
    if w == v then upd (gettrie t w) else gettrie t w.
Proof.
rewrite /gettrie /= => /getsub_updatetrie/[apply] ->.
case: (boolP (prefix w v)) => [| npref]; first last.
  suff /negbTE -> : w != v by [].
  by apply/contra: npref => /eqP ->; rewrite prefix_refl.
move/prefixP => [/= suf {v}->]; rewrite drop_size_cat //.
case: suf => [| s0 s] /=.
  by rewrite cats0 eqxx; case: (getsubtrie t w).
have /negbTE -> : w != w ++ s0 :: s.
  apply/negP => /eqP/(congr1 size)/eqP.
  by rewrite size_cat /= addnS ltn_eqF // ltnS leq_addr.
by case: (getsubtrie t w) => // r a; case: eqP.
Qed.
Definition get_updatefltrie (t : fltrie) v upd w :=
  get_updatetrie (v := v) upd w (fltrieP t).


(** Given a trie `t` and a word `w`, search for the shortest prefix of `w` *)
(** that index a non empty node of `t`. If found, return `Some (e, v)`     *)
(** where `e` is the value and `v` is the suffix of the remaining letters  *)
(** of `w`. If not found, return `None`                                    *)
Fixpoint getprefixtrie t w :=
  match t, w with
  | Trie (Some e) a, _ => Some (e, w)
  | Trie None a, w0 :: w' => getprefixtrie a.[w0] w'
  | _, _ => None
  end.
(** Specification of getprefixtrie *)
Variant getprefixtrie_spec t w : option (T * seq int) -> Type :=
  | PrefixNotFound of (forall v, prefix v w -> gettrie t v = None) :
    getprefixtrie_spec t w None
  | PrefixFound e v1 v2 of (w = v1 ++ v2) & (gettrie t v1 = Some e)
    & (forall v', prefix v' v1 -> v' != v1 -> gettrie t v' = None) :
    getprefixtrie_spec t w (Some (e, v2)).

Lemma getprefixtrieP t w : getprefixtrie_spec t w (getprefixtrie t w).
Proof.
elim: w t => [|w0 w IHw] /=.
  case=> [|x a] /=; first by apply: PrefixNotFound => [[]].
  case: x => [e|]; last by apply: PrefixNotFound => [[]].
  by apply: (PrefixFound (v1 := [::]) (v2 := [::])) => // [[]].
case=> [|s a] /=; first by apply: PrefixNotFound => [[]].
case: s => [e|] /=.
  by apply: (PrefixFound (v1 := [::]) (v2 := (w0 :: w))) => // [[]].
case/IHw: a.[w0] => [minpref | e pre suf eqcat getpre minpre] {IHw}/=.
  by apply: PrefixNotFound => [[]] //= v0 v /andP[/eqP {v0}-> /minpref].
apply: (PrefixFound (v1 := w0 :: pre) (v2 := suf)) => //=.
  by rewrite eqcat.
case=> // v0 v /= /andP[/eqP {v0}-> {}/minpre Hmin].
by rewrite eqseq_cons eqxx /=.
Qed.

End Defs.


(** Rewriting and normal forms using trie            *)
(* Could be made even faster with a Gilman automaton *)
Section TrieRewrites.

Variable trielen : int.
Hypothesis (maxlen : (0 < trielen <= max_length)%O).

Definition rewtrie := @trie (word int).

Implicit Type (R : relat int) (t : rewtrie) (u v w : seq int).


Definition addpair p (t : rewtrie) := addtrie trielen t p.1 p.2.
Definition mktrie := foldr addpair Empty.
Definition trie_rewrites1_front (t : rewtrie) w :=
  omap (fun p => p.1 ++ p.2) (getprefixtrie t w).


Lemma is_flmktrie R : is_fltrie trielen (mktrie R).
Proof.
elim : R => [// | [r1 r2] R IHR] /=.
by rewrite /addpair /=; exact: (is_fltrie_updatetrie maxlen _ _ IHR).
Qed.
Canonical flmktrie R := FLTrie (is_flmktrie R).

Lemma trie_rewrites1_front0 R w :
  all_relwords R (<%O^~ trielen) ->
  trie_rewrites1_front (mktrie R) w = None -> rewrites_front R w = [::].
Proof.
rewrite /trie_rewrites1_front /mktrie /all_relwords => /= corr.
case: getprefixtrieP => // Hpref _.
elim: R corr Hpref => [// | [/= r1 r2 R IHR]].
case/andP => /andP[allr1 allr2] {}/IHR Hrec Hget.
case: (boolP (prefix r1 w)) => Hpref.
  exfalso; move/(_ _ Hpref): Hget => /=.
  rewrite get_updatetrie //=; last exact: is_flmktrie.
  by rewrite eqxx.
apply: Hrec => v {}/Hget.
rewrite get_updatetrie //=; last exact: is_flmktrie.
by case: eqP.
Qed.

Lemma getprefixmktrieE R w :
  all_relwords R (<%O^~ trielen) ->
  forall u v : word int, getprefixtrie (mktrie R) w = Some (u, v) ->
         u ++ v \in rewrites_front R w.
Proof.
rewrite /mktrie /all_relwords => /= corr.
case: getprefixtrieP => // res => v1 v2 {w}-> eqres Hpref u v [{u}<- {v}<-].
suff {v2} : res \in rewrites_front R v1.
  case/rewrites_frontP => /= suf [r1 r2] /= {eqres Hpref v1}-> {res}-> rinP.
  by apply/rewrites_frontP; exists (suf ++ v2) (r1, r2) => //= /[!catA].
elim: R corr eqres Hpref => [| [/= r1 r2 R IHR]]/=; first by case: v1.
case/andP => /andP[allr1 allr2] {}/IHR Hrec found getpref.
case: (boolP (prefix r1 v1)) => [Hpref| npref].
  case: (altP (r1 =P v1)) => [eqr1 {Hpref} |].
    subst r1; move: found.
    rewrite get_updatetrie //= ?eqxx => [[<-]|]; last exact: is_flmktrie.
    by rewrite inE drop_size cats0 eqxx.
  move=> /(getpref _ Hpref).
  by rewrite get_updatetrie //= ?eqxx => [//|]; last exact: is_flmktrie.
have {npref} neqr1v1 : r1 != v1 by case: eqP npref => // ->; rewrite prefix_refl.
move: found; rewrite get_updatetrie //=; last exact: is_flmktrie.
rewrite eq_sym (negbTE neqr1v1) => Hget.
apply: Hrec => // v /getpref/[apply].
rewrite get_updatetrie //=; last exact: is_flmktrie.
by case: eqP.
Qed.

Lemma trie_rewrites1_frontP R :
  all_relwords R (<%O^~ trielen) ->
  rewrites1_front_Ok R (trie_rewrites1_front (mktrie R)).
Proof.
move=> Hcorr w; rewrite /trie_rewrites1_front /=.
case H : (getprefixtrie (mktrie R) w) => [[v1 v2]|]/=; constructor.
  exact: getprefixmktrieE.
rewrite (trie_rewrites1_front0 Hcorr) => //.
by rewrite /trie_rewrites1_front /= H.
Qed.

Definition trie_rewrites1 t :=
  rewrites1_from_front (trie_rewrites1_front t).

Lemma trie_rewrites1P R :
  all_relwords R (<%O^~ trielen) -> rewrites1_Ok R (trie_rewrites1 (mktrie R)).
Proof. by move/trie_rewrites1_frontP => H; apply:rewrite1_from_frontP. Qed.


Definition eqnor tr fuel (p1 p2 : word int) :=
  let x1 := norfuel2 (trie_rewrites1 tr) fuel p1 in
  let x2 := norfuel2 (trie_rewrites1 tr) fuel p2 in
  eqseq_int x1.1 x2.1.


Definition spair_confluence_dec_trie R fuel :=
  let tr := mktrie R in
  if all_tr (fun p => eqseq_int p.1 p.2) (all_npairs_int R) then
    let spairs := filter_rev_tr
                    (fun p => ~~ eqseq_int p.1 p.2) (all_spairs_int R) in
    (* all (fun p => norfuel_int R fuel p.1 == norfuel_int R fuel p.2) spairs *)
    all_tr (fun p => eqnor tr fuel p.1 p.2) spairs
  else false.
Lemma spair_confluence_dec_intE R :
  spair_confluence_dec R (trie_rewrites1 (mktrie R)) = spair_confluence_dec_trie R.
Proof. by []. Qed.

Definition spair_confluence_loop_trie R fuel :=
  let tr := (mktrie R) in
  (all_pred_npairs_int eqseq_int R) &&
  (all_pred_spairs_int (fun p1 p2 =>
     if eqseq_int p1 p2 then true else eqnor tr fuel p1 p2) R).

Lemma spair_confluence_loop_trieE R :
  spair_confluence_loop R (trie_rewrites1 (mktrie R)) =
    spair_confluence_loop_trie R.
Proof. by []. Qed.

End TrieRewrites.


(** Ensuring that the tries have a sufficiently large enough length *)
(** to deal with a presentation `P`.                                *)
Section Size.

Variable P : pres int.

Lemma pgen_size sz :
  all (<%O^~ sz) (pgen P) -> all_relwords (prelat P) (<%O^~ sz).
Proof.
move=> /allP /= H.
have /sub_all {}H : subpred (mem (pgen P)) (<%O^~ sz) by move=> i /H.
apply/allP => /= [[r1 r2] /=].
have /allP /= /[apply] /= := wf_relat P.
by move/andP=> [/H -> /H ->].
Qed.

Definition pres_trielen := foldl max 0 (pgen P) + 1.

Hypothesis pgenOk : all (<%O^~ max_length) (pgen P).

Local Lemma foldlmaxlt : (foldl max 0 (pgen P) < max_length)%O.
Proof.
have : (0 < max_length)%O by [].
elim: (pgen P) (0) pgenOk => [|g0 g IHg] //= i /[swap] lti.
case/andP => ltg0 {}/IHg; apply.
by rewrite ltEint maxEint gtn_max -!ltEint lti ltg0.
Qed.

Lemma pgen_maxlen : (0 < pres_trielen <= max_length)%O.
Proof.
have foldlmaxlt : (foldl max 0 (pgen P) < max_length)%O.
  have : (0 < max_length)%O by [].
  elim: (pgen P) (0) pgenOk => [|g0 g IHg] //= i /[swap] lti.
  case/andP => ltg0 {}/IHg; apply.
  by rewrite ltEint maxEint gtn_max -!ltEint lti ltg0.
apply/andP; split; first last.
  by rewrite /pres_trielen; apply ltleSint; exact: foldlmaxlt.
rewrite /pres_trielen ltEint to_nat0 to_natD; first by rewrite addnS ltnS.
rewrite addn1.
move: foldlmaxlt; rewrite ltEint => /leq_ltn_trans; apply.
by apply/ltP; rewrite -Z2Nat.inj_lt.
Qed.

Lemma pgen_trielen :
  all (<%O^~ max_length) (pgen P) -> all (<%O^~ pres_trielen) (pgen P).
Proof.
rewrite /pres_trielen.
have : (0 < max_length)%O by [].
elim: (pgen P) (0) => // [g0 g IHg] /= i lti.
case/andP => ltg0 alllt; apply/andP; split; first last.
  by apply: IHg => //; rewrite ltEint maxEint gtn_max -!ltEint lti ltg0.
elim: g alllt {IHg} i lti g0 ltg0 => [| g1 g IHg] /=.
  move=> _ i lti g ltg; rewrite ltEint to_natD to_nat1 addn1 maxEint.
    by rewrite ltnS leq_maxr.
  apply: (leq_trans (n := (to_nat max_length).+1)).
    by rewrite ltnS gtn_max -!ltEint lti ltg.
  by apply/ltP; rewrite -Z2Nat.inj_lt.
case/andP => [ltg1 alllt] i lti g0 ltg0.
have -> : max (max i g0) g1 = max (max i g1) g0.
  apply: to_nat_inj.
  rewrite [LHS]maxEint [in LHS]maxEint [RHS]maxEint [in RHS]maxEint.
  by rewrite -!maxnA [maxn (to_nat g1) _]maxnC.
apply: IHg => //=.
by rewrite ltEint maxEint gtn_max -!ltEint lti ltg1.
Qed.

Lemma corrrelat_trielen : all_relwords (prelat P) (<%O^~ pres_trielen).
Proof. exact/pgen_size/pgen_trielen. Qed.

Definition spair_confluence_loop_trieP :=
  spair_confluence_loopP (trie_rewrites1P pgen_maxlen corrrelat_trielen).

End Size.


(** Enumeration of normal forms using tries *)
Section EnumNormalForms.

Variable (P : pres int) (trielen : int).
Hypothesis convP : convergent P.
Hypothesis genPlen : all (<%O^~ max_length) (pgen P).

Implicit Types (u v w : word int) (norf : seq (word int)).

Let Ptrie := mktrie (pres_trielen P) (prelat P).
Let rew1P : rewrites1_Ok P (trie_rewrites1 Ptrie)
    := trie_rewrites1P (pgen_maxlen genPlen) (corrrelat_trielen genPlen).

Definition enum_normal_next_trie := enum_normal_next P (trie_rewrites1 Ptrie).
Definition enum_normal_trie_sz := enum_normal_sz P (trie_rewrites1 Ptrie).
Definition enum_normal_trie := enum_normal P (trie_rewrites1 Ptrie).

Lemma normal_sz_enum_normal_trie_sz n : all (normal_sz P n) (enum_normal_trie_sz n).
Proof. exact: normal_sz_enum_normal_sz. Qed.

Lemma count_mem_enum_normal_trie_sz n u :
  normal_sz P n u -> count_mem u (enum_normal_trie_sz n) = 1%N.
Proof. exact: count_mem_enum_normal_sz. Qed.

Lemma uniq_enum_normal_trie_sz n : uniq (enum_normal_trie_sz n).
Proof. exact: uniq_enum_normal_sz. Qed.

Lemma mem_enum_normal_trie_szP n u :
  (u \in enum_normal_trie_sz n) = normal_sz P n u.
Proof. exact: mem_enum_normalP. Qed.

Lemma enum_normal_trieP bound :
  let: (l, ok) := enum_normal_trie bound in ok -> is_enum_normal P l.
Proof. exact: enum_normalP. Qed.

End EnumNormalForms.


(** ** An example *)
Require Import rewcert sizelexi.

Module Example.

Definition P := make_pres [::0; 1]
  [::
   ([::1;0], [::0;1]);
   ([::0;0;0], [::0;1]);
   ([::1;1], [::1])
  ].

Theorem final_ok : convergent P.
Proof.
apply: diamond.
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
have pgenOk : all (<%O^~ max_length) (pgen P) by [].
apply: (spair_confluence_loop_trieP pgenOk (fuel := 10)).
rewrite spair_confluence_loop_trieE.
by native_cast_no_check is_true_true.
Qed.

Definition nf := [:: [::]; [:: 0]; [:: 1]; [:: 0; 0]; [:: 0; 1]; [:: 0; 0; 1]].

Lemma is_enum_normal_nf : is_enum_normal P nf.
Proof. exact: (@enum_normal_trieP _ final_ok _ 5 _). Qed.

End Example.
