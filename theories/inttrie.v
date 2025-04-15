From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63 PArray.
From mathcomp Require Import all_ssreflect.

Require Import int_seq present fastcert enumnf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope uint63_scope.


Local Notation wBnat := (BinInt.Z.to_nat wB).


Lemma lt_lenght_wB (T : Type) (a : array T) : to_nat (length a) < wBnat.
Proof.
have /leq_ltn_trans : to_nat (length a) <= to_nat max_length.
  by rewrite -leintE; exact: leb_length.
by apply; apply/ltP/Z2Nat.inj_lt.
Qed.


Fixpoint loop {A : Type} (cnt : nat) (i : int) (f : A -> int -> A) (init : A) : A :=
    match cnt with
    | O => init
    | cnt'.+1 => loop cnt' (i + 1) f (f init i)
    end.


Section Defs.

Context {T : eqType} (trielen : int).

Unset Elimination Schemes.
Inductive trie := Empty | Trie : option T -> array trie -> trie.
Set Elimination Schemes.

Definition isEmpty t := if t is Empty then true else false.
Lemma isEmptyP t : reflect (t = Empty) (isEmpty t).
Proof. by case: t => [| x a] /=; apply (iffP idP). Qed.

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

Lemma eqtrieP : Equality.axiom eq_trie.
Proof.
move=> s t; apply (iffP idP) => [|{s}->].
  elim/rectrie: s t => [[] //|a IHdef IHa] x [//| y] b /= /andP[/eqP {y}<-].
  rewrite /eq_trarray => /and3P[/eqP eqlen {}/IHdef eqdef /allP /= eq].
  congr Trie; apply: array_ext => // i /[dup] {}/IHa Hrec ltil.
  apply: Hrec; rewrite -(to_natK i); apply: eq.
  by rewrite mem_iota /= add0n -ltintE; exact: ltil.
elim/rectrie: t => [//| a IHdef IHa] x; rewrite /= eqxx {x} /=.
rewrite /eq_trarray !eqxx {}IHdef /=.
apply/allP => /= n; rewrite mem_iota /= add0n => ltn.
apply: IHa; rewrite ltintE of_natK //.
move/leq_trans: ltn; apply.
have /leq_trans: to_nat (length a) <= to_nat max_length.
  by rewrite -leintE; exact: leb_length.
by apply; apply/leP; rewrite -Z2Nat.inj_le.
Qed.
HB.instance Definition _ := hasDecEq.Build trie eqtrieP.


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

(* Fixed length arrays and tries *)
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
  by rewrite mem_iota /= add0n -ltintE.
- split; first by case: eqlen => ->; rewrite eqxx // orbT.
    by case: (default a) def0.
  apply/allP => n; rewrite mem_iota /= add0n => ltnsz.
  have /of_natK eqn : n < wBnat.
    apply: (ltn_trans ltnsz); apply/ltP; rewrite -Z2Nat.inj_lt; last by [].
    * by case/andP: le_trielen => _ /lebP/(BinInt.Z.le_lt_trans _); apply.
    * by rewrite -to_Z_0; apply/lebP; apply: le0int.
  by move: ltnsz; rewrite -{1}eqn -ltintE => /trienth.
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


Fixpoint updatetrie t v (upd : option T -> option T) :=
  match v, t with
  | v0 :: v', Trie x a =>
      if length a == 0 then
        Trie x (make trielen Empty).[v0 <- updatetrie Empty v' upd]
      else
        Trie x a.[v0 <- updatetrie a.[v0] v' upd]
  | v0 :: v', Empty    => Trie None
                            (make trielen Empty).[v0 <- updatetrie Empty v' upd]
  | [::], Trie x a => Trie (upd x) a
  | [::], Empty    => Trie (upd None) (make 0 Empty)
  end.

Definition addtrie t v e := updatetrie t v (fun => Some e).
Definition deltrie t v := updatetrie t v (fun => None).

Fixpoint gettrie t v :=
  match v, t with
  | v0 :: v', Trie x a => gettrie a.[v0] v'
  | [::], Trie x a => x
  | _, _  => None
  end.

Lemma get_empty i : [| | Empty : trie |].[i] = Empty.
Proof.
by rewrite get_out_of_bounds //= -[i <? 0]/(i < 0)%O ltintE to_nat0 ltn0.
Qed.

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
- by rewrite length_make lelenmax; right.
- by rewrite default_make.
- by move=> /= i lti; rewrite get_make.
Qed.

Lemma is_fltrie_updatetrie t v upd :
  is_fltrie t -> is_fltrie (updatetrie t v upd).
Proof.
elim: v t => [|v0 v IHv] [_ |x t] //=; first exact: flarray_make0.
  apply/flarrayP; split.
  + by right; rewrite length_set length_make lelenmax.
  + by rewrite default_set default_make.
  + move=> /= i lti; case: (altP (v0 =P i)) => [{v0}->|/eqP v0neqi].
    * rewrite get_set_same; first exact: IHv.
      by rewrite length_make lelenmax.
    * by rewrite (get_set_other _ _ _ _ _ v0neqi) get_make.
case/flarrayP => eqlen eqdef /= flti.
case: eqlen => [-> /= | Hlen].
  apply/flarrayP; split.
  - by right; rewrite length_set length_make lelenmax.
  - by rewrite default_set default_make.
  - move=> /= i lti.
    case: (altP (v0 =P i)) => [{v0}->|/eqP v0neqi].
    + rewrite get_set_same; first exact: IHv.
      by rewrite length_make lelenmax; exact: lti.
    + by rewrite (get_set_other _ _ _ _ _ v0neqi) get_make.
rewrite Hlen (negbTE len_neq0) /=.
apply/flarrayP; split.
- by right; rewrite length_set.
- by rewrite default_set.
- move=> /= i lti.
  case: (altP (v0 =P i)) => [{v0}->|/eqP v0neqi].
  + rewrite get_set_same; first exact: (IHv _ (flti _ lti)).
    by rewrite Hlen; exact: lti.
  + by rewrite (get_set_other _ _ _ _ _ v0neqi) (flti _ lti).
Qed.
Canonical updatefltrie (t : fltrie) v upd :=
  FLTrie (is_fltrie_updatetrie v upd (fltrieP t)).


Lemma get_updatetrie t v upd w :
  is_fltrie t ->
  all (<%O^~ trielen)%O v ->
  gettrie (updatetrie t v upd) w =
    if w == v then upd (gettrie t w) else gettrie t w.
Proof.
elim: w v t => [| w0 w IHw] [|v0 v] [|x t] //=.
- by move => _ _; case: eqP => //=.
- by move=> _ _; rewrite get_empty /=; case w.
- move=> _; case/andP=> [ltv0 {}/IHw Hrec].
  rewrite eqseq_cons; case: eqP => /= [{w0}-> | neq].
    rewrite get_set_same; last by rewrite length_make lelenmax.
    by rewrite {}Hrec /=; case: (w == v) => /=; case w.
  by rewrite (get_set_other _ _ _ _ _ (not_eq_sym neq)) get_make /=; case w.
- case/flarrayP => eqlen eqdef /= fltrec.
  case/andP=> [ltv0 {}/IHw Hrec].
  case: eqlen => [len0 | leneq] /=.
    rewrite len0 /= [t.[w0]]get_out_of_bounds; first last.
      by rewrite len0 -[w0 <? 0]/(w0 < 0)%O ltintE to_nat0 ltn0.
    rewrite eqdef eqseq_cons; case: eqP => /= [ {w0}-> | neq] /=.
      rewrite get_set_same; last by rewrite length_make lelenmax; exact: ltv0.
      exact: Hrec.
    by rewrite (get_set_other _ _ _ _ _ (not_eq_sym neq)) get_make /=.
  rewrite leneq (negbTE len_neq0).
  rewrite eqseq_cons; case: eqP => /= [{w0}-> | neq].
    rewrite get_set_same; last by rewrite leneq; exact: ltv0.
    by move/(_ _ ltv0): fltrec => /Hrec.
  by rewrite (get_set_other _ _ _ _ _ (not_eq_sym neq)).
Qed.
Definition get_updatefltrie (t : fltrie) v upd w :=
  get_updatetrie (v := v) upd w (fltrieP t).


Lemma updatetrie_comp t v u1 u2 :
  is_fltrie t ->
  all (<%O^~ trielen) v ->
  gettrie (updatetrie t v (u1 \o u2))
  =1 gettrie (updatetrie (updatetrie t v u2) v u1).
Proof.
move=> flt allv w; rewrite !get_updatetrie //=; last exact: is_fltrie_updatetrie.
by case: eqP.
Qed.
Definition updatefltrie_comp (t : fltrie) v u1 u2 :=
  updatetrie_comp (v := v) u1 u2 (fltrieP t).


Lemma updatetrieC t v w u1 u2 :
  is_fltrie t ->
  all (<%O^~ trielen) v -> all (<%O^~ trielen) w -> v != w ->
  gettrie (updatetrie (updatetrie t v u1) w u2)
  =1 gettrie (updatetrie (updatetrie t w u2) v u1).
Proof.
move=> flt allv allw /negbTE neqvw x.
rewrite !get_updatetrie //=; try exact: is_fltrie_updatetrie.
by case: (altP (x =P v)) => [{x}->|]; first by rewrite neqvw.
Qed.
Definition updatefltrieC (t : fltrie) v w u1 u2 :=
  updatetrieC (v := v) (w := w) u1 u2 (fltrieP t).


Fixpoint getprefixtrie t w :=
  match t, w with
  | Trie (Some e) a, _ => Some (e, w)
  | Trie None a, w0 :: w' => getprefixtrie a.[w0] w'
  | _, _ => None
  end.

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
  correctrelat R (<%O^~ trielen) ->
  trie_rewrites1_front (mktrie R) w = None -> rewrites_front R w = [::].
Proof.
rewrite /trie_rewrites1_front /mktrie /correctrelat => /= corr.
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
  correctrelat R (<%O^~ trielen) ->
  forall u v : word int, getprefixtrie (mktrie R) w = Some (u, v) ->
         u ++ v \in rewrites_front R w.
Proof.
rewrite /mktrie /correctrelat => /= corr.
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
  correctrelat R (<%O^~ trielen) ->
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
  correctrelat R (<%O^~ trielen) -> rewrites1_Ok R (trie_rewrites1 (mktrie R)).
Proof. by move/trie_rewrites1_frontP => H; apply:rewrite1_from_frontP. Qed.


Definition eqnor tr fuel (p1 p2 : word int) :=
  let x1 := norfuel2 (trie_rewrites1 tr) fuel p1 in
  let x2 := norfuel2 (trie_rewrites1 tr) fuel p2 in
  eqseq_int x1.1 x2.1.


Definition spair_confluence_dec_trie R fuel :=
  let tr := (mktrie R) in
  if all_tr (fun p => eqseq_int p.1 p.2) (all_npairs_int R) then
    let spairs := filter (fun p => ~~ eqseq_int p.1 p.2) (all_spairs_int R) in
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


Section Size.

Variable P : pres int.

Lemma pgen_size sz :
  all (<%O^~ sz) (pgen P) -> correctrelat (prelat P) (<%O^~ sz).
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
by rewrite ltintE maxintE gtn_max -!ltintE lti ltg0.
Qed.

Lemma pgen_maxlen : (0 < pres_trielen <= max_length)%O.
Proof.
have foldlmaxlt : (foldl max 0 (pgen P) < max_length)%O.
  have : (0 < max_length)%O by [].
  elim: (pgen P) (0) pgenOk => [|g0 g IHg] //= i /[swap] lti.
  case/andP => ltg0 {}/IHg; apply.
  by rewrite ltintE maxintE gtn_max -!ltintE lti ltg0.
apply/andP; split; first last.
  by rewrite /pres_trielen; apply ltleint; exact: foldlmaxlt.
rewrite /pres_trielen ltintE to_nat0 to_natD; first by rewrite addnS ltnS.
rewrite addn1.
move: foldlmaxlt; rewrite ltintE => /leq_ltn_trans; apply.
by apply/ltP; rewrite -Z2Nat.inj_lt.
Qed.

Lemma pgen_trielen :
  all (<%O^~ max_length) (pgen P) -> all (<%O^~ pres_trielen) (pgen P).
Proof.
rewrite /pres_trielen.
have : (0 < max_length)%O by [].
elim: (pgen P) (0) => // [g0 g IHg] /= i lti.
case/andP => ltg0 alllt; apply/andP; split; first last.
  by apply: IHg => //; rewrite ltintE maxintE gtn_max -!ltintE lti ltg0.
elim: g alllt {IHg} i lti g0 ltg0 => [| g1 g IHg] /=.
  move=> _ i lti g ltg; rewrite ltintE to_natD to_nat1 addn1 maxintE.
    by rewrite ltnS leq_maxr.
  apply: (leq_trans (n := (to_nat max_length).+1)).
    by rewrite ltnS gtn_max -!ltintE lti ltg.
  by apply/ltP; rewrite -Z2Nat.inj_lt.
case/andP => [ltg1 alllt] i lti g0 ltg0.
have -> : max (max i g0) g1 = max (max i g1) g0.
  apply: to_nat_inj.
  rewrite [LHS]maxintE [in LHS]maxintE [RHS]maxintE [in RHS]maxintE.
  by rewrite -!maxnA [maxn (to_nat g1) _]maxnC.
apply: IHg => //=.
by rewrite ltintE maxintE gtn_max -!ltintE lti ltg1.
Qed.

Lemma corrrelat_trielen : correctrelat (prelat P) (<%O^~ pres_trielen).
Proof. exact/pgen_size/pgen_trielen. Qed.

Definition spair_confluence_loop_trieP :=
  spair_confluence_loopP (trie_rewrites1P pgen_maxlen corrrelat_trielen).

End Size.


Section EnumNormalForms.

Variable (P : pres int) (trielen : int).
Hypothesis convP : convergent (prelat P).
Hypothesis trielenOk : (0 < trielen <= max_length)%O.
Hypothesis genPlen : all (<%O^~ trielen) (pgen P).

Implicit Types (u v w : word int) (norf : seq (word int)).

Let Ptrie := mktrie trielen (prelat P).
Let rew1P := trie_rewrites1P trielenOk (pgen_size genPlen).

Definition enum_normal_next_trie := enum_normal_next P (trie_rewrites1 Ptrie).
Definition enum_normal_trie_sz := enum_normal_sz P (trie_rewrites1 Ptrie).

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

End EnumNormalForms.


Require Import rewcert wfsizelexi.

Module Example.

Definition P := make_pres [::0; 1]
  [::
   ([::1;0], [::0;1]);
   ([::0;0;0], [::0;1]);
   ([::1;1], [::1])
  ].

Theorem final_ok : convergent (prelat P).
Proof.
apply: diamond.
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
have pgenOk : all (<%O^~ max_length) (pgen P) by [].
apply: (spair_confluence_loop_trieP pgenOk (fuel := 10)).
rewrite spair_confluence_loop_trieE.
by native_cast_no_check is_true_true.
Qed.

Goal flatten (traject (enum_normal_next_trie P (pres_trielen P)) [:: [::]] 4)
       = [:: [::]; [:: 0]; [:: 1]; [:: 0; 0]; [:: 0; 1]; [:: 0; 0; 1]].
Proof. by []. Qed.

End Example.
