(** * Rewriting certificate for presentations *)
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
(** Presentation isomorphism certificate / To be extracted from SA database *)
From Stdlib Require Import Uint63.
From mathcomp Require Import all_boot all_order.
Require Import int_seq sizelexi monoids present.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma perm_eq_move_to_end (T : eqType) (x0 : T) (s : seq T) (n : nat) :
  n < size s -> perm_eq (rcons (take n s ++ drop n.+1 s) (nth x0 s n)) s.
Proof.
move=> ltnsz.
rewrite -cats1 -catA -[X in perm_eq _ X](cat_take_drop n s) perm_cat2l perm_catC.
by rewrite [X in perm_eq _ X](drop_nth x0).
Qed.


(* Proof that the entry and final presentations define the same monoid.
   Warning: this is an effective result, containing the data of the isomorphism,
   hence the Defined. *)
Section Certificate.

Context {A : choiceType}.

Section Rewrites.

Context (R : relat A).

Implicit Types (u v w : word A).

(** Apply relation no nrel at position pos in direction dirrel *)
Record rew_triple : Type := RTriple {
  nrel : PrimInt63.int;
  pos : nat;
  dirrel : bool; (* true means left to right rewriting *)
}.

Definition rew_cert := seq rew_triple.

Section ApplyTriple.
Variables (w : word A) (c : rew_triple).

Definition wf_triple :=
  (pos c <= size w) &&
    (if onth_int R (nrel c) is Some (r1, r2) then
       let src := if dirrel c then r1 else r2 in
       take (size src) (drop (pos c) w) == src
     else false).
Definition apply_triple :=
  if onth_int R (nrel c) is Some (r1, r2) then
    let src := if dirrel c then r1 else r2 in
    let dst := if dirrel c then r2 else r1 in
    take (pos c) w ++ dst ++ drop (pos c + size src) w
  else [::].

Lemma apply_tripleP : wf_triple -> apply_triple \in rewrites (undirected R) w.
Proof.
rewrite /apply_triple; case/andP => ltpre.
have /= := @onth_int_mem _ R (nrel c).
case: (onth_int R (nrel c)) => [/=[r1 r2] /(_ _ erefl) rinR|] //.
set src := if _ then _ else _; set dst := if _ then _ else _.
have Rin : (src, dst) \in (undirected R).
  by rewrite {}/src {}/dst mem_undirected; case: dirrel; rewrite rinR // orbT.
move=> /eqP eqsrc; apply/rewritesP.
exists (take (pos c) w) (drop (pos c + size src) w) (src, dst) => //=.
rewrite addnC -drop_drop -eqsrc size_take size_drop.
case: ltnP => [_ | Habs]; first by rewrite !cat_take_drop.
have := congr1 size eqsrc.
rewrite size_take size_drop ltnNge {}Habs /= => <-.
by rewrite !cat_take_drop.
Qed.

End ApplyTriple.

Implicit Type c : rew_cert.

Fixpoint check_rew_cert u v c :=
  if c is c0 :: c' then
    wf_triple u c0 && check_rew_cert (apply_triple u c0) v c'
  else u == v.
Fixpoint apply_seq_triple w c :=
  if c is c0 :: c' then
    apply_seq_triple (apply_triple w c0) c'
  else w.

Lemma check_certP u v c : check_rew_cert u v c -> u = v %[mod R].
Proof.
elim: c u => [| c0 c IHc] u /=; first by move/eqP ->;  exists [::].
rewrite andbC => /andP[{}/IHc /[swap]].
by move=> /apply_tripleP/rewrites_to1/rewrites_to_trans; apply.
Qed.

End Rewrites.


Variant transfo : Type :=
  | add_gen : A -> word A -> transfo
  | add_rel : word A -> word A -> rew_cert -> transfo
  | rm_rel : PrimInt63.int -> rew_cert -> transfo.
  (* | rm_gen : nat -> A -> word A -> transfo
     | perm_transf ??? *)

Definition pres_cert := seq transfo.

Section Defs.

Section Transfo.

Variable (G : seq A) (R : relat A) (t : transfo).

Definition wf_transfo : bool :=
  match t with
  | add_gen g w => (g \notin G) && (all (mem G) w)
  | add_rel u v prf =>
      [&& all (mem G) u, all (mem G) v & check_rew_cert R u v prf]
  | rm_rel n prf =>
      if onth_int R n is Some (u, v) then
        check_rew_cert (remove_ith_int R n) u v prf
      else false
  end.
Definition gen_transfo : seq A :=
  match t with
  | add_gen g w => rcons G g
  | _ => G
  end.
Definition rel_transfo : relat A :=
  match t with
  | add_gen g w => rcons R (w, [:: g])
  | add_rel u v prf => rcons R (u, v)
  | rm_rel n prf => remove_ith_int R n
  end.

End Transfo.

Variable (R : pres A) (t : transfo) (wft : wf_transfo (pgen R) (prelat R) t).

Lemma uniq_gen_transfo : uniq (gen_transfo (pgen R) t).
Proof.
case: t wft.
- by move=> g w /andP[gok _]; apply: Tietze2_gen_uniq.
- by move=> u v /= _ _; case: R.
- by move=> n /= _ _; case: R.
Qed.
Lemma correct_rel_transfo :
  all_relwords (rel_transfo (prelat R) t) (mem (gen_transfo (pgen R) t)).
Proof.
case: t wft.
- by move=> g w /andP[gok win]; apply: Tietze2_wf_relat.
- move=> u v prf /and3P[uin vin /check_certP eq_u_v].
  exact: wf_rcons_ext_pres.
- move=> n prf _; case: R => gens rels /= _.
  rewrite /all_relwords /= remove_ith_intE all_cat => /allP /= allok.
  apply/andP; split; apply/allP => /= p pin; apply allok.
  + exact: mem_take pin.
  + exact: mem_drop pin.
Qed.
Definition pres_transfo := Pres _ _ uniq_gen_transfo correct_rel_transfo.

End Defs.


Section IsoTransfo.

Variables (R : pres A) (t : transfo) (wft : wf_transfo (pgen R) (prelat R) t).

Theorem isopres_transfo_ex :
  { p : isopres R (pres_transfo wft) | p =1 idfun :> (_ -> _) }.
Proof.
case: t wft => /=.
- move=> g w /[dup] /andP[gok win] prf /=.
  set newpres := pres_transfo _.
  have -> : newpres = T2_pres win gok
    by apply/eqP; rewrite -eqpresE /= !eqxx.
  by exists (isopres_Tietze2 win gok).
- move=> u v prf /[dup] /and3P[uin vin /check_certP eq_u_v] tok.
  set newpres := pres_transfo _.
  have -> : newpres = rcons_ext_pres uin vin
    by apply/eqP; rewrite -eqpresE /= !eqxx.
  by exists (isopres_rcons_rule uin vin eq_u_v).
- move=> n prf wf_prf.
  have /= := @onth_int_mem _ (prelat R) n.
  case Hnth: (onth_int _ _) => [[/= u v] |]; first last.
    by exfalso; move: wf_prf; rewrite Hnth.
  have : check_rew_cert (remove_ith_int (prelat R) n) u v prf.
    by rewrite Hnth in wf_prf.
  move/check_certP => eq_u_v /(_ _ (erefl _)) prf0.
  set newpres := pres_transfo _.
  have [uin vin] : u \in words_of newpres /\ v \in words_of newpres.
    have eq_words_of : words_of newpres = words_of R by [].
    rewrite eq_words_of /words_of; move: prf0; case R => gens rels /= _.
    by rewrite /all_relwords !inE => /allP /= /[apply] /= /andP[-> ->].
  have @iso2 : isopres R newpres.
    apply: isopres_sym.
    apply: (isopres_trans (isopres_rcons_rule uin vin eq_u_v)).
    apply: pres_irrelevance_perm_eq => //=.
    rewrite -(onth_intE Hnth ([::], [::])) remove_ith_intE.
    exact/perm_eq_move_to_end/(onth_int_le Hnth).
  by exists iso2.
Qed.
Definition isopres_transfo : isopres R (pres_transfo wft)
  := let: exist x _ := isopres_transfo_ex in x.
Lemma isopres_transfoE : isopres_transfo =1 idfun :> (_ -> _).
Proof. by rewrite /isopres_transfo; case: isopres_transfo_ex. Qed.

End IsoTransfo.


Implicit Types (R : pres A) (c : pres_cert) (t : transfo).

Fixpoint gen_cert (gens : seq A) (c : pres_cert) :=
  if c is t :: c' then gen_cert (gen_transfo gens t) c' else gens.
Fixpoint rel_cert (rels : relat A) (c : pres_cert) :=
  if c is t :: c' then rel_cert (rel_transfo rels t) c' else rels.
Fixpoint wf_cert (gens : seq A) (rels : relat A) (c : pres_cert) :=
  if c is t :: c' then
    (wf_transfo gens rels t) &&
      (wf_cert (gen_transfo gens t) (rel_transfo rels t) c')
  else true.

Definition wfpres_cert R c := wf_cert (pgen R) (prelat R) c.

Definition final_pres R c (wfc : wfpres_cert R c) : pres A.
Proof.
elim: c R wfc => [R _ | t c IHc R /= /andP[wft wfc]]; first exact: R.
exact: (IHc (pres_transfo wft) wfc).
Defined.


Lemma pgen_final_pres R c (wfc : wfpres_cert R c) :
  pgen (final_pres wfc) = gen_cert (pgen R) c.
Proof.
elim: c R wfc => // t c IHc R /= /andP[wft /= wfc].
exact: (IHc (pres_transfo wft) wfc).
Qed.

Lemma prelat_final_pres R c (wfc : wfpres_cert R c) :
  prelat (final_pres wfc) = rel_cert (prelat R) c.
Proof.
elim: c R wfc => // t c IHc R /= /andP[wft /= wfc].
exact: (IHc (pres_transfo wft) wfc).
Qed.

Theorem iso_final_pres_ex R c (wfc : wfpres_cert R c) :
  { p : isopres R (final_pres wfc) | p =1 idfun :> (_ -> _) }.
Proof.
elim: c R wfc => [| t c IHc] R /= wf; first by exists (isopres_refl R).
case/andP : wf => [wft wfc].
have [isotr eqisotr] := isopres_transfo_ex wft.
have [isoc eqisoc] := IHc (pres_transfo wft) wfc.
exists (isopres_trans isotr isoc) => u /=.
by rewrite eqisoc eqisotr.
Qed.
Definition iso_final_pres R c (wfc : wfpres_cert R c) :
  isopres R (final_pres wfc) := let: exist x _ := iso_final_pres_ex wfc in x.
Lemma iso_final_presE R c (wfc : wfpres_cert R c) :
  iso_final_pres wfc =1 idfun :> (_ -> _).
Proof. by rewrite /iso_final_pres; case: iso_final_pres_ex. Qed.

End Certificate.


Section NatListOrder.

Variable ord : list nat.

Definition rank (t : nat) : nat :=
  if t \in ord then index t ord else t + size ord.
Definition unrank (n : nat) : nat :=
  if n < size ord then nth 0 ord n else n - (size ord).

Lemma rankK : cancel rank unrank.
Proof.
rewrite /rank /unrank => t /=.
case: (boolP (t \in ord)) => [tin | tout].
  by rewrite index_mem tin nth_index.
by rewrite ltnNge leq_addl /= addnK.
Qed.

End NatListOrder.


Section ListOrder.

Variable (T : eqType).

Definition pord (l1 l2 : list T) (t : T) : T := nth t l2 (index t l1).

Lemma pordK (l1 l2 : list T) :
  uniq l1 -> perm_eq l1 l2 -> cancel (pord l1 l2) (pord l2 l1).
Proof.
rewrite /pord => uniq1 Hperm t.
have uniq2 : uniq l2 by rewrite -(perm_uniq Hperm).
have eqsize : size l1 = size l2 by rewrite (perm_size Hperm).
case (boolP (t \in l1)) => [tin | tout].
  rewrite nthK ?nth_index // -eqsize.
  by move: tin; rewrite -index_mem.
rewrite (memNindex tout) eqsize (nth_default _ (s := l2)) //.
move: tout; rewrite (perm_mem Hperm) => /memNindex ->.
by rewrite nth_default ?eqsize.
Qed.

End ListOrder.


Section SortedListOrder.

Context {d : Order.disp_t} {T : orderType d}.
Variables (l : seq T) (l_uniq : uniq l).

Let lsort := sort <%O l.

Lemma sort_perm : perm_eq l lsort.
Proof. by rewrite perm_sym perm_sort perm_refl. Qed.

Definition reorderK := pordK l_uniq sort_perm.

End SortedListOrder.


Module Example.

(* Autogenerated cert for < ab | babaabaa = abaaabaaa > *)
Definition present_entry := make_pres [::0;1]
  [:: ([::1;0;1;0;0;1;0;0], [::0;1;0;0;0;1;0;0;0])].

Definition present_final := make_pres [::0;1;2]
  [:: ([::1;0;0;0], [::2]);
      ([::1;0;1;0;0;2], [::0;2;2;0]);
      ([::1;0;1;0;0;1;0;0], [::0;2;2])].

Definition cert : pres_cert := [:: add_gen 2 [::1;0;0;0];
     add_rel [::1;0;1;0;0;2] [::0;2;2;0]
     [:: RTriple 1 5 false;
         RTriple 0 0 true;
         RTriple 1 1 true;
         RTriple 1 2 true];
     add_rel [::1;0;1;0;0;1;0;0] [::0;2;2]
     [:: RTriple 0 0 true;
         RTriple 1 1 true;
         RTriple 1 2 true];
     rm_rel 0
     [:: RTriple 2 0 true;
         RTriple 0 1 false;
         RTriple 0 5 false]].

Definition final_order := [::1;0;2].


(* Proof that the two presentation defines isomorphic monoids *)
Theorem isopres_final : isopres present_entry present_final.
Proof.
have certOk : wfpres_cert present_entry cert by [].
suff -> : present_final = final_pres certOk by apply: iso_final_pres.
by apply/eqP; rewrite -eqpresE pgen_final_pres prelat_final_pres.
Qed.

(* Proof that the presentation is terminating + confluent. *)
Theorem final_ok : convergent present_final.
Proof.
apply: (rgen_convergent (reorderK (l := final_order) is_true_true) erefl).
exact: (check_convergenceP (rewrites1P _)
          lt_sizelexi_stable sizelexi_nat_wf (fuel := 5)).
Qed.

End Example.

(*
Definition image_of_cert (p1 p2 : pres A) (c : pres_cert) : seq (word A).

Definition morph_of_cert (p1 p2 : pres A) (c : pres_cert) :
  wf_cert p1 p2 c -> {presmorph p1 -> p2}.

Theorem morph_correct p1 p2 c (wfc : wf_cert p1 p2 c) :
  morph_of_cert wfc = isopres_of_cert wfc.
*)
