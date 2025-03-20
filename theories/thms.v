From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Require Import monoids present factor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section AlphabetChange.

Context {Alph : choiceType} (P : pres Alph).
Implicit Type (u v w : word Alph).


Variant first_occ_spec (p : pred Alph) u : Type :=
  FirstOcc a u0 u1 : all (predC p) u0 -> p a -> u = u0 ++ a :: u1
                     -> first_occ_spec p u.
Lemma first_occP p u : has p u -> first_occ_spec p u.
Proof.
move=> pu.
have x0 : Alph by case: u pu.
move: pu; case: findP => // i ltiu /(_ x0); set a := nth x0 u i => Hb.
move/(_ a) => before _.
have := cat_take_drop i u; rewrite (drop_nth x0 ltiu) => eq.
have {}before : all (predC p) (take i u).
  apply/allP => x /[dup] xin.
  rewrite -{1}index_mem size_take ltiu => {}/before /=.
  have:= xin => /(nth_index a); rewrite nth_take => [-> -> //|].
  have:= size_take i u; rewrite ltiu => {2}<-.
  by rewrite index_mem.
by exists (nth x0 u i) (take i u) (drop i.+1 u).
Qed.

Theorem simpleWPdec :
  WPdecidable P -> forall u v : word Alph, decidable (u = v %[mod prelat P]).
Proof.
pose out := predC (mem (pgen P)).
have outwords w : (all (predC out) w) = (w \in words_of P).
  by apply: eq_all => a; rewrite /= negbK.
have cnteq r s : r = s %[mod prelat P] -> count out r = count out s.
  admit.
move=> Hdec u; move: {2}(count _ _) (erefl (count out u)) => n.
elim: n u => [| n IHn] u.
  move/eqP; rewrite -leqn0 leqNgt -has_count has_predC negbK => Pu v.
  have {}Pu : u \in words_of P by exact: Pu.
  case: (boolP (v \in words_of P)) => [Pv | nPv]; first exact: Hdec.
  by right=> equv; move: nPv; rewrite -(equiv_words_ofE equv) Pu.
move=> cntu v.
have /first_occP[a u0 u1] : has out u by rewrite has_count cntu.
rewrite outwords => Pu0 /= outa equ.
case: (altP (count out u =P count out v)) => [/esym | /negbTE neqout]; first last.
  by right => {}/cnteq /eqP; rewrite neqout.
rewrite cntu => cntv.
have {cntv} /first_occP[b v0 v1] : has out v by rewrite has_count cntv.
rewrite {}outwords => Pv0 /= outb eqv.
have {outb} equv : u = v %[mod prelat P] <->
              u0 = v0 %[mod prelat P] /\ u1 = v1 %[mod prelat P].
  admit.
case: (Hdec u0 v0 Pu0 Pv0) => {Pv0} [eq0 | neq0]; first last.
  by right; rewrite equv => [[eq0 _]]; exact: neq0.
have : count out u = (count out u1).+1.
  move: outa; rewrite equ count_cat /= => ->; rewrite add1n.
  suff -> : count out u0 = 0 by [].
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_predC negbK.
rewrite {}cntu => -[] /esym {}/IHn/(_ v1) [eq1 | neq1]; first last.
  by right; rewrite equv => [[_ eq1]]; exact: neq1.
by left; rewrite equv.
Admitted.

End AlphabetChange.


Section Monogenic.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition monogenic P : bool := size (pgen P) == 1.

Theorem monogenic_WPdec P : monogenic P -> WPdecidable P.
Admitted.

End Monogenic.

Section DefLeftCycleFree1Rel.

Context {Alph : choiceType} {x0 : Alph}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition two_letters P : bool := size (pgen P) == 2.

Definition is_left_cycle_free_1rel P : bool :=
  let rel := head ([::], [::]) (prelat P) in
  [&& size (prelat P) == 1,
    rel.1 != [::], rel.2 != [::] &
    head x0 rel.1 != head x0 rel.2].

Inductive left_cycle_free_1rel
  (P : pres Alph) : Prop :=
  LeftCycleFree1RelProp :
    forall (a b : Alph) (u v : word Alph),
      a != b -> a \in pgen P -> b \in pgen P ->
      prelat P = [:: (a :: u, b :: v)] ->
      left_cycle_free_1rel P.

Lemma left_cycle_free_1relP P :
  reflect (left_cycle_free_1rel P)
          (is_left_cycle_free_1rel P).
Proof.
Admitted.

Definition has_same_number_of_occ P a :=
  all (fun r => (count_mem a r.1 > 0)
                && (count_mem a r.1 ==
                      count_mem a r.2)) (prelat P).

Definition same_number_of_occ P a :=
  forall r, r \in prelat P ->
                  (count_mem a r.1 > 0 /\
                     count_mem a r.1 = count_mem a r.2).

(* Theorem 4.1 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem left_cycle_free_1rel_same_number_occ_dec P a :
  left_cycle_free_1rel P -> (same_number_of_occ P a) ->
  WPdecidable P.
Admitted.

End DefLeftCycleFree1Rel.


Section SmallOverlap.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition non_empty_factors u :=
  [seq drop i (take j u) | j <- iota 0 (size u).+1,
    i <- iota 0 j].

Lemma non_empty_factorsP w u :
  reflect (u != [::] /\ factor w u)
    (u \in non_empty_factors w).
Proof.
apply (iffP idP).
- elim/last_ind: w u => [| w wl IHw] u.
    by rewrite /non_empty_factors //.
  rewrite /non_empty_factors size_rcons.
  admit.
Admitted.

Definition relwords P :=
  [seq r.1 | r <- undirected (prelat P)].

Inductive piece P u : Prop :=
| PieceSameWord :
  forall p1 q1 p2 q2,
    u != p1 ++ u ++ q1 ->
    p1 != p2 ->
    p1 ++ u ++ q1 = p2 ++ u ++ q2 ->
    p1 ++ u ++ q1 \in relwords P -> piece P u
| PieceDiffWords :
  forall w1 w2,
    w1 != w2 ->
    w1 \in relwords P ->
    w2 \in relwords P ->
    factor w1 u -> factor w2 u
    -> piece P u.

Fixpoint piece_pair (once twice facts : seq (word Alph)) :=
  if facts is f :: facts' then
    if     f \in twice then piece_pair once twice facts'
    else if f \in once then piece_pair once (f :: twice) facts'
    else                    piece_pair (f :: once) twice facts'
  else (once, twice).

Definition pieces P :=
  (foldl (fun once_twice w => piece_pair once_twice.1 once_twice.2
                               (non_empty_factors w))
    ([::], [::]) (relwords P)).2.

Lemma piecesP P u :
  reflect (piece P u) (u \in pieces P).
Proof.
Admitted.

Definition small_overlap (n : nat) P :=
  forall u, u \in relwords P ->
     forall f : seq (word Alph),
     (forall w, w \in f -> piece P w) ->
       u = flatten f -> size f >= n.

(** u is a greedy prefix of v for the pieces accepted by p *)
Definition is_greedy_prefix (p : pred (word Alph)) u v :=
  (u == v) || prefix u v && ~~ p (take (size u).+1 v).
Fixpoint is_greedy_rec (p : pred (word Alph)) f :=
  if f is f0 :: tl then
    if ~~ (is_greedy_prefix p f0 (f0 ++ head [::] tl)) then false
    else is_greedy_rec p tl
  else true.
Definition is_greedy_factorisation (p : pred (word Alph)) u f :=
  ([::] \notin f) && (flatten f == u) && (is_greedy_rec p f).

Definition check_small_overlap n P facts :=
  let p := pieces P in
  let rw := relwords P in
  if has (fun f => size f < n) facts then false
  else if size rw != size facts then false
  else all (fun pair_w_f => is_greedy_factorisation (mem p) pair_w_f.1 pair_w_f.2)
           (zip rw facts).

(* Section 4.2 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem c3_monoid_dec P :
  small_overlap 3 P -> WPdecidable P.
Admitted.

(* Section 4.2 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem c4_monoid_dec P :
  small_overlap 4 P -> WPdecidable P.
Admitted.

End SmallOverlap.



Eval compute in non_empty_factors [:: 3; 1; 2; 1].
Eval compute in piece_pair
                  [::] [::] (non_empty_factors [:: 3; 1; 2; 1]).

Definition testpres :=
  make_pres [:: 0; 1]
            [:: ([:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0],
                 [:: 0; 1; 1; 1; 0; 0; 1; 0]) ].
Definition testpieces := pieces testpres.

Goal perm_eq testpieces
  [:: [:: 1; 0; 0; 0]; [:: 0; 0; 0]; [:: 0; 0; 1]; [:: 0; 1; 1];
   [:: 1; 1; 0]; [:: 1; 1; 0; 0]; [:: 1; 0; 0]; [:: 0; 0]; [:: 0; 1];
   [:: 1; 1]; [:: 1]; [:: 1; 0]; [:: 0]].
Proof. by []. Qed.

Eval compute in testpieces.
Eval compute in is_greedy_factorisation (mem testpieces)
                  [:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0]
                  [:: [:: 1; 0; 0; 0]; [:: 0; 1; 1]; [:: 0; 0; 0] ].



Eval compute in pieces testpres.


Section Watier.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Variant isWatier P :=
  | IsWatier : forall (a b : Alph) (u v : word Alph) (k : nat),
      a != b -> pgen P = [:: a; b] ->
      prelat P = [:: (nseq k b ++ a :: u, a :: v)] ->
      ~~ factor (nseq k b) u -> isWatier P.

(* Theorem 4.2 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem Watier_dec P : isWatier P -> WPdecidable P.
Admitted.

End Watier.

Definition testWatier :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].

Lemma testWatierP : isWatier testWatier.
Proof. by exists 0 1 [:: 1; 1; 0] [::] 3. Qed.

