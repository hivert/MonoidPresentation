From HB Require Import structures.
From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect.

Require Import monoids present factor rewcert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma flatten0 (T : eqType) (s : seq (seq T)) :
  flatten s = [::] -> all (@nilp _) s.
Proof.
move=> /(congr1 size); rewrite size_flatten /= => /eqP/natnseq0P shape0.
apply/(all_nthP [::]) => i _; apply/eqP.
by rewrite -nth_shape shape0 nth_nseq if_same.
Qed.

Section AlphabetChange.

Context {Alph : choiceType}.
Implicit Type (P : pres Alph) (u v w : word Alph).

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

Theorem simpleWPdec P :
  WPdecidable P -> forall u v : word Alph, decidable (u = v %[mod prelat P]).
Proof.
pose out := predC (mem (pgen P)).
have outwords w : (all (predC out) w) = (w \in words_of P).
  by apply: eq_all => a; rewrite /= negbK.
have cnteq r s : r = s %[mod prelat P] -> count out r = count out s.
  case=> pth /[swap] {s}->; elim: pth r => [//| p0 pth IHpth] r /=.
  case/andP => /[swap]{}/IHpth <- {pth}.
  case/rewritesP => pre suf [r1 r2] /= {r}-> {p0}-> rinP.
  rewrite !count_cat; congr (_ + (_ + _)) => {pre suf}.
  have count0 r : r \in words_of P -> count out r = 0.
    rewrite /out unfold_in /= => Hall.
    by apply/eqP; rewrite -leqn0 leqNgt -has_count has_predC negbK.
  have {rinP} :(r1 \in words_of P) && (r2 \in words_of P).
    by move: rinP; rewrite mem_undirected => /orP[] /words_of_prelat/andP[/= -> ->].
  by case/andP=> /count0-> /count0->.
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
                 [/\ a = b, u0 = v0 %[mod prelat P] & u1 = v1 %[mod prelat P] ].
  rewrite {IHn u cntu}equ {v}eqv.
  split=> [|[eqab eq0 eq1]]; first last.
    apply: (stable_cat (@equiv_trans _ _) (@equiv_stable _ _)) => //.
    rewrite -{}eqab -(cat1s a u1) -(cat1s a v1).
    apply: (stable_cat (@equiv_trans _ _) (@equiv_stable _ _)) => //.
    exact: equiv_refl.
  admit.
case: (altP (a =P b)) => [eqab | /negbTE neqab]; first last.
  by right; rewrite {}equv => [[/eqP]]; rewrite neqab.
subst b.
case: (Hdec u0 v0 Pu0 Pv0) => {Pv0} [eq0 | neq0]; first last.
  by right; rewrite equv => [[_ eq0 _]]; exact: neq0.
have : count out u = (count out u1).+1.
  move: outa; rewrite equ count_cat /= => ->; rewrite add1n.
  suff -> : count out u0 = 0 by [].
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_predC negbK.
rewrite {}cntu => -[] /esym {}/IHn/(_ v1) [eq1 | neq1]; first last.
  by right; rewrite equv => [[_ eq1]]; exact: neq1.
by left; rewrite equv.
Admitted.

Corollary eqrelat_dec (P1 P2 : pres Alph) :
  prelat P1 = prelat P2 -> WPdecidable P1 -> WPdecidable P2.
Proof. by move=> eq /simpleWPdec dec u v _ _; rewrite -eq. Qed.

End AlphabetChange.


Section Monogenic.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition monogenic P : bool := size (pgen P) == 1.

Theorem monogenic_dec P : monogenic P -> WPdecidable P.
(* TODO : Confined in a^m where m is the size of the largest relation word *)
Admitted.

End Monogenic.


Section FreeProductMonogenicFree.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition free_product_monogenic_free P :=
  size (undup (flatten (relwords P))) <= 1.

Theorem free_product_monogenic_free_dec P :
  free_product_monogenic_free P -> WPdecidable P.
Proof.
rewrite /free_product_monogenic_free.
case Hgs : (undup (flatten (relwords P))) => [|g [|//]] _.
- move/undup_nil/flatten0/allP=> /= in Hgs.
  move=> u v _ _; case: (altP (u =P v)) => [-> | /negP nequv].
  + left; exact: equiv_refl.
  + right=> [eq]; apply: nequv.
    case: eq  => pth /[swap] {v}->.
    elim: pth u => [| p0 pth IHpth] //= u /andP[Hp0 {}/IHpth /eqP <-].
    case/rewritesP: Hp0 => pre suf [r1 r2] /= {u}-> {p0}-> rinP.
    suff : (r1 \in relwords P) && (r2 \in relwords P).
      by case/andP => /Hgs/nilP-> /Hgs/nilP->.
    move: rinP; rewrite mem_undirected => /orP[] /mem_relatwords //.
    by rewrite andbC.
- have gsrel : correctrelat (prelat P) (mem [:: g]).
    apply/allP => /= -[r1 r2] /= /mem_relatwords.
    suff rnseq r : r \in relwords P -> exists n, r = nseq n g.
      case/andP => /rnseq [n1] {r1}-> /rnseq [n2] {r2}->.
      by rewrite !all_nseq !inE eqxx !orbT.
    move=> H; exists (size r).
    apply/all_pred1P/allP => x xinr /=.
    suff : x \in [:: g] by rewrite inE => ->.
    by rewrite -Hgs mem_undup; apply/flattenP => /=; exists r.
  pose Q := Pres [:: g] _ is_true_true gsrel.
  apply: (eqrelat_dec (P1 := Q)) => //.
  exact: monogenic_dec.
Qed.

End FreeProductMonogenicFree.


Section DefLeftCycleFree1Rel.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition two_letters P : bool := size (pgen P) == 2.

Definition left_cycle_free_1rel (P : pres Alph) : Prop :=
  exists (a b : Alph) (u v : word Alph),
      a != b /\ prelat P = [:: (a :: u, b :: v)].
Definition is_left_cycle_free_1rel P : bool :=
  if (prelat P) is [:: (a :: _, b :: _)] then a != b else false.

Lemma left_cycle_free_1relP P :
  reflect (left_cycle_free_1rel P) (is_left_cycle_free_1rel P).
Proof.
rewrite /is_left_cycle_free_1rel.
apply (iffP idP); case Hrel: (prelat P) => [|[[|a r1][|b r2]] [|rels]] //;
  first 1 [by move=> neqab; exists a; exists  b; exists r1; exists r2]
        || (try by move=> [a'][b'][u'][v']; rewrite Hrel => [[]]).
by case=> [a'][b'][u'][v'][neq]; rewrite Hrel => [[-> _ -> _]].
Qed.

Definition same_number_of_occ P a :=
  forall r, r \in prelat P ->
                 count_mem a r.1 > 0 /\ count_mem a r.1 = count_mem a r.2.
Definition has_same_number_of_occ P a :=
  all (fun r => (count_mem a r.1 > 0) && (count_mem a r.1 == count_mem a r.2))
    (prelat P).
Lemma has_same_number_of_occP P a :
  reflect (same_number_of_occ P a) (has_same_number_of_occ P a).
Proof.
rewrite /has_same_number_of_occ /same_number_of_occ.
by apply (iffP allP) => /= H r {}/H => [/andP[-> /eqP ->]// | [-> /= ->]].
Qed.

(* Theorem 4.1 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem left_cycle_free_1rel_same_number_occ_dec P a :
  left_cycle_free_1rel P -> same_number_of_occ P a ->
  WPdecidable P.
Admitted.

Corollary check_same_number_occ_dec P a :
  is_left_cycle_free_1rel P -> has_same_number_of_occ P a ->
  WPdecidable P.
Proof.
move=> /left_cycle_free_1relP H1 /has_same_number_of_occP.
exact: left_cycle_free_1rel_same_number_occ_dec.
Qed.

End DefLeftCycleFree1Rel.


Section SmallOverlap.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Variant piece P u : Prop :=
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
    infix w1 u -> infix w2 u
    -> piece P u.

Fixpoint piece_pair (once twice facts : seq (word Alph)) :=
  if facts is f :: facts' then
    if     f \in twice then piece_pair once twice facts'
    else if f \in once then piece_pair once (f :: twice) facts'
    else                    piece_pair (f :: once) twice facts'
  else (once, twice).

Definition pieces P :=
  (foldl (fun once_twice w => piece_pair once_twice.1 once_twice.2
                               (non_empty_infixes w))
    ([::], [::]) (relwords P)).2.

Lemma piecesP P u :
  reflect (piece P u) (u \in pieces P).
Proof.
(* TODO *)
Admitted.

Definition small_overlap (n : nat) P :=
  forall u, u \in relwords P ->
     forall f : seq (word Alph),
     (forall w, w \in f -> piece P w) ->
       u = flatten f -> size f >= n.

Lemma small_overlapW P n1 n2 :
  n1 >= n2 -> small_overlap n1 P -> small_overlap n2 P.
Proof.
by move=> leqn12 Hso u /[swap] f {}/Hso/[apply]/[apply]/(leq_trans leqn12).
Qed.

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

Lemma check_small_overlapP n P facts :
  check_small_overlap n P facts -> small_overlap n P.
Proof.
(* TODO: greedy factorization is shorter than any other one *)
Admitted.


(* Section 4.2 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem c3_monoid_dec P : small_overlap 3 P -> WPdecidable P.
Admitted.

Corollary check_c3_monoid_dec P facts :
  check_small_overlap 3 P facts -> WPdecidable P.
Proof. by move/check_small_overlapP/c3_monoid_dec. Qed.

End SmallOverlap.



Definition sotestpres :=
  make_pres [:: 0; 1]
            [:: ([:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0],
                 [:: 0; 1; 1; 1; 0; 0; 1; 0]) ].

Lemma sotestpres_dec : WPdecidable sotestpres.
Proof. exact: (check_c3_monoid_dec (facts := [::
                     [:: [:: 1; 0; 0; 0]; [:: 0; 1; 1]; [:: 0; 0; 0] ];
                     [:: [:: 0; 1; 1]; [:: 1; 0; 0]; [:: 1; 0] ]
                  ])).
Qed.

(*
Eval compute in non_empty_factors [:: 3; 1; 2; 1].
Eval compute in piece_pair
                  [::] [::] (non_empty_factors [:: 3; 1; 2; 1]).

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

Eval compute in check_small_overlap 3 testpres
                  [::
                     [:: [:: 1; 0; 0; 0]; [:: 0; 1; 1]; [:: 0; 0; 0] ];
                     [:: [:: 0; 1; 1]; [:: 1; 0; 0]; [:: 1; 0] ]
                  ].
*)

Section Watier.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Variant isWatier P :=
  | IsWatier : forall (a b : Alph) (u v : word Alph) (k : nat),
      a != b -> pgen P = [:: a; b] ->
      prelat P = [:: (nseq k b ++ a :: u, a :: v)] ->
      ~~ infix (nseq k b) u -> isWatier P.
Definition check_Watier P (a b : Alph) (u v : word Alph) (k : nat) :=
  [&& a != b, pgen P == [:: a; b],
    prelat P == [:: (nseq k b ++ a :: u, a :: v)] &
      ~~ infix (nseq k b) u].
Lemma check_WatierP P a b u v k : check_Watier P a b u v k -> isWatier P.
Proof. by case/and4P => H1 /eqP H2 /eqP H3 H4; exists a b u v k. Qed.

(* Theorem 4.2 in https://github.com/james-d-mitchell/1-relation-paper *)
Theorem is_Watier_dec P : isWatier P -> WPdecidable P.
Admitted.
Corollary check_Watier_dec P a b u v k : check_Watier P a b u v k -> WPdecidable P.
Proof. move/check_WatierP; exact: is_Watier_dec. Qed.

End Watier.

Definition testWatier :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].

Lemma testWatierP : isWatier testWatier.
Proof. by exists 0 1 [:: 1; 1; 0] [::] 3. Qed.


Section Certificate.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).
Local Notation word := (word Alph).

Variant prescertificate :=
    (* param: rewriting certificate + final order *)
  | CompleteRewritingSystem of @pres_cert Alph & seq Alph
    (* param: a b u v k in < a b | b^k a u = a v > *)
  | Watier of Alph & Alph & word & word & nat
  | Monogenic
  | FreeProductMonogenicAndFree
    (* param: repeated letter a in < a b | a^k = a^l > *)
  | EqualNumberOfOccurences of Alph
    (* param: list of the factorizations of each relations words *)
    (*        in the order given by relwords P                   *)
  | SmallOverlap of seq (seq word)
  | Homogeneous. (* Not used in the database *)

Definition getRWScert C :=
  if C is CompleteRewritingSystem cert _ then cert else [::].
Definition getRWSorder C :=
  if C is CompleteRewritingSystem _ order then order else [::].

End Certificate.

(* Examples *)

Definition AB_AAAAAA_ABAABA :=
  make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])].
Lemma AB_AAAAAA_ABAABA_dec : WPdecidable AB_AAAAAA_ABAABA.
Proof.
set pres := AB_AAAAAA_ABAABA.
pose certCRS := CompleteRewritingSystem
    [::
       add_rel [::0;1;0;0;1;0] [::0;0;0;0;0;0]
         [:: RTriple 0 0 false];
       add_rel [::0;1;0;0;0;0;0;0;0] [::0;0;0;0;0;0;0;1;0]
         [:: RTriple 0 3 true;
             RTriple 1 0 true];
       rm_rel 0
         [:: RTriple 0 0 false]]
    [::0;1].
pose p := if certCRS is CompleteRewritingSystem cert order then
            (cert, order) else ([::], [::]).
pose cert := p.1; pose order := p.2.
have wfc : wfpres_cert pres cert by compute.
apply: (isopres_dec (@iso_final_pres _ pres cert wfc)).
apply: convergent_dec; rewrite prelat_final_pres.
apply: (rgen_convergent (@reorderK _ _ order is_true_true) erefl).
apply: diamond.
  exact: (decreasing_wf (@lt_sizelexi_stable _ nat) sizelexi_nat_wf).
exact: (spair_confluence_loopP (fuel := 10)).
Qed.

Definition AB_AAAB_A :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].
Lemma AB_AAAB_A_dec : WPdecidable AB_AAAB_A.
Proof. exact: (@check_Watier_dec _ _ 0 1 [:: 1; 1; 0] [::] 3). Qed.

Definition A_AAA_A := make_pres [:: 0] [:: ([:: 0; 0; 0], [:: 0])].
Lemma A_AAA_A_dec : WPdecidable A_AAA_A.
Proof. exact: monogenic_dec. Qed.

Definition AB_ABB_BA := make_pres [:: 0; 1] [:: ([:: 0; 1; 1], [:: 1; 0])].
Lemma AB_ABB_BA_dec : WPdecidable AB_ABB_BA.
Proof. exact: (check_same_number_occ_dec (a := 0)). Qed.

Definition AB_BAAAABBAAA_ABBBAABA :=
  make_pres [:: 0; 1]
       [:: ([:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0], [:: 0; 1; 1; 1; 0; 0; 1; 0]) ].
Lemma AB_BAAAABBAAA_ABBBAABA_dec : WPdecidable AB_BAAAABBAAA_ABBBAABA.
Proof. exact: (check_c3_monoid_dec (facts := [::
                     [:: [:: 1; 0; 0; 0]; [:: 0; 1; 1]; [:: 0; 0; 0] ];
                     [:: [:: 0; 1; 1]; [:: 1; 0; 0]; [:: 1; 0] ]
                  ])).
Qed.


