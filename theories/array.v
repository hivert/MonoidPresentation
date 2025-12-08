(** * Array binding for Mathematical components                               *)
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
From Corelib Require Import Setoid.
From HB Require Import structures.
From Stdlib Require Import Znat BinIntDef Uint63 Ring Ring63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot all_order ssralg.

(* Workaround for MathComp / PArray notation incompatibilities *)
Notation "t .[ i ]" := (get t i).
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").


Require Import int_seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Order.POrderTheory.

Local Open Scope uint63_scope.


Lemma lt_max_lenght_wB : to_nat (max_length) < wBnat.
Proof. by rewrite wBnatE; apply/ssrnat.ltP/Z2Nat.inj_lt. Qed.

Lemma lt_lenght_wB (T : Type) (a : array T) : to_nat (length a) < wBnat.
Proof.
apply: (leq_ltn_trans _ lt_max_lenght_wB).
by rewrite -leEint; exact: leb_length.
Qed.


Local Open Scope order_scope.

Section ForLoop.

Context {A B : Type}.
Implicit Types (m n i j : int) (x y : A).

Inductive loopresult := | Continue of A | Return of B.

Variables (body : (int -> A -> loopresult)) (finish : A -> B).

Lemma for_loop_rec_subproof m n : m < n -> n - succ m < n - m.
Proof.
move=> /[dup] ltmn /ltW lemn; rewrite ltEint.
have leSmn : succ m <= n by apply ltleSint.
rewrite [X in (_ < X)%N]to_natB // [X in (X < _)%N]to_natB //.
rewrite ltn_sub2lE -?leEint //.
rewrite -{2}(to_natK m) succ_of_nat of_natK; first by rewrite ltnS.
move: ltmn; rewrite ltEint => /leq_ltn_trans; apply.
exact: ltwBnat.
Qed.

Fixpoint for_loop_rec m n x0
    (ACC : Acc (fun m n => m <? n) (n - m)) {struct ACC} : B :=
  match (decP (@idP (m <? n))) with
  | right _ => finish x0
  | left pf =>
      match body m x0 with
      | Return res => res
      | Continue a => for_loop_rec a (Acc_inv ACC (for_loop_rec_subproof pf))
      end
  end.
Definition for_loop m n x0 :=
  for_loop_rec x0 (Acc_intro_generator 40 wf_ltint (n - m)).

Lemma for_loop_rec_accE m n x0 ACC1 ACC2 :
  @for_loop_rec m n x0 ACC1 = @for_loop_rec m n x0 ACC2.
Proof.
move: {1}(n - m) (erefl (n - m)) ACC1 ACC2 => d Hd.
elim/(well_founded_ind wf_ltint): d m Hd x0 => d IHd m Hd x0.
case=> [ACC1][ACC2] /=; case: (body m x0) => [a | b //].
case decP => //= ltmn.
apply: (IHd _ _ _ (erefl _)).
by rewrite Hd for_loop_rec_subproof.
Qed.
Lemma for_loop_recE m n x0 ACC : @for_loop_rec m n x0 ACC = for_loop m n x0.
Proof. exact: for_loop_rec_accE. Qed.
Lemma for_loop_retE m n x0 res :
  m < n -> body m x0 = Return res -> for_loop m n x0 = res.
Proof.
rewrite /for_loop; case: (Acc_intro_generator _ _ _) => /= ACC ltmn ->.
by rewrite -[m <? n]/(m < n) ltmn.
Qed.
Lemma for_loop_contE m n x0 val :
  m < n -> body m x0 = Continue val ->
  for_loop m n x0 = for_loop (succ m) n val.
Proof.
rewrite {1}/for_loop; case: (Acc_intro_generator _ _ _) => ACC ltmn Heq /=.
rewrite -[m <? n]/(m < n) Heq; move: ltmn.
case (@idP (m < n)) => //= ltmn _.
exact: for_loop_recE.
Qed.
Lemma for_loop_finishE m n x0 : ~~ (m < n) -> for_loop m n x0 = finish x0.
Proof.
rewrite {1}/for_loop; case: (Acc_intro_generator _ _ _) => ACC /=.
by rewrite -[m <? n]/(m < n); case (@idP (m < n)).
Qed.

Lemma for_loop_ind_postcond m n x0
     (invar : int -> A -> Type) (postcond : B -> Type) :
  (forall i x, n <= i -> invar i x -> postcond (finish x)) ->
  (forall i x r, i < n -> body i x = Return r   -> invar i x -> postcond r) ->
  (forall i x c, i < n -> body i x = Continue c -> invar i x -> invar (succ i) c) ->
  invar m x0 -> postcond (for_loop m n x0).
Proof.
move=> Hfin Hret Hcont.
move: {1}(n - m) (erefl (n - m)) => d Hd.
elim/(well_founded_induction_type wf_ltint): d m Hd x0 => d IHd m Hd x0 Px0.
case: (boolP (m < n)) => [ltmn | /[dup] /for_loop_finishE ->]; first last.
  by rewrite -leNgt => /Hfin; apply.
case Hnext : (body m x0) => [a | b].
- have /(for_loop_contE ltmn) := Hnext => /[dup] Heq ->.
  apply: (IHd _ _ _ (erefl _)).
  + by rewrite Hd for_loop_rec_subproof.
  + exact: (Hcont _ _ _ ltmn Hnext).
- have /(for_loop_retE ltmn) := Hnext => /[dup] Heq ->.
  exact: (Hret _ _ _ ltmn Hnext).
Qed.

End ForLoop.

Section ForLoopLE.

Context {A B : Type}.
Implicit Types (m n i j : int) (x y : A).
Variables (body : (int -> A -> @loopresult A B)) (finish : A -> B).

Lemma for_loop_ind_le_postcond m n x0
     (invar : int -> A -> Type) (postcond : B -> Type) :
  (forall x, invar n x -> postcond (finish x)) ->
  (forall i x r, i < n -> body i x = Return r   -> invar i x -> postcond r) ->
  (forall i x c, i < n -> body i x = Continue c -> invar i x -> invar (succ i) c) ->
  invar m x0 -> m <= n -> postcond (for_loop body finish m n x0).
Proof.
move=> Hfin Hret Hcont Hinit lemn.
apply: (for_loop_ind_postcond
          (invar := fun i r => ((i <= n) * invar i r)%type)).
- move=> i x leni [lein] Hinv; apply: Hfin.
  by have -> : n = i by apply le_anti; rewrite leni lein.
- by move=> i x r /Hret/[apply]/[swap][[_]]/[swap]/[apply].
- move=> i x c /[dup] /ltleSint lti1n /Hcont/[apply]/[swap][[_]]/[swap]/[apply] H.
  by split; [exact: lti1n | exact: H].
- exact: (lemn, Hinit).
Qed.

End ForLoopLE.


Section ForLoopLE.

Context {A : Type}.
Implicit Types (m n i j : int) (x y : A).

Lemma for_loop_ind body m n x0 (invar : int -> A -> Type) :
  (forall i x, n <= i -> invar i x -> invar n x) ->
  (forall i x r, i < n -> body i x = Return r   -> invar i x -> invar n r) ->
  (forall i x c, i < n -> body i x = Continue c -> invar i x -> invar (succ i) c) ->
  invar m x0 -> invar n (for_loop body id m n x0).
Proof. exact: for_loop_ind_postcond. Qed.

Lemma for_loop_ind_le body m n x0 (invar : int -> A -> Type) :
  (forall i x r, i < n -> body i x = Return r   -> invar i x -> invar n r) ->
  (forall i x c, i < n -> body i x = Continue c -> invar i x -> invar (succ i) c) ->
  invar m x0 -> m <= n -> invar n (for_loop body id m n x0).
Proof. exact: for_loop_ind_le_postcond. Qed.

End ForLoopLE.


Section ForLoopSimple.

Context {A : Type} (body : (int -> A -> A)).
Implicit Types (m n i j : int) (x y : A).

Fixpoint for_loop_simple_rec m n x0
    (ACC : Acc (fun m n => m <? n) (n - m)) {struct ACC} : A :=
  match (decP (@idP (m <? n))) with
  | right _ => x0
  | left pf =>
      for_loop_simple_rec (body m x0) (Acc_inv ACC (for_loop_rec_subproof pf))
  end.
Definition for_loop_simple m n x0 :=
  for_loop_simple_rec x0 (Acc_intro_generator 40 wf_ltint (n - m)).

Lemma for_loop_simple_recE m n x0 :
  forall (acc1 acc2 : Acc (fun m n => m <? n) (n - m)),
  for_loop_simple_rec x0 acc1 =
    for_loop_rec (fun i a => Continue (body i a)) id x0 acc2.
Proof.
move: {1}(n - m) (erefl (n - m)) => d Hd.
elim/(well_founded_induction_type wf_ltint): d m Hd x0 => d IHd m Hd x0.
case => /= acc1; case => /= acc2.
case: (boolP (m < n)) => [ltmn | gemn] /=; first last.
  by case: decP => // H; exfalso; move: H gemn; rewrite -[m <? n]/(m < n) => ->.
case: decP => // H; apply: (IHd (Uint63.pred d)).
  rewrite ltEint -ltnS succ_subint1E // {}Hd.
  apply/negP => /eqP/(congr1 (fun i => to_nat i))/eqP.
  rewrite to_nat0 to_natB; last exact: ltW.
  by rewrite -/(_ <= _)%N leqNgt -ltEint ltmn.
by rewrite {d IHd}Hd /succ /Uint63.pred; ring.
Qed.
Lemma for_loop_simpleE m n x0 :
  for_loop_simple m n x0 = for_loop (fun i a => Continue (body i a)) id m n x0.
Proof. exact: for_loop_simple_recE. Qed.

Lemma for_loop_simple_ind m n x0 (invar : int -> A -> Type) :
  (forall i x, i < n -> invar i x -> invar (succ i) (body i x)) ->
  invar m x0 -> m <= n -> invar n (for_loop_simple m n x0).
Proof.
move=> Hrec Hx0 lemn; rewrite for_loop_simpleE.
by apply: for_loop_ind_le => // i x c ltin [{c}<-] /(Hrec _ _ ltin).
Qed.

End ForLoopSimple.

(*
From Coq Require Extraction ExtrOCamlInt63.

(* Print Extraction Inline.
Extraction Inline boolP.
Extraction Inline altP.
Extraction Inline idP.
*)
Extraction Inline add ltb succ decP.

Recursive Extraction for_loop_rec.
*)

Section ArrayManip.

Context {A : Type} (p : A -> bool) (a : array A).
Implicit Types (i j m n len : int).

Definition make_array (d : A) (len : int) (f : int -> A) :=
  for_loop_simple (fun i a => a.[i <- f i]) 0 len (make len d).
Definition find_array : int :=
  for_loop (fun i _ => if p a.[i] then Return i else Continue tt)
           (fun=> length a) 0 (length a) tt.
Definition has_array : bool :=
  for_loop (fun i _ => if p a.[i] then Return true else Continue tt)
           xpred0 0 (length a) tt.

Lemma length_make_array d len f :
  len <= max_length -> length (make_array d len f) = len.
Proof.
rewrite /make_array => le.
apply: (for_loop_simple_ind (invar := fun i ar => length ar = len)) => //.
- by move=> i c _ <-; rewrite length_set.
- by rewrite length_make -[len ≤? max_length]/(len <= max_length)%O le.
- exact: le0x.
Qed.
Lemma default_make_array d len f : default (make_array d len f) = d.
Proof.
apply: (for_loop_simple_ind (invar := fun i ar => default ar = d)) => //.
- by move=> i x _ <-; rewrite default_set.
- by rewrite default_make.
- exact: le0x.
Qed.
Lemma get_make_array len d f i :
  i < len <= max_length -> (make_array d len f).[i] = f i.
Proof.
rewrite /make_array => /andP[ltil lelen].
apply (for_loop_simple_ind
    (invar := fun n ar => length ar = len /\ forall j, j < n -> ar.[j] = f j)) => //.
- move=> j x ltjl [lenx Heq].
  rewrite length_set; split => // k /ltSleint.
  rewrite le_eqVlt => /orP[/eqP {k}-> | ltki].
    by rewrite get_set_same ?lenx.
  rewrite get_set_other ?Heq //.
  by apply/eqP; move: ltki; rewrite lt_def => /andP[].
- split => [|j]; last by rewrite ltEint to_nat0.
  by rewrite length_make -[len ≤? max_length]/(len <= max_length) lelen.
- exact: le0x.
Qed.
Lemma make_arrayE : make_array (default a) (length a) (get a) = a.
Proof.
have lena : length a <= max_length by exact: leb_length.
apply: array_ext; rewrite ?length_make_array //.
- by move=> i lti ; rewrite get_make_array // lena andbT.
- by rewrite default_make_array.
Qed.

Lemma find_array_ltn n : n < find_array -> ~~ p a.[n].
Proof.
rewrite /find_array; pose IH i := forall j, j < i -> ~~ p a.[j].
apply: (for_loop_ind_le_postcond (invar := fun i _ => IH i) (postcond := IH)) => //.
- rewrite {}/IH => i x r lti.
  by case: (boolP (p a.[i])) => Hp // [{r}<-].
- rewrite {}/IH => i c x lti.
  case: (boolP (p a.[i])) => Hp // _ H j /ltSleint.
  by rewrite le_eqVlt => /orP[/eqP -> // | /H].
- by move=> j; rewrite {}/IH ltEint to_nat0.
- exact: le0x.
Qed.
Lemma find_arrayE : find_array < length a -> p a.[find_array].
Proof.
rewrite /find_array; apply/contraLR; rewrite -leNgt.
move: 0 (le0x _ : 0 <= length a) => j.
apply: (for_loop_ind_postcond (invar := fun i _ => i <= length a)
          (postcond := fun b => ~~ p a.[b] -> length a <= b)) => //.
- move=> i x r ltil.
  by case: (boolP (p a.[i])) => // /[swap]-[{r}<- ->].
- by move=> i x c /ltleSint ltil; case: p.
Qed.

Lemma has_arrayP : reflect (exists2 n : int, n < length a & p a.[n]) has_array.
Proof.
suff /equivP : reflect (exists2 n, 0 <= n < length a & p a.[n]) has_array.
  by apply; split => [][x xin pax]; exists x =>[]//; move: xin; rewrite le0x.
rewrite /= /has_array; set body := (X in for_loop X).
apply (iffP idP).
  apply: (for_loop_ind_postcond (body := body)
            (invar := fun _ _ => true) (postcond := fun b => b -> _)) => //.
  rewrite {}/body => i _ r lti + _ _.
  case: (boolP (p a.[i])) => Hp // [] _.
  by exists i => //; rewrite le0x lti.
move=> [i /andP[_ lti] pai].
have : for_loop body xpred0 i (length a) tt.
  by apply: for_loop_retE => //; rewrite {}/body pai.
apply: contraLR; move: 0 (le0x i : 0 <= i) => j.
apply (for_loop_ind_postcond (body := body) (m := j)
          (invar := fun j _ => _) (postcond := fun b => ~~ b -> _)) => // {j}.
- by move=> j _ /le_trans/[apply]/le_lt_trans/(_ lti); rewrite ltxx.
- by rewrite /body => j x r _; case: p => // [][<-{r}].
- rewrite /body=> j x c _ /[swap].
  by rewrite le_eqVlt => /orP[/eqP{j}-> | /ltleSint]; first by rewrite pai.
Qed.

End ArrayManip.


Section ToSeq.

Context {S : Type}.
Implicit Type (a : array S) (s : seq S).

(* Definition to_seq a := array_foldr cons [::] a. *)
Definition to_seq a := mkseq (fun i => a.[of_nat i]) (to_nat (length a)).
(*Definition from_seq s d := (* FIXME : O((size s)^2) should be O(size s) *)
  make_array d (of_nat (size s)) (fun i => nth d s (to_nat i)). *)
Definition from_seq s d :=
  let len := of_nat (size s) in
  (for_loop_simple (fun i tls_ar =>
                     (behead tls_ar.1, tls_ar.2.[i <- head d tls_ar.1]))
    0 len (s, make len d)).2.

Lemma size_to_seq a : size (to_seq a) = to_nat (length a).
Proof. by rewrite /to_seq size_mkseq. Qed.
Lemma nth_to_seq a i : nth (default a) (to_seq a) (to_nat i) = a.[i].
Proof.
case: (boolP (i < length a)) => [Hlt | /negbTE Hlt].
  rewrite /to_seq nth_mkseq ?to_natK // -ltEint //.
rewrite nth_default ?get_out_of_bounds //.
by rewrite size_to_seq -leEint Order.TotalTheory.leNgt Hlt.
Qed.

Local Lemma size_max_wBnat s : (size s <= to_nat max_length -> size s < wBnat)%N.
Proof. move/leq_ltn_trans; apply; exact: lt_max_lenght_wB. Qed.

Lemma default_from_seq s d : default (from_seq s d) = d.
Proof.
apply: (for_loop_simple_ind (invar := fun i la => default la.2 = d)) => //=.
- by move=> i [l a] r <- /=; rewrite default_set.
- exact: default_make.
- exact: le0x.
Qed.

Lemma length_from_seq s d :
  size s <= to_nat max_length -> length (from_seq s d) = of_nat (size s).
Proof.
move=> Hsz.
apply: (for_loop_simple_ind
          (invar := fun i la => length la.2 = of_nat (size s))) => //=.
- by move=> i [l a] r <- /=; rewrite length_set.
- rewrite length_make -[_ ≤? max_length]/(_ <= max_length)%O leEint.
  by rewrite of_natK ?size_max_wBnat // -leEnat Hsz.
- exact: le0x.
Qed.

Lemma get_from_seq s d i :
  size s <= to_nat max_length -> nth d s (to_nat i) = (from_seq s d).[i].
Proof.
move=> H.
have ltsz : of_nat (size s) <= max_length.
  by rewrite leEint of_natK ?size_max_wBnat.
have ltiE j : j < of_nat (size s) = (to_nat j < size s)%N.
  by rewrite -{2}(@of_natK (size s)) -?ltEint; last by rewrite size_max_wBnat ?gei.
case: (boolP (i < of_nat (size s))) => [| gei].
  pose IH i la := [/\ length la.2 = of_nat (size s),
      la.1 = drop (to_nat i) s &
        forall j, j < i -> nth d s (to_nat j) = la.2.[j]].
  rewrite /from_seq; set loop := (X in X.2); move: i.
  suff : IH (of_nat (size s)) loop by rewrite /IH /= => [[]].
  apply (for_loop_simple_ind (invar := IH)) => {loop}.
  - rewrite {}/IH => i [l a] lti //= [/[dup] Hlena <- {l}->] Hnth.
    split; first by rewrite length_set.
      rewrite to_nat_succ; first last.
        by apply: (leq_ltn_trans _ (size_max_wBnat H)); rewrite -ltiE.
      by rewrite -drop1  drop_drop add1n.
    have -> : head d (drop (to_nat i) s) = nth d s (to_nat i).
      by rewrite -nth0 nth_drop addn0.
    move=> j /ltSleint; rewrite le_eqVlt => /orP[/eqP ->|/[dup]/Hnth -> ltji].
      by rewrite get_set_same // Hlena.
    by rewrite get_set_other //; apply/eqP; rewrite gt_eqF.
  - split => [||j]; rewrite ?drop0 // ?ltx0 //.
    by rewrite length_make -[_ ≤? _]/(_ <= max_length) ltsz.
  - exact: le0x.
rewrite get_out_of_bounds; first last.
  by rewrite length_from_seq //; apply: negbTE.
by rewrite default_from_seq nth_default // leqNgt -ltiE.
Qed.
Lemma from_seqK s d :
  size s <= to_nat max_length -> to_seq (from_seq s d) = s.
Proof.
move=> H.
have eqsz : size (to_seq (from_seq s d)) = size s.
  by rewrite size_to_seq length_from_seq // of_natK ?size_max_wBnat.
apply: (eq_from_nth (x0 := d) eqsz).
rewrite eqsz => i lti.
have /of_natK eqi : (i < wBnat)%N by apply: (ltn_trans lti); apply: size_max_wBnat.
rewrite -[in LHS]eqi -{1}(default_from_seq s d) nth_to_seq.
by rewrite -get_from_seq // eqi.
Qed.
Lemma to_seqK a : from_seq (to_seq a) (default a) = a.
Proof.
have to_natle : to_nat (length a) <= to_nat max_length.
  by rewrite -[_ <= _]/(_ <= _)%N -leEint; exact: leb_length.
have eqlen : length (from_seq (to_seq a) (default a)) = length a.
  by rewrite length_from_seq size_to_seq ?to_natK.
apply: array_ext; rewrite ?eqlen ?default_from_seq // => i lti.
have {}lti : i < length a by [].
by rewrite -get_from_seq ?size_to_seq // nth_to_seq.
Qed.

End ToSeq.


Section FoldL.

Context {T R : Type} (f : R -> T -> R) (z : R) (a : array T).
Implicit Types (i j m n len : int).

Definition foldl_array :=
  for_loop_simple (fun i r => f r a.[i]) 0 (length a) z.

Lemma foldl_arrayE : foldl_array = foldl f z (to_seq a).
Proof.
pose A n := foldl f z (take (to_nat n) (to_seq a)).
transitivity (A (length a)); last by rewrite /A -size_to_seq take_size.
apply: (for_loop_simple_ind (invar := fun n r => r = A n)).
- move=> i x; rewrite ltEint => leli {x}->.
  rewrite {}/A to_nat_succ; last exact: (leq_ltn_trans leli (lt_lenght_wB _)).
  rewrite (take_nth (default a)) ?size_mkseq //.
  by rewrite foldl_rcons nth_mkseq // to_natK.
- by rewrite {}/A to_nat0 take0.
- exact: le0x.
Qed.

End FoldL.


Section Test.

Let taille := 10000.
Let a := make_array 0 taille (fun i => i).

Goal has_array (fun i => (i > 2000000000)%O) a = false.
Proof. by vm_cast_no_check (erefl false). Qed.
Goal has_array (fun i => (i > 2000000000)%O) a = false.
Proof. by native_cast_no_check (erefl false). Qed.


Goal foldl_array add 0 a = 49995000.
Proof. by vm_cast_no_check (erefl 49995000). Qed.

End Test.
