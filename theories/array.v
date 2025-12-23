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

Definition continue r := if r is Continue _ then true else false.

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

Definition decP_inline P b (Pb : reflect P b) : decidable P :=
  (if b as b0 return (if b0 then P else ~ P) -> decidable P
   then [eta left]
   else [eta right]) (decPcases Pb).

Fixpoint for_loop_rec m n x0
    (ACC : Acc (fun m n => m <? n) (n - m)) {struct ACC} : B :=
  match decP_inline (@idP (m <? n)) with
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
case decP_inline => //= ltmn.
apply: (IHd _ _ _ (erefl _)).
by rewrite Hd for_loop_rec_subproof.
Qed.
Lemma for_loop_recE m n x0 ACC : @for_loop_rec m n x0 ACC = for_loop m n x0.
Proof. exact: for_loop_rec_accE. Qed.
Lemma for_loop_retE m n x0 res :
  m < n -> body m x0 = Return res -> for_loop m n x0 = res.
Proof.
rewrite /for_loop; case: (Acc_intro_generator _ _ _) => /= ACC ltmn ->.
by rewrite ltbE ltmn.
Qed.
Lemma for_loop_contE m n x0 val :
  m < n -> body m x0 = Continue val ->
  for_loop m n x0 = for_loop (succ m) n val.
Proof.
rewrite {1}/for_loop; case: (Acc_intro_generator _ _ _) => ACC ltmn Heq /=.
rewrite -[m <? n]/(m < n) Heq; move: ltmn. (* Why ltbE doesn't work ? *)
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
- rewrite (for_loop_contE ltmn Hnext); apply: (IHd _ _ _ (erefl _)).
  + by rewrite Hd for_loop_rec_subproof.
  + exact: (Hcont _ _ _ ltmn Hnext).
- rewrite (for_loop_retE ltmn Hnext).
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


Section ForLoop2.

Context {A1 B1 A2 B2 : Type}.
Implicit Types (m n i j : int).
Variables (body1 : (int -> A1 -> @loopresult A1 B1)) (finish1 : A1 -> B1)
          (body2 : (int -> A2 -> @loopresult A2 B2)) (finish2 : A2 -> B2)
          (invar : int -> A1 -> A2 -> Type) (postcond : B1 -> B2 -> Type).


Section Shift.

Variables (m1 n1 shift : int).
Hypotheses
  (Hsync : forall i x y, invar i x y ->
                         continue (body1 i x) = continue (body2 (i + shift) y))
  (Hpost : forall x y, invar n1 x y -> postcond (finish1 x) (finish2 y))
  (Hret : forall i x y r s, i < n1 ->
                            body1 i x = Return r ->
                            body2 (i + shift) y = Return s ->
                            invar i x y -> postcond r s)
  (Hcont : forall i x y c d, i < n1 ->
                             body1 i x = Continue c ->
                             body2 (i + shift) y = Continue d
                             -> invar i x y -> invar (succ i) c d).

Lemma for_loop_rel_le_shift_postcond x0 y0 :
  (to_nat n1 + to_nat shift < wBnat)%N ->
  invar m1 x0 y0 -> m1 <= n1 ->
  postcond (for_loop body1 finish1 m1 n1 x0)
    (for_loop body2 finish2 (m1 + shift) (n1 + shift) y0).
Proof.
move=> Hn1.
have ltmshift m : m < n1 -> m + shift < n1 + shift.
  move=> ltm; rewrite ltEint to_natD; first last.
    by apply: (ltn_trans _ Hn1); rewrite ltn_add2r -ltEint.
  by rewrite (to_natD Hn1) ltn_add2r -ltEint.
move: {1}(n1 - m1) (erefl (n1 - m1)) => d Hd.
elim/(well_founded_induction_type wf_ltint): d m1 Hd x0 y0 => d IHd m Hd x0 y0 Px0.
case (ltP m n1) => [ltm _ | gem lem]; first last.
  have {lem gem} eqm : m = n1 by apply: le_anti; rewrite lem gem.
  rewrite eqm /= !for_loop_finishE ?ltxx //.
  by apply: Hpost; rewrite -eqm.
case Hnext1 : (body1 m x0) => [a | a].
- rewrite (for_loop_contE _ ltm Hnext1).
  have := Hsync Px0; rewrite Hnext1 /=.
  case Hnext2 : (body2 _ y0) => [b | //] _.
  rewrite (for_loop_contE _ (ltmshift m ltm) Hnext2).
  have -> : succ (m + shift) = succ m + shift by rewrite /succ; ring.
  apply: (IHd _ _ _ (erefl _)).
  + by rewrite Hd for_loop_rec_subproof.
  + exact: (Hcont ltm Hnext1 Hnext2).
  + exact: ltleSint.
- rewrite (for_loop_retE _ ltm Hnext1).
  have := Hsync Px0; rewrite Hnext1 /=.
  case Hnext2 : (body2 _ y0) => [//| b] _.
  rewrite (for_loop_retE _ (ltmshift m ltm) Hnext2).
  exact: (Hret ltm Hnext1 Hnext2).
Qed.

End Shift.

Section NoShift.

Variables (m n : int).
Hypotheses
  (Hsync : forall i x y, invar i x y ->
                         continue (body1 i x) = continue (body2 i y))
  (Hpost : forall x y, invar n x y -> postcond (finish1 x) (finish2 y))
  (Hret : forall i x y r s, i < n ->
                            body1 i x = Return r ->
                            body2 i y = Return s ->
                            invar i x y -> postcond r s)
  (Hcont : forall i x y c d, i < n ->
                             body1 i x = Continue c ->
                             body2 i y = Continue d
                             -> invar i x y -> invar (succ i) c d).

Lemma for_loop_rel_le_postcond x0 y0 :
  invar m x0 y0 -> m <= n ->
  postcond (for_loop body1 finish1 m n x0) (for_loop body2 finish2 m n y0).
Proof.
have addi0 (i : int) : i + 0 = i by ring.
rewrite -{4}(addi0 m) -{3}(addi0 n).
apply: for_loop_rel_le_shift_postcond => //.
- by move=> i x y; rewrite addi0 => /Hsync.
- by move=> i x y r s; rewrite addi0; apply: Hret.
- by move=> i x y c d; rewrite addi0; apply: Hcont.
- by rewrite to_nat0 addn0 ltwBnat.
Qed.

End NoShift.

End ForLoop2.


Section FoldInt.

Context {A : Type} (body : (int -> A -> A)).
Implicit Types (m n i j : int) (x y : A).

Fixpoint foldint_rec m n x0
    (ACC : Acc (fun m n => m <? n) (n - m)) {struct ACC} : A :=
  match (decP_inline (@idP (m <? n))) with
  | right _ => x0
  | left pf =>
      foldint_rec (body m x0) (Acc_inv ACC (for_loop_rec_subproof pf))
  end.
Definition foldint m n x0 :=
  foldint_rec x0 (Acc_intro_generator 40 wf_ltint (n - m)).

Lemma foldint_recE m n x0 :
  forall (acc1 acc2 : Acc (fun m n => m <? n) (n - m)),
  foldint_rec x0 acc1 =
    for_loop_rec (fun i a => Continue (body i a)) id x0 acc2.
Proof.
move: {1}(n - m) (erefl (n - m)) => d Hd.
elim/(well_founded_induction_type wf_ltint): d m Hd x0 => d IHd m Hd x0.
case => /= acc1; case => /= acc2.
case: (boolP (m < n)) => [ltmn | gemn] /=; first last.
  by case: decP_inline => // H; exfalso; move: H gemn; rewrite ltbE => ->.
case: decP_inline => // H; apply: (IHd (Uint63.pred d)).
  rewrite ltEint -ltnS succ_subint1E // {}Hd.
  apply/negP => /eqP/(congr1 (fun i => to_nat i))/eqP.
  rewrite to_nat0 to_natB; last exact: ltW.
  by rewrite -/(_ <= _)%N leqNgt -ltEint ltmn.
by rewrite {d IHd}Hd /succ /Uint63.pred; ring.
Qed.
Lemma foldintE m n x0 :
  foldint m n x0 = for_loop (fun i a => Continue (body i a)) id m n x0.
Proof. exact: foldint_recE. Qed.

Lemma foldint_ind m n x0 (invar : int -> A -> Type) :
  (forall i x, i < n -> invar i x -> invar (succ i) (body i x)) ->
  invar m x0 -> m <= n -> invar n (foldint m n x0).
Proof.
move=> Hrec Hx0 lemn; rewrite foldintE.
by apply: for_loop_ind_le => // i x c ltin [{c}<-] /(Hrec _ _ ltin).
Qed.

End FoldInt.


Section AllInt.

Implicit Type (P : pred int) (i j m n : int).
Definition allint P m n :=
  for_loop (fun i _ => if P i then Continue tt else Return false) xpredT m n tt.

Lemma allintNP P m n :
  reflect (exists2 i : int, m <= i < n & ~~ P i) (~~ allint P m n).
Proof.
rewrite /allint; set body := (X in for_loop X); apply (iffP idP).
- apply: (for_loop_ind_postcond (body := body)
            (invar := fun i _ => m <= i) (postcond := fun r => ~~ r -> _)) => //.
  + rewrite {}/body => i _ r ltin.
    case: (boolP (P i)) => Hpi // [{r}<-] lemi _.
    by exists i; rewrite // lemi ltin.
  + rewrite {}/body => i c d ltin _ /le_trans; apply.
    rewrite leEint to_nat_succ ?leqnSn //.
    by apply: (leq_trans _ (ltwBnat n)); rewrite ltnS -ltEint.
- move=> [i0 /andP[lemi0 lti0m] /negbTE NPi0].
  have : ~~ for_loop body xpredT i0 n tt.
    by apply: negbT; apply: for_loop_retE => //; rewrite {}/body NPi0.
  apply: contra; move: lemi0.
  apply: (for_loop_ind_postcond (body := body)
            (invar := fun _ _ => _) (postcond := fun b => b -> _)) => //.
  + move=> j _ /le_trans/[apply] ltni0 _.
    by rewrite for_loop_finishE // -leNgt.
  + by rewrite /body => j x r _; case: (P j) => // [][<-{r}].
  + rewrite /body=> j x c _ /[swap].
    rewrite le_eqVlt => /orP[/eqP{j}-> | /ltleSint + _ //].
    by rewrite NPi0.
Qed.


Lemma allintP P m n : reflect (forall i, m <= i < n -> P i) (allint P m n).
Proof.
apply: introP.
- move=> H i Hi; move: H; apply: contraLR => NPi.
  by apply/allintNP; exists i.
- by move/allintNP => [i Hi NPi] /(_ i Hi); rewrite (negbTE NPi).
Qed.

End AllInt.


Section ArrayManip.

Context {A : Type} (P : A -> bool) (a : array A).
Implicit Types (i j m n len : int).

Definition make_array (d : A) (len : int) (f : int -> A) :=
  foldint (fun i a => a.[i <- f i]) 0 len (make len d).
Definition find_array : int :=
  for_loop (fun i _ => if P a.[i] then Return i else Continue tt)
           (fun=> length a) 0 (length a) tt.
Definition all_array : bool := allint (fun i => P a.[i]) 0 (length a).
Definition has_array : bool := ~~ allint (fun i => ~~ P a.[i]) 0 (length a).

Lemma length_make_array d len f :
  len <= max_length -> length (make_array d len f) = len.
Proof.
rewrite /make_array => le.
apply: (foldint_ind (invar := fun i ar => length ar = len)) => //.
- by move=> i c _ <-; rewrite length_set.
- by rewrite length_make -[len ≤? max_length]/(len <= max_length)%O le.
Qed.
Lemma default_make_array d len f : default (make_array d len f) = d.
Proof.
apply: (foldint_ind (invar := fun i ar => default ar = d)) => //.
- by move=> i x _ <-; rewrite default_set.
- by rewrite default_make.
Qed.
Lemma get_make_array len d f i :
  i < len <= max_length -> (make_array d len f).[i] = f i.
Proof.
rewrite /make_array => /andP[ltil lelen].
apply (foldint_ind
    (invar := fun n ar => length ar = len /\ forall j, j < n -> ar.[j] = f j)) => //.
- move=> j x ltjl [lenx Heq].
  rewrite length_set; split => // k /ltSleint.
  rewrite le_eqVlt => /orP[/eqP {k}-> | ltki].
    by rewrite get_set_same ?lenx.
  rewrite get_set_other ?Heq //.
  by apply/eqP; move: ltki; rewrite lt_def => /andP[].
- split => [|j]; last by rewrite ltEint to_nat0.
  by rewrite length_make -[len ≤? max_length]/(len <= max_length) lelen.
Qed.
Lemma make_arrayE : make_array (default a) (length a) (get a) = a.
Proof.
have lena : length a <= max_length by exact: leb_length.
apply: array_ext; rewrite ?length_make_array //.
- by move=> i lti ; rewrite get_make_array // lena andbT.
- by rewrite default_make_array.
Qed.

Lemma find_array_ltn n : n < find_array -> ~~ P a.[n].
Proof.
rewrite /find_array; pose IH i := forall j, j < i -> ~~ P a.[j].
apply: (for_loop_ind_le_postcond (invar := fun i _ => IH i) (postcond := IH)) => //.
- rewrite {}/IH => i x r lti.
  by case: (boolP (P a.[i])) => Hp // [{r}<-].
- rewrite {}/IH => i c x lti.
  case: (boolP (P a.[i])) => Hp // _ H j /ltSleint.
  by rewrite le_eqVlt => /orP[/eqP -> // | /H].
- by move=> j; rewrite {}/IH ltEint to_nat0.
Qed.
Lemma find_arrayE : find_array < length a -> P a.[find_array].
Proof.
rewrite /find_array; apply/contraLR; rewrite -leNgt.
move: 0 (le0x _ : 0 <= length a) => j.
apply: (for_loop_ind_postcond (invar := fun i _ => i <= length a)
          (postcond := fun b => ~~ P a.[b] -> length a <= b)) => //.
- move=> i x r ltil.
  by case: (boolP (P a.[i])) => // /[swap]-[{r}<- ->].
- by move=> i x c /ltleSint ltil; case: P.
Qed.

Lemma all_arrayP : reflect (forall n : int, n < length a -> P a.[n]) all_array.
Proof.
apply (iffP (allintP _ _ _)) => [H n lt| H n /andP[_ /H] //].
by apply: H; rewrite le0x lt.
Qed.

Lemma has_arrayP : reflect (exists2 n : int, n < length a & P a.[n]) has_array.
Proof.
apply (iffP (allintNP _ _ _)) => -[i].
- by rewrite negbK => /andP[_ lti] Pai; exists i.
- by move=> lti Pai; exists i; rewrite ?negbK // lti le0x.
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
  (foldint (fun i tls_ar =>
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
apply: (foldint_ind (invar := fun i la => default la.2 = d)) => //=.
- by move=> i [l a] r <- /=; rewrite default_set.
- exact: default_make.
Qed.

Lemma length_from_seq s d :
  size s <= to_nat max_length -> length (from_seq s d) = of_nat (size s).
Proof.
move=> Hsz.
apply: (foldint_ind
          (invar := fun i la => length la.2 = of_nat (size s))) => //=.
- by move=> i [l a] r <- /=; rewrite length_set.
- rewrite length_make -[_ ≤? max_length]/(_ <= max_length)%O leEint.
  by rewrite of_natK ?size_max_wBnat // -leEnat Hsz.
Qed.

Lemma get_from_seq s d i :
  (size s <= to_nat max_length)%N -> nth d s (to_nat i) = (from_seq s d).[i].
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
  apply (foldint_ind (invar := IH)) => {loop}.
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
  (size s <= to_nat max_length)%N -> to_seq (from_seq s d) = s.
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
have to_natle : (to_nat (length a) <= to_nat max_length)%N.
  by rewrite -leEint; exact: leb_length.
have eqlen : length (from_seq (to_seq a) (default a)) = length a.
  by rewrite length_from_seq size_to_seq ?to_natK.
apply: array_ext; rewrite ?eqlen ?default_from_seq // => i lti.
have {}lti : i < length a by [].
by rewrite -get_from_seq ?size_to_seq // nth_to_seq.
Qed.

End ToSeq.


Section ArrayEqType.

Context {S : eqType}.
Implicit Type (i : int) (a : array S) (s : seq S).

Lemma mem_to_seqP a x :
  reflect (exists2 i : int, i < length a & a.[i] = x) (x \in to_seq a).
Proof.
apply (iffP idP) => [/(nthP (default a))[n] | [i lti {x}<-]]; first last.
  by rewrite -nth_to_seq mem_nth // size_to_seq -ltEint.
rewrite size_to_seq => ltn {x}<-.
have /of_natK eqn : (n < wBnat)%N by apply: (ltn_trans ltn (ltwBnat _)).
exists (of_nat n); first by rewrite ltEint eqn.
by rewrite -nth_to_seq eqn.
Qed.

Lemma forall_mem_to_seq (P : S -> Prop) a :
  (forall i, i < length a -> P a.[i]) <-> (forall x : S, x \in to_seq a -> P x).
Proof.
split => [H x -/mem_to_seqP [i {}/H H {x}<-] // | H i lti].
by apply/H/mem_to_seqP; exists i.
Qed.

Definition eq_array_cont a1 a2 :
  allint (fun i => a1.[i] == a2.[i]) 0 (length a1) ->
  forall i, i < length a1 -> a1.[i] = a2.[i].
Proof. by move/allintP => H i lti; apply/eqP/H; rewrite le0x. Qed.

Definition eq_array a1 a2 :=
  [&& length a1 == length a2,
    locked (allint (fun i => a1.[i] == a2.[i]) 0 (length a1)) &
      default a1 == default a2].
Lemma eqarray_subproof : Equality.axiom eq_array.
Proof.
rewrite /eq_array=> a1 a2; apply (iffP idP) => [|->].
- move/and3P=> [/eqP eqlen + /eqP eqdef].
  unlock => /eq_array_cont Heq.
  exact: array_ext.
- rewrite !eqxx /= andbT; unlock; exact/allintP.
Qed.
HB.instance Definition _ := hasDecEq.Build (array S) eqarray_subproof.

End ArrayEqType.


Section FoldL.

Context {T R : Type} (f : R -> T -> R) (z : R) (a : array T).
Implicit Types (i j m n len : int).

Definition foldl_array := foldint (fun i acc => f acc a.[i]) 0 (length a) z.
Definition foldscanl_array :=
  foldint (fun i acc_a =>
                     let: (acc, ar) := acc_a in
                     let newacc := f acc a.[i] in
                     (newacc, ar.[i <- newacc]))
    0 (length a) (z, make (length a) z).
Definition scanl_array := foldscanl_array.2.

Lemma foldl_foldscanl_arrayE : foldl_array = foldscanl_array.1.
Proof.
rewrite /foldl_array /foldscanl_array.
rewrite !foldintE.
apply (for_loop_rel_le_postcond (invar := fun i ar1 ar2 => ar1 = ar2.1)) => //.
- by move=> i x [r ra] y [s sb] lti [{y}<-] [{s}<-] /= _ {x}->.
Qed.

Local Lemma foldscanl_arrayE :
  foldl_array = foldl f z (to_seq a) /\
  to_seq scanl_array = scanl f z (to_seq a).
Proof.
rewrite foldl_foldscanl_arrayE /scanl_array /foldscanl_array.
set scanpair := foldint _ _ _ _.
pose FL n := foldl f z (take (to_nat n) (to_seq a)).
pose SC n := scanl f z (take (to_nat n) (to_seq a)).
pose invar i (p : R * array R) :=
  let (fl, sc) := p in
  [/\ length sc = length a, default sc = z,
    fl = FL i
    & take (to_nat i) (to_seq sc) = SC i].
suff : invar (length a) scanpair.
  case: scanpair => [v b] /= [eqlen _ {v}->].
  by rewrite -{1}eqlen {invar}/SC{}/FL -!size_to_seq !take_size.
apply: foldint_ind => {scanpair} .
- move=> i [fl sc]; rewrite ltEint => leli.
  rewrite {}/invar{}/FL{}/SC=> -[eqlen eqdef eqfl eqtake].
  rewrite to_nat_succ; last exact: (leq_ltn_trans leli (lt_lenght_wB _)).
  rewrite (take_nth (default a)) ?size_mkseq //.
  split.
  - by rewrite length_set.
  - by rewrite default_set.
  - by rewrite foldl_rcons nth_mkseq // to_natK eqfl.
  rewrite scanl_rcons foldl_rcons nth_mkseq // to_natK eqfl.
  rewrite -eqtake (take_nth z); first last.
    by rewrite size_mkseq length_set eqlen.
  congr rcons.
    apply (eq_from_nth (x0 := z)) => [| n].
      by rewrite !size_take !size_to_seq !length_set eqlen.
    rewrite !size_take !size_to_seq !length_set eqlen leli => leni.
    have /of_natK eqn : (n < wBnat)%N.
      exact: (leq_trans leni (ltnW (ltwBnat i))).
    rewrite !nth_take // -{1 3}eqdef -eqfl -eqn nth_to_seq.
    have -> : default sc = default sc.[i<-f fl a.[i]] by rewrite default_set.
    rewrite nth_to_seq get_set_other //.
    by apply/eqP; rewrite gt_eqF // ltEint eqn.
  rewrite -{1}eqdef -eqfl.
  have -> : default sc = default sc.[i<-f fl a.[i]] by rewrite default_set.
  rewrite nth_to_seq get_set_same // eqlen.
  by move: leli; rewrite -ltEint.
- rewrite /invar/FL/SC to_nat0 take0 /=.
  by rewrite length_make leb_length default_make take0.
- exact: le0x.
Qed.

Lemma foldl_arrayE : foldl_array = foldl f z (to_seq a).
Proof. by have [] := foldscanl_arrayE. Qed.
Lemma to_seq_scanlarrayE : to_seq scanl_array = scanl f z (to_seq a).
Proof. by have [] := foldscanl_arrayE. Qed.

End FoldL.


Section FoldR.

Context {T R : Type} (f : T -> R -> R) (z : R) (a : array T).
Implicit Types (i j m n len : int).

Definition foldr_array :=
  foldint (fun i acc => f a.[length a - (succ i)] acc) 0 (length a) z.
Lemma foldr_arrayE : foldr_array = foldr f z (to_seq a).
Proof.
pose fs u v := f v u.
transitivity (foldl fs z (rev (to_seq a))); last by rewrite foldl_rev.
have lesz : (size (rev (to_seq a)) <= to_nat max_length)%N.
  by rewrite size_rev size_to_seq -leEint; apply: leb_length.
rewrite -[rev _](from_seqK (default a)) //.
rewrite -foldl_arrayE /foldr_array /foldl_array.
rewrite length_from_seq // size_rev size_to_seq to_natK.
rewrite !foldintE.
apply: (for_loop_rel_le_postcond (invar := fun i x y => x = y)) => //.
move=> i x y c d lti [{c}<-][{d}<-] {y}<-; rewrite {}/fs; congr f.
rewrite -get_from_seq // nth_rev size_to_seq -?ltEint //.
rewrite -[X in a.[X]]to_natK -nth_to_seq to_natK; congr nth.
rewrite to_natB; last exact: ltleSint.
rewrite -/(succ i) to_nat_succ //.
move: lti; rewrite ltEint => /leq_ltn_trans; apply.
exact: lt_lenght_wB.
Qed.

End FoldR.


Section Test.

Let taille := 1000000.
Let a := make_array 0 taille (fun i => i).

Goal has_array (fun i => (i > 2000000000)%O) a = false.
Proof. by vm_cast_no_check (erefl false). Qed.
Goal has_array (fun i => (i > 2000000000)%O) a = false.
Proof. by native_cast_no_check (erefl false). Qed.


Goal foldl_array add 0 a = 499999500000.
Proof. by native_cast_no_check (erefl 499999500000). Qed.

End Test.


(*
From Coq Require Extraction ExtrOCamlInt63 ExtrOCamlPArray.
Extraction Inline add sub ltb succ decP_inline length get foldint foldint_rec.

(*
Print Extraction Inline.
Extraction Inline boolP.
Extraction Inline altP.
Extraction Inline idP.
*)

Recursive Extraction for_loop_rec.
Recursive Extraction foldl_array.
Recursive Extraction foldr_array.
*)
