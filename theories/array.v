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
From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63 PArray.
From Coq Require Import Program.Wf.

From mathcomp Require Import all_ssreflect.

Require Import int_seq sizelexi fastcert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Order.POrderTheory.

Local Open Scope uint63_scope.


Local Notation wBnat := (BinInt.Z.to_nat wB).

Lemma lt_lenght_wB (T : Type) (a : array T) : to_nat (length a) < wBnat.
Proof.
have /leq_ltn_trans : to_nat (length a) <= to_nat max_length.
  by rewrite -leintE; exact: leb_length.
by apply; apply/ssrnat.ltP/Z2Nat.inj_lt.
Qed.


(* iteri n g x0 == g n.-1 (g ... (g 0 x0)) *)
Section IterTailRecursive.

Context {S : Type}.
Implicit Types (n : nat) (f : nat -> S -> S) (x : S).

Definition iteritl n f x0 : S :=
  let fix aux res m i :=
    if m is m'.+1 then aux (f i res) m' i.+1
    else res
  in aux x0 n 0%N.

Lemma iteritlS n f x0 : iteritl n.+1 f x0 = f n (iteritl n f x0).
Proof.
have shift m g y : iteritl m.+1 g y = iteritl m (g \o succn) (g 0%N y).
  by rewrite /iteritl /=; elim: m g y 0%N.
by rewrite shift; elim: n f x0 => //= n IHn f x0; rewrite !shift.
Qed.
Lemma iteritlE n f x0 : iteritl n f x0 = iteri n f x0.
Proof. by elim: n => //= n <-; rewrite iteritlS. Qed.

End IterTailRecursive.


Section IterInt.

Context {S : Type}.
Implicit Types (n : int) (f : int -> S -> S) (x : S).

Definition iterint n f x0 : S :=
  let fix aux res m i :=
    if m is m'.+1 then aux (f i res) m' (succ i)
    else res
  in aux x0 (to_nat n) 0.

Lemma interintE n f x0 :
  iterint n f x0 = iteri (to_nat n) (fun i => f (of_nat i)) x0.
Proof.
rewrite -iteritlE /iterint /iteritl -(to_natK 0) to_nat0.
elim: (to_nat n) 0%N x0 => // i IHi n0 x0.
by rewrite -IHi succ_of_nat.
Qed.

End IterInt.


Local Open Scope order_scope.

Section ForLoop.

Context {A B : Type}.
Implicit Types (m n i j : int) (x y : A).

Inductive loopresult := | Continue of A | Return of B.

Variables (finish : A -> B) (body : (int -> A -> loopresult)).

Lemma for_loop_rec_subproof m n : m < n -> n - succ m < n - m.
Proof.
move=> /[dup] ltmn /ltW lemn; rewrite ltintE.
have leSmn : succ m <= n by apply ltleSint.
rewrite [X in (_ < X)%N]to_natB // [X in (X < _)%N]to_natB //.
rewrite ltn_sub2lE -?leintE //.
rewrite -{2}(to_natK m) succ_of_nat of_natK; first by rewrite ltnS.
move: ltmn; rewrite ltintE => /leq_ltn_trans; apply.
exact: ltwBnat.
Qed.

Fixpoint for_loop_rec m n x0
    (ACC : Acc (fun m n => m <? n) (n - m)) {struct ACC} : B :=
  match (decP (@idP (m <? n))) with
  | right _  => finish x0
  | left pf  =>
      match body m x0 with
      | Return res => res
      | Continue a =>
          for_loop_rec a (Acc_inv ACC (for_loop_rec_subproof pf))
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
case (@idP (m <? n)) => //= ltmn.
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

Lemma for_loop_ind m n x0 (PA : int -> A -> Type) (PB : B -> Type) :
  (forall i x, n <= i -> PA i x -> PB (finish x)) ->
  (forall i x r, i < n -> body i x = Return r   -> PA i x -> PB r) ->
  (forall i x c, i < n -> body i x = Continue c -> PA i x -> PA (succ i) c) ->
  PA m x0 -> PB (for_loop m n x0).
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
  for_loop id (fun i a => Continue a.[i <- f i]) 0 len (make len d).
Definition find_array : int :=
  for_loop (fun=> length a)
    (fun i _ => if p a.[i] then Return i else Continue tt)
    0 (length a) tt.
Definition has_array : bool :=
  for_loop xpred0
    (fun i _ => if p a.[i] then Return true else Continue tt)
    0 (length a) tt.

Lemma length_make_array d len f :
  len <= max_length -> length (make_array d len f) = len.
Proof.
rewrite /make_array => lelen; pose P (ar : array A) := length ar = len.
apply: (for_loop_ind (PA := fun i ar => P ar) (PB := P)) => //.
- by rewrite {}/P => i c x _ [] <- <-; rewrite length_set.
- by rewrite {}/P length_make -[len ≤? max_length]/(len <= max_length)%O lelen.
Qed.
Lemma default_make_array d len f : default (make_array d len f) = d.
Proof.
rewrite /make_array; pose P (ar : array A) := default ar = d.
apply: (for_loop_ind (PA := fun i a => P a) (PB := P)) => //.
- by rewrite {}/P => i c x _ [] <- <-; rewrite default_set.
- by rewrite {}/P default_make.
Qed.
Lemma get_make_array len d f i :
  i < len <= max_length -> (make_array d len f).[i] = f i.
Proof.
rewrite /make_array => /andP[ltil lelen]; set body := (X in for_loop _ X).
pose IH n ar := length ar = len /\ forall j, j < n -> ar.[j] = f j.
apply (for_loop_ind (PA := IH) (PB := fun ar => IH len ar)) => //.
- rewrite /IH => j ar leli [Hlen Heq]; split => // k ltkl.
  exact: Heq (lt_le_trans ltkl leli).
- rewrite /body {}/IH => j x c ltjl [] {c}<- [lenx Heq].
  rewrite length_set; split => // k /ltSleint.
  rewrite le_eqVlt => /orP[/eqP {k}-> | ltki].
    by rewrite get_set_same ?lenx.
  rewrite get_set_other ?Heq //.
  by apply/eqP; move: ltki; rewrite lt_def => /andP[].
- split => [|j]; last by rewrite ltintE to_nat0.
  by rewrite length_make -[len ≤? max_length]/(len <= max_length) lelen.
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
apply: (for_loop_ind (PA := fun i _ => IH i) (PB := IH)).
- rewrite {}/IH => i _ gti H j ltj.
  exact: H (lt_le_trans ltj gti).
- rewrite {}/IH => i x r lti.
  by case: (boolP (p a.[i])) => Hp // [{r}<-].
- rewrite {}/IH => i c x lti.
  case: (boolP (p a.[i])) => Hp // _ H j /ltSleint.
  by rewrite le_eqVlt => /orP[/eqP -> // | /H].
- by move=> j; rewrite {}/IH ltintE to_nat0.
Qed.
Lemma find_arrayE : find_array < length a -> p a.[find_array].
Proof.
rewrite /find_array; set body := (X in for_loop _ X) => H.
apply/contraLR: H; rewrite -leNgt.
move: 0 (le0x _ : 0 <= length a) => j.
apply: (for_loop_ind (PA := fun i _ => _)
          (PB := fun b => ~~ p a.[b] -> length a <= b)) => //.
- rewrite /body=> i x r ltil.
  by case: (boolP (p a.[i])) => // /[swap]-[{r}<- ->].
- by rewrite /body=> i x c /ltleSint ltil; case: p.
Qed.

Lemma has_arrayP : reflect (exists2 n : int, n < length a & p a.[n]) has_array.
Proof.
suff /equivP : reflect (exists2 n, 0 <= n < length a & p a.[n]) has_array.
  by apply; split => [][x xin pax]; exists x =>[]//; move: xin; rewrite le0x.
rewrite /= /has_array; set body := (X in for_loop _ X).
apply (iffP idP).
  apply: (for_loop_ind (body := body)
            (PA := fun _ _ => true) (PB := fun b => b -> _)) => //.
  rewrite {}/body => i _ r lti + _ _.
  case: (boolP (p a.[i])) => Hp // [] _.
  by exists i => //; rewrite le0x lti.
move=> [i /andP[_ lti] pai].
have : for_loop xpred0 body i (length a) tt.
  by apply: for_loop_retE => //; rewrite {}/body pai.
apply: contraLR; move: 0 (le0x i : 0 <= i) => j.
apply (for_loop_ind (body := body) (m := j)
          (PA := fun j _ => _) (PB := fun b => ~~ b -> _)) => // {j}.
- by move=> j _ /le_trans/[apply]/le_lt_trans/(_ lti); rewrite ltxx.
- by rewrite /body => j x r _; case: p => // [][<-{r}].
- rewrite /body=> j x c _ /[swap].
  by rewrite le_eqVlt => /orP[/eqP{j}-> | /ltleSint]; first by rewrite pai.
Qed.

End ArrayManip.


Section Test.

Let taille := 1000000.
Let a := make_array 0 taille (fun i => i).
Time Eval vm_compute in has_array (fun i => (i > 2000000000)%O) a.
Time Eval native_compute in has_array (fun i => (i > 2000000000)%O) a.

End Test.


Section ToSeq.

Context {S : Type}.
Implicit Type (a : array S) (s : seq S).

(* Definition to_seq a := array_foldr cons [::] a. *)
Definition to_seq a := mkseq (fun i => a.[of_nat i]) (to_nat (length a)).
Definition from_seq s d :=
  make_array d (of_nat (size s)) (fun i => nth d s (to_nat i)).

Lemma size_to_seq a : size (to_seq a) = to_nat (length a).
Proof. by rewrite /to_seq size_mkseq. Qed.
Lemma nth_to_seq a i : nth (default a) (to_seq a) (to_nat i) = a.[i].
Proof.
case: (boolP (i < length a)) => [Hlt | /negbTE Hlt].
  rewrite /to_seq nth_mkseq ?to_natK // -ltintE //.
rewrite nth_default ?get_out_of_bounds //.
by rewrite size_to_seq -leintE Order.TotalTheory.leNgt Hlt.
Qed.

End ToSeq.

