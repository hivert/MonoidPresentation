(** Native int is a well founded choice and type **)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Implicit Type (x y : int).

Fact natint_eq_axiom : Equality.axiom eqb.
Proof. by move=> i j; apply (iffP idP); rewrite -eqb_spec. Qed.
HB.instance Definition _ := hasDecEq.Build int natint_eq_axiom.

Lemma le0Z x : BinInt.Z.le 0 φ(x).
Proof. by have [] := to_Z_bounded x. Qed.

Definition int_to_nat (i : int) : nat := to_nat i.
Definition nat_to_int (n : nat) : int := of_nat n.
Fact int_to_natK : cancel int_to_nat nat_to_int.
Proof.
move=> i; rewrite /int_to_nat /nat_to_int.
rewrite Z2Nat.id ?of_to_Z // -to_Z_0.
exact: le0Z.
Qed.
HB.instance Definition _ := CanIsCountable int_to_natK.

Lemma int_to_nat_inj : injective int_to_nat.
Proof. exact: can_inj int_to_natK. Qed.

Check int : countType.

Fact int_disp : Order.disp_t. by []. Qed.

Lemma leintbE x y : (x ≤? y) = (int_to_nat x <= int_to_nat y).
Proof. by apply/lebP/leP; rewrite (Z2Nat.inj_le _ _ (@le0Z x) (@le0Z y)). Qed.
Lemma int_ltbE x y : (x <? y) = (int_to_nat x < int_to_nat y).
Proof. by apply/ltbP/ltP; rewrite (Z2Nat.inj_lt _ _ (@le0Z x) (@le0Z y)). Qed.

Fact int_lt_def x y : (x <? y) = (y != x) && (x ≤? y).
Proof.
by rewrite int_ltbE leintbE -(eqtype.inj_eq int_to_nat_inj) ltn_neqAle eq_sym.
Qed.
Fact leint_refl x : (x <=? x).
Proof. by rewrite leintbE leqnn. Qed.
Fact leint_anti : antisymmetric leb.
Proof. by move=> x y; rewrite !leintbE -eqn_leq => /eqP/int_to_nat_inj. Qed.
Fact leint_trans : transitive leb.
Proof. by move=> y x z; rewrite !leintbE => /leq_trans/[apply]. Qed.
HB.instance Definition _ := Order.isPOrder.Build int_disp int
                              int_lt_def leint_refl leint_anti leint_trans.

Lemma leintE x y : (x <= y)%O = (int_to_nat x <= int_to_nat y).
Proof. exact: leintbE. Qed.
Lemma int_ltE x y : (x < y)%O = (int_to_nat x < int_to_nat y).
Proof. exact: int_ltbE. Qed.

Fact leint_total : total (<=%O : rel int).
Proof. by move=> x y; rewrite !leintE -!leEnat Order.le_total. Qed.
HB.instance Definition _ := Order.POrder_isTotal.Build int_disp int leint_total.

Fact le0int x : (0 <= x)%O.
Proof. by rewrite leintE. Qed.
HB.instance Definition _ := Order.hasBottom.Build int_disp int le0int.

Require Import present cert.

Lemma wf_ltint : well_founded (<%O : rel int).
Proof.
apply: (wf_f int_to_natK _ wf_ltnat) => x y.
by rewrite int_ltE ltEnat.
Qed.
Definition sizelexi_int_wf := sizelexi_wf wf_ltint.
Definition check_convergence_intP fuel R :
  is_Ok (check_convergence <%O fuel R) -> convergent R :=
  check_convergenceP (@lt_sizelexi_stable _ int) sizelexi_int_wf
    (fuel := fuel) (R := R).

Load "samples/largest.v".
(* Load "samples/baaabaaaba_ababa.v". *)

Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check (eq_refl true).
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.

Fixpoint eqseq_int (s1 s2 : seq int) {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => if eqb x1 x2 then eqseq_int s1' s2' else false
  | _, _ => false
  end.
Lemma eqseq_intE : @eq_op (seq int) = eqseq_int.
Proof. by []. Qed.


Fixpoint prefix_int s1 s2 {struct s2} :=
  if s1 isn't x :: s1' then true else
  if s2 isn't y :: s2' then false else
    if eqb x y then prefix_int s1' s2' else false.
Lemma prefixE : @prefix int = prefix_int.
Proof. by []. Qed.

Definition drop_int := Eval compute in @drop int.     (* 7%   speedup ?? *)
Definition cat_int := Eval compute in @cat int.       (* 3.5% speedup ?? *)
Definition size_int := Eval compute in @seq.size int. (* 4%   speedup ?? *)

Fixpoint rewrites1_front_int (R : relat int) (u : seq int) :=
  if R is (r1, r2) :: R' then
    if prefix_int r1 u then Some (cat_int r2 (drop_int (size_int r1) u))
    else rewrites1_front_int R' u
  else None.
Lemma rewrites1_front_intE : @rewrites1_front int = rewrites1_front_int.
Proof. by []. Qed.
Definition rewrites1_front_int_fast := Eval compute in rewrites1_front_int.

Definition rewrites1_int  := (* Eval compute in 25% speedup ?? 25% slowdown ?? *)
  fun R : relat int => (fix rec (u : seq int) :=
                         if u is a :: u' then
                           if rewrites1_front_int_fast R u is Some u as res then res
                           else option_map (cons a) (rec u')
                         else rewrites1_front_int_fast R [::]).
Lemma rewrites1_intE : @rewrites1 int = rewrites1_int.
Proof. by []. Qed.

Fixpoint norfuel_int R fuel u :=
  if fuel is fuel'.+1 then
    if rewrites1_int R u is Some v then norfuel_int R fuel' v else (u, true)
  else (u, false).
Lemma norfuel_intE : @norfuel int = norfuel_int.
Proof. by []. Qed.

Definition all_spairs_rule_int (r1 r2 s1 s2 : seq int) :=
  [seq (r2 ++ drop (seq.size r1 - shift) s1, take shift r1 ++ s2) |
    shift <- iota 0 (seq.size r1) & prefix_int (drop shift r1) s1].
Definition all_spairs_int R :=
  flatten [seq all_spairs_rule_int r.1 r.2 s.1 s.2 | r <- R, s <- R].
Definition all_npairs_rule_int (r1 r2 s1 s2 : seq int) :=
  [seq (r2, take shift r1 ++ s2 ++ drop (shift + seq.size s1) r1) |
    shift <- iota 0 (seq.size r1 - seq.size s1).+1 &
      eqseq_int s1 (take (seq.size s1) (drop shift r1))].
Definition all_npairs_int R :=
  flatten [seq all_npairs_rule_int r.1 r.2 s.1 s.2 | r <- R, s <- R].
Lemma all_spairs_intE : @all_spairs int = all_spairs_int.
Proof. by []. Qed.
Lemma all_npairs_intE : @all_npairs int = all_npairs_int.
Proof. by []. Qed.

Definition eqbool b1 b2 := Eval compute in addb (~~ b1) b2.
Definition eqnor R fuel (p : word int * word int) :=
  let x1 := norfuel_int R fuel p.1 in
  let x2 := norfuel_int R fuel p.2 in
  if eqseq_int x1.1 x2.1 then eqbool x1.2 x2.2 else false.

Definition spair_confluence_dec_int fuel R :=
  if all (fun p => eqseq_int p.1 p.2) (all_npairs_int R) then
    let spairs := filter (fun p => ~~ eqseq_int p.1 p.2) (all_spairs_int R) in
    (* all (fun p => norfuel_int R fuel p.1 == norfuel_int R fuel p.2) spairs *)
    all (eqnor R fuel) spairs
  else false.
Lemma spair_confluence_dec_intE :
  @spair_confluence_dec int = spair_confluence_dec_int.
Proof. by []. Qed.


Definition R := (prelat present_final).
Definition spair_confluence_fast := Eval compute in @spair_confluence_dec int.
Lemma spair_confluence_dec_fastE :
  @spair_confluence_dec int = spair_confluence_fast.
Proof. by []. Qed.


Section ListOrder.

Variable (T : eqType).

Definition pord (l1 l2 : list T) (t : T) : T := nth t l2 (index t l1).

Lemma pordK (l1 l2 : list T) :
  uniq l1 -> perm_eq l1 l2 -> cancel (pord l1 l2) (pord l2 l1).
Proof.
rewrite /pord => uniq1 Hperm t.
have uniq2 : uniq l2 by rewrite -(perm_uniq Hperm).
have eqsize : seq.size l1 = seq.size l2 by rewrite (perm_size Hperm).
case (boolP (t \in l1)) => [tin | tout].
  rewrite nthK ?nth_index // -eqsize.
  by move: tin; rewrite -index_mem.
rewrite (memNindex tout) eqsize (nth_default _ (s := l2)) //.
move: tout; rewrite (perm_mem Hperm) => /memNindex ->.
by rewrite nth_default ?eqsize.
Qed.

End ListOrder.

(*
Time Eval native_compute in all (spair_confluence_dec_int 5)
                              (nseq 10 (prelat present_final)).
(* Finished transaction in 7.328 secs (7.209u,0.s) (successful) *)
Time Eval native_compute in all (spair_confluence_fast 5)
                              (nseq 10 (prelat present_final)).
(* Finished transaction in 13.338 secs (12.972u,0.003s) (successful) *)
*)

Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent (reorderK (l := final_order) is_true_true) erefl).
apply: diamond.
  apply: (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check (eq_refl true).
apply: (spair_confluenceP (fuel := 10)).
rewrite spair_confluence_dec_intE.

(*
Set NativeCompute Timing.
Set NativeCompute Profiling.
Time by native_compute. *)
by native_cast_no_check (eq_refl true).
Optimize Heap.
Time Qed.
(* Finished transaction in 1.456 secs (1.281u,0.004s) (successful) *)
(* WAS : *)
(* Finished transaction in 17.524 secs (17.357u,0.s) (successful) *)
