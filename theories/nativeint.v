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

Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check (eq_refl true).
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.


Definition R := (prelat present_final).
Definition foo := Eval compute in @spair_confluence_dec int.
Lemma fooE : @spair_confluence_dec PrimInt63_int__canonical__choice_Choice = foo.
Proof. by []. Qed.

(*
Time Eval native_compute in foo 5 R.

Definition bla := let spairs := filter (fun p => p.1 != p.2) (all_spairs R) in
  all (fun p => norfuel R 5 p.1 == norfuel R 5 p.2) spairs.

Set NativeCompute Profiling.

Time Eval native_compute in
  let spairs := filter (fun p => p.1 != p.2) (all_spairs R) in
  all (fun p => norfuel R 5 p.1 == norfuel R 5 p.2) spairs.

Time Definition spairs := Eval vm_compute in filter (fun p => p.1 != p.2) (all_spairs R).
Time Eval native_compute in
  all (fun p => norfuel R 5 p.1 == norfuel R 5 p.2) spairs.
 *)

Theorem final_ok : convergent (prelat present_final).
Proof.
(* FIXME: renumbering is broken on int apply: (rgen_convergent int_to_natK erefl). *)
apply: diamond.
  apply: (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check (eq_refl true).
apply: (spair_confluenceP (fuel := 5)).
rewrite fooE.
by native_cast_no_check (eq_refl true).
Time Qed.
(* Finished transaction in 17.524 secs (17.357u,0.s) (successful) *)
