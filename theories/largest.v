From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import monoids present cert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Load "samples/largest.v".

(* Proof that the two presentation defines isomorphic monoids *)
Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check (eq_refl true).
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.

(* Proof that the presentation is terminating + confluent. *)
Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent (rankK final_order) erefl).
apply: diamond.
  apply: (decreasing_wf (@lt_sizelexi_stable _ nat) sizelexi_nat_wf).
  by native_cast_no_check (eq_refl true).
apply: (spair_confluenceP (fuel := 5)).
time by native_cast_no_check (eq_refl true).
Time Qed.
(* Finished transaction in 18.554 secs (18.363u,0.s) (successful) *)

(*
Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent (rankK final_order) erefl).
apply: diamond.
  apply: (decreasing_wf (@lt_sizelexi_stable _ nat) sizelexi_nat_wf).
  Time by vm_compute.
apply: (spair_confluenceP (fuel := 5)).
Time by vm_compute.
(* Tactic call ran for 104.807 secs (104.8u,0.003s) (success) *)

(* set R := (X in convergent X).
Time Eval vm_compute in has (fun p => p.1 != p.2) (all_npairs R).
Time Eval vm_compute in size (all_spairs R). 
apply (check_convergence_natP (fuel := 5)). *)
Time Qed.
*)
