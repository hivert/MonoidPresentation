From mathcomp Require Import order.


Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check is_true_true.
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.


Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent (reorderK (l := final_order) is_true_true) erefl).
apply: diamond.
  apply: (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
apply: (spair_confluenceP (fuel := 100)).
rewrite -spair_confluence_loopE spair_confluence_loop_intE.
(* Set NativeCompute Timing.
Set NativeCompute Profiling.
Time by native_compute.  *)
by native_cast_no_check is_true_true.
(* Optimize Heap. *)
Time Qed.
