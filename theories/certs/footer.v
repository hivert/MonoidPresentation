From mathcomp Require Import eqtype order.


Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check is_true_true.
suff -> : present_final = final_pres wfc by apply: iso_final_pres.
apply/eqP; rewrite -eqpresE pgen_final_pres prelat_final_pres.
by vm_cast_no_check is_true_true.
Time Qed.


Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent (reorderK (l := final_order) is_true_true) erefl).
apply: diamond.
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
apply: (spair_confluence_loopP (rewrites1P _) (fuel := 10)).
rewrite spair_confluence_loop_intE.
(* Set NativeCompute Timing.
Set NativeCompute Profiling.
Time by native_compute.  *)
by native_cast_no_check is_true_true.
(* Optimize Heap. *)
Time Qed.
