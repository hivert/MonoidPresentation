From mathcomp Require Import order.


Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check is_true_true.
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.

Require Import inttrie.


Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent (reorderK (l := final_order) is_true_true) erefl).
apply: diamond.
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
pose trsize := pres_triesize present_final.
have relbound : correctrelat (prelat present_final) (<%O^~ trsize) by [].
have sizebound : (trsize <= PArray.max_length)%O by [].
apply (spair_confluence_loopP (trie_rewrites1P sizebound relbound) (fuel := 10)).
rewrite spair_confluence_loop_trieE.
(* Set NativeCompute Timing.
Set NativeCompute Profiling.
Time by native_compute.  *)
by native_cast_no_check is_true_true.
(* Optimize Heap. *)
Time Qed.
