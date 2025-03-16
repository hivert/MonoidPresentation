Definition sorted_order := Eval compute in sort <%O final_order.

Definition reorderK := @pordK _ final_order sorted_order
                      is_true_true is_true_true.

Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check (eq_refl true).
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.

Theorem final_ok : convergent (prelat present_final).
Proof.
apply: (rgen_convergent reorderK erefl).
apply: diamond.
  apply: (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check (eq_refl true).
apply: (spair_confluenceP (fuel := 20)).
rewrite spair_confluence_dec_intE.
(* Set NativeCompute Timing.
Set NativeCompute Profiling.
Time by native_compute.  *)
by native_cast_no_check (eq_refl true).
(* Optimize Heap. *)
Time Qed.
