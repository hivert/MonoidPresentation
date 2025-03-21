From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.

Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import present rewcert fastcert criteria.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Fuel : nat := 20.

Variant CheckCertifiedPresentationError :=
  | CPOk
  | CPRewriteSequenceError
  | CPOrderDup
  | CPConfluenceError
  | CPNotDecreasing
  | CPWatierError
  | CPMonogenicError
  | CPLeftCycleFree1RelError
  | CPOccError
  | CPSmallOverlapError
  | CPNotImplemented.

Definition check_certpres (CP : @CertifiedPresentation int) :=
  let (P, PC) := CP in match PC with
  | CompleteRewritingSystem cert order =>
      if ~~ wfpres_cert P cert then CPRewriteSequenceError else
      if ~~ uniq order then CPOrderDup  else
         let relfinal := rel_cert (prelat P) cert in
         let sorted_ord := sort <%O order in
         let newg := pord order sorted_ord in
         let newrels := [seq rgen_rels newg i | i <- relfinal] in
         if ~~ decreasing <%O newrels then CPNotDecreasing else
         if ~~ spair_confluence_loop_int Fuel newrels
         then CPConfluenceError
         else CPOk
  | Watier a b u v k =>
      if ~~ check_Watier P a b u v k then CPWatierError else CPOk
  | Monogenic =>
      if ~~ monogenic P then CPMonogenicError else CPOk
  | FreeProductMonogenicAndFree => CPNotImplemented
  | EqualNumberOfOccurences l =>
      if ~~ is_left_cycle_free_1rel P then CPLeftCycleFree1RelError else
      if ~~ has_same_number_of_occ P l then CPOccError else CPOk
  | SmallOverlap facts =>
      if ~~ check_small_overlap 3 P facts then CPSmallOverlapError else CPOk
  end.
Definition certpres_Ok r := if r is CPOk then true else false.

Lemma check_certpresP P : certpres_Ok (check_certpres P) -> WPdecidable P.1.
Proof.
rewrite /check_certpres; case: P => pres [] //.
- move=> cert order.
  case: (boolP (wfpres_cert pres cert)) => //= wfc.
  case: (boolP (uniq _)) => //= uniq_order.
  case: (boolP (decreasing _ _)) => //= decr.
  case: (boolP (spair_confluence_loop_int  _ _)) => //= confl _.
  apply: (isopres_dec (@iso_final_pres _ pres cert wfc)).
  apply: convergent_dec; rewrite prelat_final_pres.
  apply: (rgen_convergent (reorderK uniq_order) erefl).
  apply: diamond.
    exact: (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  apply: spair_confluence_loopP.
  rewrite spair_confluence_loop_intE.
  exact: confl.
- move=> a b u v k /=.
  case: (boolP (check_Watier _ _ _ _ _ _)) => //= cW _.
  exact: (check_Watier_dec cW).
- case: (boolP (monogenic _)) => //= mono _.
  exact: monogenic_dec.
- move=> l.
  case: (boolP (is_left_cycle_free_1rel _)) => //= free.
  case: (boolP (has_same_number_of_occ _ _)) => //= nbocc _.
  exact: (check_same_number_occ_dec free nbocc).
- move=> facts.
  case: (boolP (check_small_overlap 3 _ _)) => //= c3 _.
  exact: (check_c3_monoid_dec c3).
Qed.
