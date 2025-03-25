From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.

Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import present rewcert fastcert criteria homogeneous.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Fuel : nat := 20.

Variant CheckCertifiedPresentationError :=
  | CPOk
  | CPTietzeSequenceError
  | CPOrderDup
  | CPConfluenceError
  | CPNotDecreasing
  | CPWatierError
  | CPMonogenicError
  | CPFreeProductMonogenicAndFreeError
  | CPLeftCycleFree1RelError
  | CPOccError
  | CPSmallOverlapError
  | CPHomogeneousError  (* Not used in the database *)
      (* Recursive cases *)
  | CPGeneratorMissmatchError
  | CPRelationMissmatchError
  | CPNotImplemented.


Definition certpres_Ok r := if r is CPOk then true else false.

Definition check_certpres (CP : @CertifiedPresentation int) :=
  let (P, PC) := CP in match PC with
  | CompleteRewritingSystem cert order =>
      if ~~ wfpres_cert P cert then CPTietzeSequenceError else
        if ~~ uniq order then CPOrderDup else
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
  | FreeProductMonogenicAndFree =>
      if ~~ free_product_monogenic_free P then
        CPFreeProductMonogenicAndFreeError
      else CPOk
  | EqualNumberOfOccurences l =>
      if ~~ is_left_cycle_free_1rel P then CPLeftCycleFree1RelError else
      if ~~ has_same_number_of_occ P l then CPOccError else CPOk
  | SmallOverlap facts =>
      if ~~ check_small_overlap 3 P facts then CPSmallOverlapError else CPOk
  | Homogeneous =>
      if ~~ is_homogeneous (prelat P) then CPHomogeneousError else CPOk
  end.

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
- case: (boolP (_ pres)) => //= fp _.
  exact: free_product_monogenic_free_dec.
- move=> l.
  case: (boolP (is_left_cycle_free_1rel _)) => //= free.
  case: (boolP (has_same_number_of_occ _ _)) => //= nbocc _.
  exact: (check_same_number_occ_dec free nbocc).
- move=> facts.
  case: (boolP (check_small_overlap 3 _ _)) => //= c3 _.
  exact: (check_c3_monoid_dec c3).
- case: (boolP (is_homogeneous _)) => //= homog _.
  exact: (homog_dec homog).
Qed.

Record checked_presentation : Type :=
  CheckedPres { chkpres :> pres int;
                certificate : PresentationCertificate;
                _ : certpres_Ok (check_certpres (chkpres, certificate)) }.
Definition make_checked_presentation PC
  (H : certpres_Ok (check_certpres (PC.1, PC.2)))
  : checked_presentation := @CheckedPres PC.1 PC.2 H.
Notation make_chkpres G R C :=
  (make_checked_presentation (PC := (make_pres G R, C)) is_true_true).

Lemma chkpres_dec (cp : checked_presentation) : WPdecidable cp.
Proof. case: cp => P C H; exact: (check_certpresP H). Qed.

Lemma check_seq_certpresP (l : seq (@CertifiedPresentation int)) :
  all (certpres_Ok \o check_certpres) l ->
  forall (P : pres int), P \in [seq CP.1 | CP <- l] -> WPdecidable P.
Proof.
elim: l => // l0 l IHl /= /andP[/check_certpresP dec0 {}/IHl Hl] P.
by rewrite inE; case: eqP => [-> //|_ /=]; apply: Hl.
Qed.


Record decidable_presentation (Alph : choiceType) : Type :=
  DecPres { decpres :> pres Alph; _ : WPdecidable decpres }.
Definition make_decidable_presentation P (H : certpres_Ok (check_certpres P))
  : decidable_presentation _ := DecPres (check_certpresP H).
Notation make_decpres PC := (make_decidable_presentation (P := PC) is_true_true).


Variant recursive_certificate (Alph : choiceType) :=
  (* apply rev to all relation words keeping the gens and relation order *)
  | Reverse
  (* reorder the generator and relation -- WARNING : very slow if needed *)
  | Reorder
  (* params : the word which is kept and sent to a which letter among 0 and 1 *)
  | StronglyCompressAndReduced of word Alph & Alph.

Definition RecursivelyCertifiedPresentation (Alph : choiceType) : Type :=
  (pres Alph * (decidable_presentation Alph * recursive_certificate Alph)).


Definition check_reccertpres (CP : @RecursivelyCertifiedPresentation int) :=
  let: (P, (recP, PC)) := CP in match PC with
  | Reverse =>
     if pgen P != (pgen recP) then CPGeneratorMissmatchError
     else if prelat P != dual_relats (prelat recP) then CPRelationMissmatchError
          else CPOk
  | Reorder =>
     if ~~ perm_eq (pgen P) (pgen recP) then CPGeneratorMissmatchError
     else if ~~ perm_eq (prelat P) (prelat recP) then CPRelationMissmatchError
          else CPOk
  | StronglyCompressAndReduced w l =>
      CPNotImplemented
  end.

Lemma check_reccertpresP P :
  certpres_Ok (check_reccertpres P) -> WPdecidable P.1.
Proof.
rewrite /check_reccertpres; case: P => pres [prec []] //.
- case: eqP => eqgen //=; case: eqP => eqrel //= _.
  suff -> : pres = dual_pres prec by apply: dual_dec; case prec.
  by apply/eqP; rewrite -eqpresE eqgen /= -eqrel !eqxx.
- case: (boolP (perm_eq _ _)) => permgen //=.
  case: (boolP (perm_eq _ _)) => permrel //= _.
  apply: (isopres_dec (pres_irrelevance_perm_eq permgen permrel)).
  by case prec.
Qed.

Definition make_recursively_decidable_presentation P
  (H : certpres_Ok (check_reccertpres P))
  : decidable_presentation _ := DecPres (check_reccertpresP H).
Notation make_recdecpres PC :=
  (make_recursively_decidable_presentation (P := PC) is_true_true).


Definition AB_AAAAAA_ABAABA :=
  (make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])],
  CompleteRewritingSystem
    [::
       add_rel [::0;1;0;0;1;0] [::0;0;0;0;0;0]
         [:: RTriple 0 0 false];
       add_rel [::0;1;0;0;0;0;0;0;0] [::0;0;0;0;0;0;0;1;0]
         [:: RTriple 0 3 true;
             RTriple 1 0 true];
       rm_rel 0
         [:: RTriple 0 0 false]]
    [::0;1]).

Definition AB_AAAAAA_ABAABA_dec := @make_decpres AB_AAAAAA_ABAABA.

Definition AB_AAAAAA_ABAABA_rec :=
  (make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])],
    (AB_AAAAAA_ABAABA_dec, @Reverse int)).
Definition AB_AAAAAA_ABAABA_dec_rec := @make_recdecpres AB_AAAAAA_ABAABA_rec.

