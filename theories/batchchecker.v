From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63.
From mathcomp Require Import all_ssreflect.

Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import int_seq present rewcert fastcert criteria homogeneous.

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
  | CPPresentationNotFound
  | CPNotImplemented.


Definition certpres_Ok r := if r is CPOk then true else false.

Definition check_certpres (P : pres int) (PC : prescertificate) :=
  match PC with
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

Lemma check_certpresP P C : certpres_Ok (check_certpres P C) -> WPdecidable P.
Proof.
rewrite /check_certpres; case: C => [].
- move=> cert order.
  case: (boolP (wfpres_cert P cert)) => //= wfc.
  case: (boolP (uniq _)) => //= uniq_order.
  case: (boolP (decreasing _ _)) => //= decr.
  case: (boolP (spair_confluence_loop_int  _ _)) => //= confl _.
  apply: (isopres_dec (@iso_final_pres _ P cert wfc)).
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
- case: (boolP (_ P)) => //= fp _.
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


Section Batch.

Variable (certType : Type).
Variable (checker : pres int -> certType -> CheckCertifiedPresentationError).
Hypothesis (checkerP : forall p c, certpres_Ok (checker p c) -> WPdecidable p).

Fixpoint generic_check_batch (lp : seq (pres int)) (lc : seq certType) :=
  match lp, lc with
  | p :: tlp, c :: tlc =>
      if ~~ certpres_Ok (checker p c) then false
      else generic_check_batch tlp tlc
  | [::], [::] => true
  | _, _ => false
  end.

Lemma generic_check_seq_certpresP (l : seq (pres int * certType)) :
  all (fun cpair => certpres_Ok (checker cpair.1 cpair.2)) l ->
  forall (P : pres int), P \in unzip1 l -> WPdecidable P.
Proof.
elim: l => // l0 l IHl /= /andP[/checkerP dec0 {}/IHl Hl] P.
by rewrite inE; case: eqP => [-> //|_ /=]; apply: Hl.
Qed.
Lemma generic_check_batchE (lp : seq (pres int)) (lc : seq certType) :
  (generic_check_batch lp lc) =
    (seq.size lp == seq.size lc) &&
    all (fun cpair => certpres_Ok (checker cpair.1 cpair.2)) (zip lp lc).
Proof.
elim: lp lc => [|p lp Hlp] [|c lc] //=.
by case: (certpres_Ok _); rewrite //= andbF.
Qed.
Lemma generic_check_batchP (lp : seq (pres int)) (lc : seq certType) :
  generic_check_batch lp lc -> forall P, P \in lp -> WPdecidable P.
Proof.
rewrite generic_check_batchE.
case/andP => /eqP eqsz /generic_check_seq_certpresP /= H P Pin.
by apply: H; rewrite unzip1_zip // eqsz.
Qed.

End Batch.

Definition check_batchP := generic_check_batchP check_certpresP.


Definition AB_AAAAAA_ABAABA :=
  make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])].
Definition AB_AAAB_A :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].
Definition A_AAA_A := make_pres [:: 0] [:: ([:: 0; 0; 0], [:: 0])].
Definition AB_ABB_BA := make_pres [:: 0; 1] [:: ([:: 0; 1; 1], [:: 1; 0])].
Definition AB_BAAAABBAAA_ABBBAABA :=
  make_pres [:: 0; 1]
       [:: ([:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0], [:: 0; 1; 1; 1; 0; 0; 1; 0]) ].
Definition all_pres := [:: AB_AAAAAA_ABAABA;
                        AB_AAAB_A;
                        A_AAA_A;
                        AB_ABB_BA;
                        AB_BAAAABBAAA_ABBBAABA].

Lemma all_pres_dec (P : pres int) : P \in all_pres -> WPdecidable P.
Proof.
apply: (check_batchP (lc :=
  [:: CompleteRewritingSystem
    [::
       add_rel [::0;1;0;0;1;0] [::0;0;0;0;0;0]
         [:: RTriple 0 0 false];
       add_rel [::0;1;0;0;0;0;0;0;0] [::0;0;0;0;0;0;0;1;0]
         [:: RTriple 0 3 true;
             RTriple 1 0 true];
       rm_rel 0
         [:: RTriple 0 0 false]]
    [::0;1];
   Watier 0 1 [:: 1; 1; 0] [::] 3;
   Monogenic;
   EqualNumberOfOccurences 0;
   SmallOverlap [::
                   [:: [:: 1; 0; 0; 0]; [:: 0; 1; 1]; [:: 0; 0; 0] ];
                 [:: [:: 0; 1; 1]; [:: 1; 0; 0]; [:: 1; 0] ]
       ]])).
   by native_cast_no_check is_true_true.
Qed.


Variant recursive_criterion {Alph : choiceType} :=
  (* apply rev to all relation words keeping the gens and relation order *)
  | Reverse
  (* reorder the generator and relation -- WARNING: very slow if needed *)
  | Reorder
  (* params: the word which is kept and sent to a which letter among 0 and 1 *)
  | StronglyCompressAndReduce of word Alph & Alph.
Record recursive_certificate {Alph : choiceType} := RecCert
  { lpres     : seq (pres Alph);
    lproof    : forall P : pres Alph, P \in lpres -> WPdecidable P;
    pres_ind  : int;
    pres_crit : @recursive_criterion Alph
  }.

Definition check_reccertpres (P : pres int) (C : recursive_certificate) :=
  let: RecCert lp lproof ind crit := C in
    if onth_int lp ind is Some prec then
      match crit with
      | Reverse =>
          if pgen P != (pgen prec) then CPGeneratorMissmatchError
          else if prelat P != dual_relats (prelat prec)
               then CPRelationMissmatchError
               else CPOk
      | Reorder =>
          if ~~ perm_eq (pgen P) (pgen prec) then CPGeneratorMissmatchError
          else if ~~ perm_eq (prelat P) (prelat prec) then CPRelationMissmatchError
          else CPOk
      | StronglyCompressAndReduce w l =>
          CPNotImplemented
      end
    else CPPresentationNotFound.

Lemma check_reccertpresP P C:
  certpres_Ok (check_reccertpres P C) -> WPdecidable P.
Proof.
rewrite /check_reccertpres; case: C => lp prf ind crit.
case Hget: (onth_int lp ind) => /= [prec|] //.
move/onth_int_mem: Hget => {}/prf prec_dec.
case: crit.
- case: eqP => eqgen //=; case: eqP => eqrel //= _.
  suff -> : P = dual_pres prec by apply: dual_dec.
  by apply/eqP; rewrite -eqpresE eqgen /= -eqrel !eqxx.
- case: (boolP (perm_eq _ _)) => permgen //=.
  case: (boolP (perm_eq _ _)) => permrel //= _.
  exact: (isopres_dec (pres_irrelevance_perm_eq permgen permrel)).
- by []. (* NotImplemented *)
Qed.

Definition check_recbatchP := generic_check_batchP check_reccertpresP.


Record decidable_presentation (Alph : choiceType) : Type :=
  DecPres { decpres :> pres Alph; _ : WPdecidable decpres }.
Definition make_decidable_presentation P C (H : certpres_Ok (check_certpres P C))
  : decidable_presentation _ := DecPres (check_certpresP H).
Notation make_decpres P C :=
  (make_decidable_presentation (P := P) (C := C) is_true_true).

Definition make_recursively_decidable_presentation P C
  (H : certpres_Ok (check_reccertpres P C))
  : decidable_presentation _ := DecPres (check_reccertpresP H).
Notation make_recdecpres P C :=
  (make_recursively_decidable_presentation (P := P) (C := C) is_true_true).



Definition AB_BBA_AB :=
  make_pres [::0;1]  [:: ([:: 1;1;0], [:: 0;1])].
Definition AB_ABBABBB_A :=
  make_pres [:: 0; 1] [:: ([:: 0;1;1;0;1;1;1], [:: 0])].
Definition BA_BBBABBA_A :=
  make_pres [:: 1; 0] [:: ([:: 1;1;1;0;1;1;0], [:: 0])].
Definition list_recpres := [:: AB_BBA_AB; AB_ABBABBB_A; BA_BBBABBA_A].

Definition AB_BBA_AB_rec_cert :=
  RecCert all_pres_dec 3 Reverse.
Definition AB_BBA_AB_dec :=
  @make_recdecpres AB_BBA_AB AB_BBA_AB_rec_cert.

Definition AB_ABBABBB_A_rec_cert :=
  RecCert all_pres_dec 1 Reverse.
Definition AB_ABBABBB_A_dec :=
  @make_recdecpres AB_ABBABBB_A AB_ABBABBB_A_rec_cert.

Definition BA_BBBABBA_A_rec_cert :=
  RecCert all_pres_dec 1 Reorder.
Definition BA_ABBABBB_A_dec :=
  @make_recdecpres BA_BBBABBA_A BA_BBBABBA_A_rec_cert.
