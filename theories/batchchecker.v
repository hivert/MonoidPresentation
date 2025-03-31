From Coq Require Import Znat BinIntDef Uint63.
From mathcomp Require Import all_ssreflect.
Require Import int_seq wfsizelexi present rewcert fastcert
  criteria compress homogeneous.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope uint63_scope.


Definition Fuel : nat := 20.


Section Certificate.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).
Local Notation word := (word Alph).

Record recursive_certificate := RecCert
  { lpres : seq (pres Alph);
    _ : forall P, P \in lpres -> WPdecidable P;
    _ : int;
  }.

Variant prescertificate :=
    (* param: rewriting certificate + final order *)
  | CompleteRewritingSystem of @pres_cert Alph & seq Alph
    (* param: a b u v k in < a b | b^k a u = a v > *)
  | Watier of Alph & Alph & word & word & nat
  | Monogenic
  | CycleFree
  | FreeProductMonogenicAndFree
    (* param: repeated letter a in < a b | a^k = a^l > *)
  | EqualNumberOfOccurences of Alph
    (* param: list of the factorizations of each relations words *)
    (*        in the order given by relwords P                   *)
  | SmallOverlap of seq (seq word)
(* Not used in the database *)
  | Homogeneous
  | Special
(* Recursive certificates *)
  (* apply rev to all relation words keeping the gens and relation order *)
  | Reverse of recursive_certificate
  (* reorder the generator and relation -- WARNING: very slow if needed *)
  | Reorder of recursive_certificate
  (* flip the direction of the relation *)
  | FlipAllRelations of recursive_certificate
  (* params: the word which is kept and sent to a which letter among 0 and 1 *)
  | StronglyCompressAndReduce of recursive_certificate & word & Alph
  (* We don't recurse here as the special presentation can have *)
  (* more than two generators and thus is not in the database.  *)
  | StronglyCompressToSpecial.


Variant check_certified_presentation_result :=
  | CPOk
  | CPTietzeSequenceError
  | CPOrderDup
  | CPConfluenceError
  | CPNotDecreasing
  | CPWatierError
  | CPMonogenicError
  | CPCycleFreeError
  | CPFreeProductMonogenicAndFreeError
  | CPLeftCycleFree1RelError
  | CPOccError
  | CPSmallOverlapError
  (* Not used in the database *)
  | CPHomogeneousError
  | CPSpecialError
  (* Recursive cases *)
  | CPGeneratorMissmatchError
  | CPRelationMissmatchError
  | CPRecursivePresentationNotFound
  (* TODO: remove me when done *)
  | CPNotImplemented.

Definition certpres_Ok r := if r is CPOk then true else false.

(* Recursive case *)
Variables
  (P : pres Alph)
  (c : recursive_certificate)
  (checker : pres Alph -> check_certified_presentation_result).

Hypothesis checkerP : forall Prec,
  WPdecidable Prec -> certpres_Ok (checker Prec) -> WPdecidable P.

Definition check_recurse :=
  let: RecCert lp _ i:= c in
  if onth_int lp i is some prec then checker prec
  else CPRecursivePresentationNotFound.

Lemma check_recurseP : certpres_Ok check_recurse -> WPdecidable P.
Proof.
rewrite /check_recurse; case: c => lp prfs ind.
case Hget: (onth_int lp ind) => /= [prec|] //.
by move/onth_int_mem: Hget => {}/prfs prec_dec /checkerP; apply.
Qed.

End Certificate.


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
  | CycleFree =>
      if ~~ is_cycle_free_1rel P then CPCycleFreeError else CPOk
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
  | Special =>
      if ~~ is_special (prelat P) then CPSpecialError else CPOk
  | Reverse c => check_recurse c (fun prec =>
      if pgen P != (pgen prec) then CPGeneratorMissmatchError
      else if prelat P != dual_relats (prelat prec)
           then CPRelationMissmatchError
           else CPOk)
  | Reorder c => check_recurse c (fun prec =>
      if ~~ perm_eq (pgen P) (pgen prec) then CPGeneratorMissmatchError
      else if ~~ perm_eq (prelat P) (prelat prec) then CPRelationMissmatchError
           else CPOk)
  | FlipAllRelations c => check_recurse c (fun prec =>
      if pgen P != (pgen prec) then CPGeneratorMissmatchError
      else if prelat prec != map swap (prelat P) then CPRelationMissmatchError
           else CPOk)
  | StronglyCompressAndReduce c w l => check_recurse c (fun prec =>
      CPNotImplemented)
  | StronglyCompressToSpecial =>
      CPNotImplemented
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
  case: (boolP (check_Watier P a b u v k)) => //= cW _.
  exact: (check_Watier_dec cW).
- case: (boolP (monogenic P)) => //= mono _.
  exact: monogenic_dec.
- case: (boolP (is_cycle_free_1rel P)) => //= cf1r _.
  exact: is_cycle_free_1rel_dec.
- case: (boolP (free_product_monogenic_free P)) => //= fp _.
  exact: free_product_monogenic_free_dec.
- move=> l.
  case: (boolP (is_left_cycle_free_1rel P)) => //= free.
  case: (boolP (has_same_number_of_occ P l)) => //= nbocc _.
  exact: (check_same_number_occ_dec free nbocc).
- move=> facts.
  case: (boolP (check_small_overlap 3 P facts)) => //= c3 _.
  exact: (check_c3_monoid_dec c3).
- case: (boolP (is_homogeneous (prelat P))) => //= homog _.
  exact: (homog_dec homog).
- case: (boolP (is_special (prelat P))) => //= spec _.
  exact: (special_dec spec).
- move=> r; apply: check_recurseP => prec prec_dec.
  case: eqP => eqgen //=; case: eqP => eqrel //= _.
  suff -> : P = dual_pres prec by apply: dual_dec.
  by apply/eqP; rewrite -eqpresE eqgen /= -eqrel !eqxx.
- move=> r; apply: check_recurseP => prec prec_dec.
  case: (boolP (perm_eq _ _)) => permgen //=.
  case: (boolP (perm_eq _ _)) => permrel //= _.
  exact: (isopres_dec (pres_irrelevance_perm_eq permgen permrel)).
- move=> r; apply: check_recurseP => prec prec_dec.
  case: eqP => eqgen //=; case: eqP => eqrel //= _; apply: flipped_pres_dec.
  suff <- : prec = flipped_pres P by [].
  by apply/eqP; rewrite -eqpresE eqgen /= !eqxx /= eqrel.
- move=> r w i; apply: check_recurseP => prec prec_dec.
  by []. (* NotImplemented *)
- by []. (* NotImplemented *)
Qed.

Variant batchresult :=
  | BatchOk
  (* Lenghts of the batch and certificate doesn't match *)
  | BatchLengthMismatch
  (* Check failed for presentation at position with given Error *)
  | BatchError of int & check_certified_presentation_result.

Definition check_batch (lp : seq (pres int)) (lc : seq prescertificate) :=
  let fix rec (i : int) lp lc :=
    match lp, lc with
    | p :: tlp, c :: tlc =>
        let res := check_certpres p c in
        if ~~ certpres_Ok (res) then BatchError i res
        else rec (i + 1) tlp tlc
    | [::], [::] => BatchOk
    | _, _ => BatchLengthMismatch
    end in
  rec 0 lp lc.
Definition batch_ok b := if b is BatchOk then true else false.
Lemma batch_okP b : reflect (b = BatchOk) (batch_ok b).
Proof. by apply (iffP idP); case: b. Qed.

Lemma check_seq_certpresP (l : seq (pres int * prescertificate)) :
  all (fun cpair => certpres_Ok (check_certpres cpair.1 cpair.2)) l ->
  forall (P : pres int), P \in unzip1 l -> WPdecidable P.
Proof.
elim: l => // l0 l IHl /= /andP[/check_certpresP dec0 {}/IHl Hl] P.
by rewrite inE; case: eqP => [-> //|_ /=]; apply: Hl.
Qed.
Lemma check_batchE (lp : seq (pres int)) (lc : seq prescertificate) :
  (batch_ok (check_batch lp lc)) =
    (seq.size lp == seq.size lc) &&
    all (fun cpair => certpres_Ok (check_certpres cpair.1 cpair.2)) (zip lp lc).
Proof.
rewrite /check_batch; move: 0 => i.
elim: lp lc i => [|p lp Hlp] [|c lc] i //=.
by case: (certpres_Ok _); rewrite //= andbF.
Qed.
Lemma check_batchP (lp : seq (pres int)) (lc : seq prescertificate) :
  check_batch lp lc = BatchOk -> forall P, P \in lp -> WPdecidable P.
Proof.
move/batch_okP; rewrite check_batchE.
case/andP => /eqP eqsz /check_seq_certpresP /= H P Pin.
by apply: H; rewrite unzip1_zip // eqsz.
Qed.


Module Examples.

Definition AB_AAAAAA_ABAABA :=
  make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])].
Definition AB_AAAB_A :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].
Definition A_AAA_A := make_pres [:: 0] [:: ([:: 0; 0; 0], [:: 0])].
Definition AB_ABB_BA := make_pres [:: 0; 1] [:: ([:: 0; 1; 1], [:: 1; 0])].
Definition AB_BAAAABBAAA_ABBBAABA :=
  make_pres [:: 0; 1]
       [:: ([:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0], [:: 0; 1; 1; 1; 0; 0; 1; 0]) ].
Definition list_pres := [:: AB_AAAAAA_ABAABA;
                        AB_AAAB_A;
                        A_AAA_A;
                        AB_ABB_BA;
                        AB_BAAAABBAAA_ABBBAABA].

Lemma all_pres_dec (P : pres int) : P \in list_pres -> WPdecidable P.
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
   by native_cast_no_check (erefl BatchOk).
Qed.

Definition AB_BBA_AB :=
  make_pres [::0;1]  [:: ([:: 1;1;0], [:: 0;1])].
Definition AB_ABBABBB_A :=
  make_pres [:: 0; 1] [:: ([:: 0;1;1;0;1;1;1], [:: 0])].
Definition BA_BBBABBA_A :=
  make_pres [:: 1; 0] [:: ([:: 1;1;1;0;1;1;0], [:: 0])].
Definition AB_BA_ABB :=
  make_pres [:: 0; 1] [:: ([:: 1; 0], [:: 0; 1; 1])].
Definition list_recpres := [:: AB_BBA_AB; AB_ABBABBB_A; BA_BBBABBA_A; AB_BA_ABB].

Lemma all_recpres_dec (P : pres int) : P \in list_recpres -> WPdecidable P.
Proof.
apply: (check_batchP (lc :=
  [::
   Reverse (RecCert all_pres_dec 3);
   Reverse (RecCert all_pres_dec 1);
   Reorder (RecCert all_pres_dec 1);
   FlipAllRelations (RecCert all_pres_dec 3)
  ])).
by native_cast_no_check (erefl BatchOk).
Qed.

(* http://127.0.0.1:5000/proof/404857/ <a, b | aabab = aaabbb > Compress aa -> a *)
(* 

abbbb aaabbb

http://127.0.0.1:5000/proof/86021/

*)

End Examples.

