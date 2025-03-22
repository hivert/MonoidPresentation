Load "header.v".

Require Import batchchecker.
Require batch0.

Lemma all_pres_correct : all (certpres_Ok \o check_certpres) batch0.all_pres.
Proof. by native_cast_no_check is_true_true. Qed.

Lemma all_pres_dec (P : pres int) :
  P \in [seq CP.1 | CP <- batch0.all_pres] -> WPdecidable P.
Proof. exact: (check_seq_certpresP all_pres_correct). Qed.

(*
Eval compute in seq.size all_pres.

Eval native_compute in all (certpres_Ok \o check_certpres) all_pres.


Section Debug.

Let P := BA_BABA_AABABBABAA_0.1.
Let bla := match BA_BABA_AABABBABAA_0.2 with
           | CompleteRewritingSystem cert ord => (cert, ord)
           | _ => ([::], [::])
           end.
Let cert := bla.1.
Let ord := Eval compute in bla.2.
Let relfinal := Eval compute in rel_cert (prelat P) cert.
Let sorted_ord := Eval compute in sort <%O ord.
Let newg := pord ord sorted_ord.
Let newrels := Eval compute in [seq rgen_rels newg i | i <- relfinal].

Eval native_compute in all (certpres_Ok \o check_certpres) all_pres.
*)
