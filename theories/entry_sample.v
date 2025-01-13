From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* A sample of formalized page of the encyclopaedia of 1-relation of monoid
   presentations. *)


(* Presentation entry, in this case <a, b | aaba = baa>. 

In the current, unsatisfactory state, a presentation is just a rewrite system.
Generators are inferred from the letters involved in the system.
Later, we should also provide the list of generators. *)
Definition present_entry := [:: ([:: 3; 3; 4; 4], [:: 4; 3; 3])].


(* First candidate alternate presentation, this time with five generators *)
Definition present_final_1 :=
  [:: (*  c < e < d < a < b. *)
      (*  0 < 1 < 2 < 3 < 4. *)
     ([:: 3; 4], [:: 0]);           (* ab → c *)
     ([:: 4; 3], [:: 2]);           (* ba → d *)
     ([:: 3; 0], [:: 1]);           (* ac → e *)
     ([:: 3; 2], [:: 0; 3]);        (* ad → ca *)
     ([:: 4; 0], [:: 2; 4]);        (* bc → db *)
     ([:: 4; 1], [:: 1; 0]);        (* be → ec *)
     ([:: 2; 3], [:: 1; 3]);        (* da → ea *)
     ([:: 2; 0], [:: 1; 0]);        (* dc → ec *)
     ([:: 2; 1], [:: 1; 1]);        (* de → ee *)
     ([:: 3; 1; 3], [:: 0; 3; 3]);  (* aea → caa *)
     ([:: 3; 1; 0], [:: 0; 1]);     (* aec → ce *)
     ([:: 3; 1; 1], [:: 0; 3; 1])   (* aee → cae*)
   ].

(* Proof that the entry and final presentations define the same monoid. 
   Warning: this is an effective result, containing the data of the isomorphism,
   hence the Defined. *)

Parameter cool : False.
Theorem present_equiv :  isopres present_entry present_final_1.
Proof. elim cool. Defined.

Corollary equiv_equal u v : 
(u = v %[mod present_entry]) <-> (present_equiv u = present_equiv v %[mod present_final_1]).
Proof. admit. Admitted.

(* Proof that the presentation is terminating + confluent. *)
Theorem final_1_ok : convergent present_final_1.
Proof. exact: (check_convergence_natP (fuel := 5)). Qed.

(* The word problem is hence decidable in this monoid. *)
Theorem decidable_entry : True.
Proof. done. Qed. 

(* To be implemented combining norfuel and termination somehow *)
Parameter normalize : seq nat -> seq nat.

Definition test_eq_entry u v := 
    (normalize (present_equiv u)) == normalize (present_equiv v).

(* And now we provide a formally verified equality test for this monoid. *)
Theorem test_eqP u v :
reflect (u = v %[mod present_entry]) (test_eq_entry u v).
Proof. admit. Admitted.

(* Now users can test (dis)equalities and get a formal proof of the result
 *)


 (* And now an optimized variant: implement a test_eq_opt and prove that it is 
   pointwise equal to tes_eq *)


(***** END ******)   

Goal ([:: 1; 2; 2] < [:: 2; 2; 1])%O. by []. Qed.
Goal ~~ ([:: 2; 2] < [:: 1])%O. by []. Qed.
Goal ~~ ([:: 1; 2; 2] < [:: 2; 2])%O. by []. Qed.

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]); ([:: 1], [:: 0])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]);
                             ([:: 1], [:: 0]);
                             ([:: 2; 1; 2], [::])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Definition present_page_3_1 :=
  [::
   ([:: 2; 1; 1], [:: 1; 1; 2; 1]);
   ([:: 1; 2], [:: 3]);
   ([:: 2; 1], [:: 4]);
   ([:: 1; 3], [:: 5]);
   ([:: 1; 4], [:: 3; 1]);
   ([:: 2; 3], [:: 4; 2]);
   ([:: 2; 5], [:: 5; 3])].



Goal not (correctpres present_page_3_1 (geq 3)). by []. Qed.
Goal not (correctpres present_page_3_1 (geq 4)). by []. Qed.
Goal correctpres present_page_3_1 (geq 5). by []. Qed.
Goal correctpres present_page_3_1 (geq 6). by []. Qed.


Lemma step_3_1 : [:: 2; 5] = [:: 5; 3] %[mod present_page_3_1].
Proof.
by exists [::
        [:: 2; 1; 3];
        [:: 2; 1; 1; 2];
        [:: 1; 1; 2; 1; 2];
        [:: 1; 3; 1; 2];
        [:: 5; 1; 2];
        [:: 5; 3]].
Qed.

Eval vm_compute in norfuel present_page_3_1 10 [:: 2; 5].

Eval vm_compute in all_spairs present_page_3_1.
Eval vm_compute in all_npairs present_page_3_1.
