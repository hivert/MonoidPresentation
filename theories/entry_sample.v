From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice bigop fintype finfun finset ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* A sample of formalized page of the encyclopaedia of 1-relation of monoid
   presentations. *)


(* Presentation entry, in this case <a, b | aaba = baa>. 

In the current, unsatisfactory state, a presentation is just a rewrite system.
 Later, we should also provide the list of generators. *)
Definition entry := [:: ([:: 0; 0; 1; 1], [:: 1; 0; 0])].



Definition present_final :=
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

Theorem final_ok : convergent present_final.
Proof. exact: (check_convergence_natP (fuel := 5)). Qed.



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
