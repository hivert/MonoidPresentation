(** * Presentation of the symmetric groups on 4 points *)
(******************************************************************************)
(*      Copyright (C) 2025      Anonymous        *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
From Coq Require Import (* Znat BinIntDef *) Uint63.
From mathcomp Require Import ssreflect ssrbool ssrfun seq choice.
From mathcomp Require Import eqtype order ssrnat path.

Local Open Scope uint63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import int_seq present rewcert fastcert criteria sizelexi.
Require Import inttrie enumnf.


Definition S4_Moore := make_pres [::0;1;2]
  [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::0;1;0], [::1;0;1]);
      ([::1;2;1], [::2;1;2]);
      ([::0;2], [::2;0])].

Definition S4_rws := make_pres [::0;1;2]
  [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::1;0;1], [::0;1;0]);
      ([::2;0], [::0;2]);
      ([::2;1;2], [::1;2;1]);
      ([::2;1;0;2], [::1;2;1;0])].

Definition S4_Moore_cert : pres_cert := [:: add_rel [::1;0;1] [::0;1;0]
     [:: RTriple 3 0 false];
     add_rel [::2;0] [::0;2]
     [:: RTriple 5 0 false];
     add_rel [::2;1;2] [::1;2;1]
     [:: RTriple 4 0 false];
     add_rel [::2;1;0;2] [::1;2;1;0]
     [:: RTriple 5 2 true;
         RTriple 8 0 true];
     rm_rel 3
     [:: RTriple 5 0 false];
     rm_rel 3
     [:: RTriple 6 0 false];
     rm_rel 3
     [:: RTriple 4 0 false]].

Definition S4_Moore_order := [::0;1;2].


Theorem isopres_S4 : isopres S4_Moore S4_rws.
Proof.
have wfc : wfpres_cert S4_Moore S4_Moore_cert by vm_cast_no_check is_true_true.
suff -> : S4_rws = final_pres wfc by apply: iso_final_pres.
apply/eqP; rewrite -eqpresE pgen_final_pres prelat_final_pres.
by vm_cast_no_check is_true_true.
Time Qed.

Theorem S4_rws_convergent : convergent (prelat S4_rws).
Proof.
apply: diamond.
  apply: (rgen_pres_terminating
            (newgK := reorderK (l := S4_Moore_order) is_true_true)).
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
have pgenOk : all (<%O^~ PArray.max_length) (pgen S4_rws) by [].
apply: (spair_confluence_loop_trieP pgenOk (fuel := 10)).
rewrite spair_confluence_loop_trieE.
by native_cast_no_check is_true_true.
Time Qed.

(*
Eval compute in size (prelat S4_Moore).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat S4_Moore)].
Eval compute in size (prelat S4_rws).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat S4_rws)].
Eval compute in size S4_Moore_cert.

Time Eval compute in foldl (fun acc s => acc + size_int s) 0
  (traject (enum_normal_next_trie S4_rws) [:: [::]] 30).
*)


Definition not_S4 := make_pres [::0;1;2]
  [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::0;1;0;1;0;1], [::]);
      ([::0;2;0;2;0;2], [::]);
      ([::1;0;1;0;1;0], [::]);
      ([::1;2;1;2;1;2], [::]);
      ([::2;0;2;0;2;0], [::]);
      ([::2;1;2;1;2;1], [::]);
      ([::0;1;2;0;1;2;0;1;2;0;1;2], [::]);
      ([::0;2;1;0;2;1;0;2;1;0;2;1], [::]);
      ([::1;0;2;1;0;2;1;0;2;1;0;2], [::]);
      ([::1;2;0;1;2;0;1;2;0;1;2;0], [::]);
      ([::2;0;1;2;0;1;2;0;1;2;0;1], [::]);
      ([::2;1;0;2;1;0;2;1;0;2;1;0], [::])].

Definition not_S4_rws := make_pres [::0;1;2]
  [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::1;2;0;1;2;0], [::0;2;1;0;2;1]);
      ([::2;1;0;2;1;0], [::0;1;2;0;1;2]);
      ([::2;0;1;2;0;1], [::1;0;2;1;0;2]);
      ([::2;1;0;2;0], [::1;2;1;0;2]);
      ([::1;0;2;1;0;2;1], [::2;0;1;2;0]);
      ([::2;0;2], [::0;2;0]);
      ([::2;1;2], [::1;2;1]);
      ([::1;0;1], [::0;1;0]);
      ([::2;0;1;2;1], [::0;2;0;1;2]);
      ([::1;0;2;0;1;2;0], [::0;1;2;1;0;2;1]);
      ([::1;2;0;1;0;2;0], [::0;2;0;1;0;2;1]);
      ([::1;0;2;0;1;0;2;1], [::2;0;1;0;2;0]);
      ([::2;0;1;0;2;1;0], [::0;1;2;0;1;0;2]);
      ([::2;0;1;0;2;0;1], [::1;0;2;0;1;0;2]);
      ([::1;0;2;0;1;0;2;0], [::0;1;2;0;1;0;2;1])].

Definition not_S4_cert : pres_cert := [:: add_rel [::1;2;0;1;2;0] [::0;2;1;0;2;1]
     [:: RTriple 10 0 false;
         RTriple 0 9 false;
         RTriple 8 10 false;
         RTriple 10 0 true;
         RTriple 6 9 false;
         RTriple 1 8 true;
         RTriple 1 11 false;
         RTriple 8 6 true;
         RTriple 4 9 false;
         RTriple 0 13 false;
         RTriple 13 14 false;
         RTriple 4 9 true;
         RTriple 3 18 false;
         RTriple 13 8 true;
         RTriple 0 12 false;
         RTriple 5 7 true;
         RTriple 3 12 false;
         RTriple 0 11 true;
         RTriple 3 8 true;
         RTriple 10 10 false;
         RTriple 2 23 false;
         RTriple 13 24 false;
         RTriple 2 23 true;
         RTriple 13 22 true;
         RTriple 4 23 false;
         RTriple 4 29 false;
         RTriple 2 32 false;
         RTriple 10 33 false;
         RTriple 4 29 true;
         RTriple 4 40 false;
         RTriple 13 47 false;
         RTriple 2 46 true;
         RTriple 6 56 false;
         RTriple 13 45 true;
         RTriple 4 40 true;
         RTriple 8 37 true;
         RTriple 5 38 false;
         RTriple 10 27 true;
         RTriple 13 28 false;
         RTriple 4 23 true;
         RTriple 13 22 true;
         RTriple 6 23 false;
         RTriple 1 22 true;
         RTriple 8 20 true;
         RTriple 11 9 true;
         RTriple 0 8 true;
         RTriple 0 9 false;
         RTriple 4 12 false;
         RTriple 0 11 true;
         RTriple 10 14 false;
         RTriple 4 10 true;
         RTriple 3 5 true;
         RTriple 0 4 true;
         RTriple 8 0 true;
         RTriple 13 12 false;
         RTriple 2 11 true;
         RTriple 13 10 true;
         RTriple 0 9 true;
         RTriple 1 8 true;
         RTriple 13 9 false;
         RTriple 2 8 true;
         RTriple 13 7 true;
         RTriple 0 6 true];
     add_rel [::2;1;0;2;1;0] [::0;1;2;0;1;2]
     [:: RTriple 2 0 false;
         RTriple 4 2 false;
         RTriple 13 7 false;
         RTriple 4 2 true;
         RTriple 1 12 false;
         RTriple 13 1 true;
         RTriple 4 4 false;
         RTriple 0 8 false;
         RTriple 13 9 false;
         RTriple 4 4 true;
         RTriple 6 14 false;
         RTriple 9 4 true;
         RTriple 6 2 true;
         RTriple 9 6 false;
         RTriple 5 16 false;
         RTriple 13 5 true;
         RTriple 0 4 true;
         RTriple 4 10 false;
         RTriple 13 17 false;
         RTriple 2 16 true;
         RTriple 6 26 false;
         RTriple 13 15 true;
         RTriple 4 10 true;
         RTriple 6 8 true;
         RTriple 1 8 true;
         RTriple 4 9 false;
         RTriple 0 8 true;
         RTriple 2 10 false;
         RTriple 0 11 false;
         RTriple 13 12 false;
         RTriple 4 7 true;
         RTriple 5 2 true;
         RTriple 1 1 true;
         RTriple 2 0 true;
         RTriple 4 10 false;
         RTriple 4 16 false;
         RTriple 2 19 false;
         RTriple 10 20 false;
         RTriple 4 16 true;
         RTriple 4 27 false;
         RTriple 13 34 false;
         RTriple 2 33 true;
         RTriple 6 43 false;
         RTriple 13 32 true;
         RTriple 4 27 true;
         RTriple 8 24 true;
         RTriple 5 25 false;
         RTriple 10 14 true;
         RTriple 13 15 false;
         RTriple 4 10 true;
         RTriple 13 9 true;
         RTriple 3 6 true;
         RTriple 13 11 false;
         RTriple 2 10 true;
         RTriple 13 9 true;
         RTriple 0 8 true;
         RTriple 13 10 false;
         RTriple 2 9 true;
         RTriple 13 8 true;
         RTriple 1 7 true;
         RTriple 0 6 true];
     add_rel [::2;0;1;2;0;1] [::1;0;2;1;0;2]
     [:: RTriple 1 0 false;
         RTriple 10 2 false;
         RTriple 4 11 false;
         RTriple 8 12 false;
         RTriple 10 2 true;
         RTriple 6 1 true;
         RTriple 2 8 false;
         RTriple 4 10 false;
         RTriple 4 16 false;
         RTriple 2 19 false;
         RTriple 10 20 false;
         RTriple 4 16 true;
         RTriple 4 27 false;
         RTriple 13 34 false;
         RTriple 2 33 true;
         RTriple 6 43 false;
         RTriple 13 32 true;
         RTriple 4 27 true;
         RTriple 8 24 true;
         RTriple 5 25 false;
         RTriple 10 14 true;
         RTriple 13 15 false;
         RTriple 4 10 true;
         RTriple 13 9 true;
         RTriple 2 10 false;
         RTriple 1 11 false;
         RTriple 8 6 true;
         RTriple 4 11 false;
         RTriple 0 10 true;
         RTriple 1 12 false;
         RTriple 2 13 false;
         RTriple 0 14 false;
         RTriple 5 15 false;
         RTriple 13 4 true;
         RTriple 0 3 true;
         RTriple 0 4 false;
         RTriple 2 5 false;
         RTriple 4 9 false;
         RTriple 0 8 true;
         RTriple 13 12 false;
         RTriple 4 7 true;
         RTriple 13 6 true;
         RTriple 10 10 false;
         RTriple 0 9 true;
         RTriple 8 18 false;
         RTriple 10 8 true;
         RTriple 13 12 false;
         RTriple 6 7 true;
         RTriple 13 6 true;
         RTriple 13 17 false;
         RTriple 2 16 true;
         RTriple 13 15 true;
         RTriple 0 14 true;
         RTriple 1 13 true;
         RTriple 13 14 false;
         RTriple 2 13 true;
         RTriple 13 12 true;
         RTriple 0 11 true;
         RTriple 8 6 true];
     add_rel [::2;1;0;2;0] [::1;2;1;0;2]
     [:: RTriple 6 0 false;
         RTriple 2 1 false;
         RTriple 1 2 false;
         RTriple 4 5 false;
         RTriple 0 9 false;
         RTriple 13 10 false;
         RTriple 4 5 true;
         RTriple 13 4 true;
         RTriple 12 9 false;
         RTriple 1 8 true;
         RTriple 2 7 true;
         RTriple 3 16 false;
         RTriple 13 6 true;
         RTriple 0 5 true;
         RTriple 0 8 false;
         RTriple 11 9 false;
         RTriple 3 4 true;
         RTriple 8 14 false;
         RTriple 10 4 true;
         RTriple 6 3 true;
         RTriple 2 4 false;
         RTriple 4 10 false;
         RTriple 2 13 false;
         RTriple 0 14 false;
         RTriple 13 15 false;
         RTriple 4 10 true;
         RTriple 13 9 true;
         RTriple 9 14 false;
         RTriple 11 24 false;
         RTriple 13 13 true;
         RTriple 0 12 true;
         RTriple 2 11 true;
         RTriple 10 6 true;
         RTriple 4 10 false;
         RTriple 13 17 false;
         RTriple 2 16 true;
         RTriple 6 26 false;
         RTriple 13 15 true;
         RTriple 4 10 true;
         RTriple 6 8 true;
         RTriple 1 8 true;
         RTriple 13 11 false;
         RTriple 4 6 true;
         RTriple 13 5 true];
     add_rel [::1;0;2;1;0;2;1] [::2;0;1;2;0]
     [:: RTriple 2 0 false;
         RTriple 0 1 false;
         RTriple 1 2 false;
         RTriple 4 6 false;
         RTriple 2 9 false;
         RTriple 10 10 false;
         RTriple 4 6 true;
         RTriple 8 14 false;
         RTriple 10 4 true;
         RTriple 2 8 false;
         RTriple 6 3 true;
         RTriple 0 17 false;
         RTriple 8 18 false;
         RTriple 10 8 true;
         RTriple 2 7 true;
         RTriple 8 4 true];
     add_rel [::2;0;2] [::0;2;0]
     [:: RTriple 4 0 false;
         RTriple 9 6 false;
         RTriple 11 16 false;
         RTriple 13 5 true;
         RTriple 0 4 true;
         RTriple 2 3 true;
         RTriple 4 14 false;
         RTriple 13 21 false;
         RTriple 2 20 true;
         RTriple 6 30 false;
         RTriple 13 19 true;
         RTriple 4 14 true;
         RTriple 6 12 true;
         RTriple 11 3 true];
     add_rel [::2;1;2] [::1;2;1]
     [:: RTriple 1 0 false;
         RTriple 2 1 false;
         RTriple 4 3 false;
         RTriple 13 8 false;
         RTriple 4 3 true;
         RTriple 1 13 false;
         RTriple 13 2 true;
         RTriple 6 3 true];
     add_rel [::1;0;1] [::0;1;0]
     [:: RTriple 0 0 false;
         RTriple 1 1 false;
         RTriple 0 7 false;
         RTriple 6 8 false;
         RTriple 10 9 false;
         RTriple 5 4 true;
         RTriple 8 13 false;
         RTriple 10 3 true;
         RTriple 8 7 true;
         RTriple 7 9 false;
         RTriple 13 13 false;
         RTriple 4 8 true;
         RTriple 13 7 true;
         RTriple 6 2 true];
     add_rel [::2;0;1;2;1] [::0;2;0;1;2]
     [:: RTriple 4 0 false;
         RTriple 1 3 false;
         RTriple 12 7 false;
         RTriple 2 14 false;
         RTriple 0 15 false;
         RTriple 6 16 false;
         RTriple 9 6 true;
         RTriple 2 9 false;
         RTriple 6 4 true;
         RTriple 4 10 false;
         RTriple 0 9 true;
         RTriple 2 8 true;
         RTriple 13 11 false;
         RTriple 4 6 true;
         RTriple 13 5 true;
         RTriple 13 11 false;
         RTriple 2 10 true;
         RTriple 13 9 true;
         RTriple 3 10 false;
         RTriple 0 9 true;
         RTriple 1 13 false;
         RTriple 4 14 false;
         RTriple 5 9 true;
         RTriple 7 7 true;
         RTriple 10 10 false;
         RTriple 6 23 false;
         RTriple 1 22 true;
         RTriple 8 20 true;
         RTriple 11 9 true;
         RTriple 13 11 false;
         RTriple 6 6 true;
         RTriple 13 5 true];
     add_rel [::1;0;2;0;1;2;0] [::0;1;2;1;0;2;1]
     [:: RTriple 4 0 false;
         RTriple 6 1 false;
         RTriple 2 2 false;
         RTriple 1 3 false;
         RTriple 4 6 false;
         RTriple 0 10 false;
         RTriple 13 11 false;
         RTriple 4 6 true;
         RTriple 13 5 true;
         RTriple 12 10 false;
         RTriple 1 9 true;
         RTriple 2 8 true;
         RTriple 3 17 false;
         RTriple 13 7 true;
         RTriple 0 6 true;
         RTriple 0 9 false;
         RTriple 11 10 false;
         RTriple 3 5 true;
         RTriple 8 15 false;
         RTriple 10 5 true;
         RTriple 6 4 true;
         RTriple 2 5 false;
         RTriple 4 11 false;
         RTriple 2 14 false;
         RTriple 0 15 false;
         RTriple 13 16 false;
         RTriple 4 11 true;
         RTriple 13 10 true;
         RTriple 9 15 false;
         RTriple 11 25 false;
         RTriple 13 14 true;
         RTriple 0 13 true;
         RTriple 2 12 true;
         RTriple 10 7 true;
         RTriple 4 11 false;
         RTriple 13 18 false;
         RTriple 2 17 true;
         RTriple 6 27 false;
         RTriple 13 16 true;
         RTriple 4 11 true;
         RTriple 6 9 true;
         RTriple 3 18 false;
         RTriple 0 17 true;
         RTriple 10 19 false;
         RTriple 6 32 false;
         RTriple 1 31 true;
         RTriple 8 29 true;
         RTriple 10 32 false;
         RTriple 6 45 false;
         RTriple 1 44 true;
         RTriple 8 42 true;
         RTriple 11 31 true;
         RTriple 13 33 false;
         RTriple 4 28 true;
         RTriple 8 29 false;
         RTriple 10 19 true;
         RTriple 1 22 true;
         RTriple 2 21 true;
         RTriple 8 22 false;
         RTriple 10 12 true;
         RTriple 2 11 true;
         RTriple 1 13 true;
         RTriple 2 12 true;
         RTriple 0 14 false;
         RTriple 11 15 false;
         RTriple 3 10 true;
         RTriple 8 20 false;
         RTriple 10 10 true;
         RTriple 6 9 true;
         RTriple 13 12 false;
         RTriple 4 7 true;
         RTriple 13 6 true];
     add_rel [::1;2;0;1;0;2;0] [::0;2;0;1;0;2;1]
     [:: RTriple 10 0 false;
         RTriple 2 1 false;
         RTriple 4 3 false;
         RTriple 2 6 false;
         RTriple 0 7 false;
         RTriple 13 8 false;
         RTriple 4 3 true;
         RTriple 13 2 true;
         RTriple 4 4 false;
         RTriple 13 9 false;
         RTriple 4 4 true;
         RTriple 1 14 false;
         RTriple 13 3 true;
         RTriple 4 9 false;
         RTriple 10 13 false;
         RTriple 4 9 true;
         RTriple 8 17 false;
         RTriple 10 7 true;
         RTriple 2 6 true;
         RTriple 6 4 true;
         RTriple 13 8 false;
         RTriple 2 7 true;
         RTriple 13 6 true;
         RTriple 1 8 false;
         RTriple 0 9 false;
         RTriple 5 4 true;
         RTriple 2 5 false;
         RTriple 4 7 false;
         RTriple 13 12 false;
         RTriple 4 7 true;
         RTriple 1 17 false;
         RTriple 13 6 true;
         RTriple 2 12 false;
         RTriple 6 7 true;
         RTriple 6 15 false;
         RTriple 1 14 true;
         RTriple 1 17 false;
         RTriple 8 12 true;
         RTriple 4 15 false;
         RTriple 0 19 false;
         RTriple 13 20 false;
         RTriple 4 15 true;
         RTriple 3 24 false;
         RTriple 13 14 true;
         RTriple 0 18 false;
         RTriple 5 13 true;
         RTriple 3 18 false;
         RTriple 0 17 true;
         RTriple 3 14 true;
         RTriple 10 16 false;
         RTriple 2 29 false;
         RTriple 13 30 false;
         RTriple 2 29 true;
         RTriple 13 28 true;
         RTriple 4 29 false;
         RTriple 4 35 false;
         RTriple 2 38 false;
         RTriple 10 39 false;
         RTriple 4 35 true;
         RTriple 4 46 false;
         RTriple 13 53 false;
         RTriple 2 52 true;
         RTriple 6 62 false;
         RTriple 13 51 true;
         RTriple 4 46 true;
         RTriple 8 43 true;
         RTriple 5 44 false;
         RTriple 10 33 true;
         RTriple 13 34 false;
         RTriple 4 29 true;
         RTriple 13 28 true;
         RTriple 6 29 false;
         RTriple 1 28 true;
         RTriple 8 26 true;
         RTriple 11 15 true;
         RTriple 0 14 true;
         RTriple 5 10 true;
         RTriple 13 14 false;
         RTriple 2 13 true;
         RTriple 13 12 true;
         RTriple 0 11 true;
         RTriple 1 10 true;
         RTriple 13 13 false;
         RTriple 4 8 true;
         RTriple 13 7 true];
     add_rel [::1;0;2;0;1;0;2;1] [::2;0;1;0;2;0]
     [:: RTriple 2 0 false;
         RTriple 4 2 false;
         RTriple 0 6 false;
         RTriple 13 7 false;
         RTriple 4 2 true;
         RTriple 13 1 true;
         RTriple 9 4 false;
         RTriple 5 14 false;
         RTriple 13 3 true;
         RTriple 0 2 true;
         RTriple 4 3 false;
         RTriple 9 9 false;
         RTriple 11 19 false;
         RTriple 13 8 true;
         RTriple 0 7 true;
         RTriple 2 6 true;
         RTriple 4 17 false;
         RTriple 4 24 false;
         RTriple 0 23 true;
         RTriple 13 24 false;
         RTriple 2 23 true;
         RTriple 6 33 false;
         RTriple 13 22 true;
         RTriple 4 17 true;
         RTriple 6 15 true;
         RTriple 11 6 true;
         RTriple 4 12 false;
         RTriple 10 18 false;
         RTriple 0 27 false;
         RTriple 8 28 false;
         RTriple 10 18 true;
         RTriple 13 19 false;
         RTriple 2 18 true;
         RTriple 6 28 false;
         RTriple 13 17 true;
         RTriple 4 12 true;
         RTriple 6 10 true;
         RTriple 1 10 true;
         RTriple 6 17 false;
         RTriple 1 16 true;
         RTriple 8 14 true;
         RTriple 2 18 false;
         RTriple 4 13 true;
         RTriple 10 6 true];
     add_rel [::2;0;1;0;2;1;0] [::0;1;2;0;1;0;2]
     [:: RTriple 4 0 false;
         RTriple 0 4 false;
         RTriple 13 5 false;
         RTriple 4 0 true;
         RTriple 4 7 false;
         RTriple 0 6 true;
         RTriple 2 5 true;
         RTriple 10 10 false;
         RTriple 0 19 false;
         RTriple 8 20 false;
         RTriple 10 10 true;
         RTriple 13 14 false;
         RTriple 6 9 true;
         RTriple 13 8 true;
         RTriple 0 7 true;
         RTriple 13 17 false;
         RTriple 2 16 true;
         RTriple 13 15 true;
         RTriple 0 14 true;
         RTriple 1 16 false;
         RTriple 3 11 true;
         RTriple 1 13 false;
         RTriple 8 8 true;
         RTriple 10 9 false;
         RTriple 6 22 false;
         RTriple 1 21 true;
         RTriple 8 19 true;
         RTriple 11 8 true;
         RTriple 0 7 true];
     add_rel [::2;0;1;0;2;0;1] [::1;0;2;0;1;0;2]
     [:: RTriple 4 0 false;
         RTriple 2 3 false;
         RTriple 10 4 false;
         RTriple 4 0 true;
         RTriple 2 2 false;
         RTriple 4 4 false;
         RTriple 2 7 false;
         RTriple 0 8 false;
         RTriple 13 9 false;
         RTriple 4 4 true;
         RTriple 13 3 true;
         RTriple 4 5 false;
         RTriple 13 10 false;
         RTriple 4 5 true;
         RTriple 1 15 false;
         RTriple 13 4 true;
         RTriple 4 10 false;
         RTriple 10 14 false;
         RTriple 4 10 true;
         RTriple 8 18 false;
         RTriple 10 8 true;
         RTriple 2 7 true;
         RTriple 6 5 true;
         RTriple 13 9 false;
         RTriple 2 8 true;
         RTriple 13 7 true;
         RTriple 1 9 false;
         RTriple 0 10 false;
         RTriple 5 5 true;
         RTriple 2 9 false;
         RTriple 4 11 false;
         RTriple 13 16 false;
         RTriple 4 11 true;
         RTriple 1 21 false;
         RTriple 13 10 true;
         RTriple 2 11 false;
         RTriple 6 6 true;
         RTriple 4 13 false;
         RTriple 13 20 false;
         RTriple 2 19 true;
         RTriple 6 29 false;
         RTriple 13 18 true;
         RTriple 4 13 true;
         RTriple 8 10 true;
         RTriple 13 15 false;
         RTriple 2 14 true;
         RTriple 13 13 true;
         RTriple 0 12 true;
         RTriple 1 11 true;
         RTriple 0 13 false;
         RTriple 13 14 false;
         RTriple 4 9 true;
         RTriple 6 19 false;
         RTriple 9 9 true;
         RTriple 6 7 true;
         RTriple 3 10 false;
         RTriple 0 9 true;
         RTriple 5 7 true;
         RTriple 10 8 false;
         RTriple 6 21 false;
         RTriple 1 20 true;
         RTriple 8 18 true;
         RTriple 11 7 true];
     add_rel [::1;0;2;0;1;0;2;0] [::0;1;2;0;1;0;2;1]
     [:: RTriple 4 0 false;
         RTriple 6 1 false;
         RTriple 2 2 false;
         RTriple 4 4 false;
         RTriple 2 7 false;
         RTriple 0 8 false;
         RTriple 13 9 false;
         RTriple 4 4 true;
         RTriple 13 3 true;
         RTriple 4 5 false;
         RTriple 13 10 false;
         RTriple 4 5 true;
         RTriple 1 15 false;
         RTriple 13 4 true;
         RTriple 4 10 false;
         RTriple 10 14 false;
         RTriple 4 10 true;
         RTriple 8 18 false;
         RTriple 10 8 true;
         RTriple 2 7 true;
         RTriple 6 5 true;
         RTriple 1 7 false;
         RTriple 2 10 false;
         RTriple 13 11 false;
         RTriple 2 10 true;
         RTriple 13 9 true;
         RTriple 4 10 false;
         RTriple 0 14 false;
         RTriple 13 15 false;
         RTriple 4 10 true;
         RTriple 13 9 true;
         RTriple 12 14 false;
         RTriple 1 13 true;
         RTriple 2 12 true;
         RTriple 3 21 false;
         RTriple 13 11 true;
         RTriple 0 10 true;
         RTriple 0 13 false;
         RTriple 11 14 false;
         RTriple 3 9 true;
         RTriple 8 19 false;
         RTriple 10 9 true;
         RTriple 6 8 true;
         RTriple 1 9 false;
         RTriple 0 10 false;
         RTriple 5 5 true;
         RTriple 2 6 false;
         RTriple 4 8 false;
         RTriple 13 13 false;
         RTriple 4 8 true;
         RTriple 1 18 false;
         RTriple 13 7 true;
         RTriple 2 11 false;
         RTriple 4 17 false;
         RTriple 2 20 false;
         RTriple 0 21 false;
         RTriple 13 22 false;
         RTriple 4 17 true;
         RTriple 13 16 true;
         RTriple 9 21 false;
         RTriple 11 31 false;
         RTriple 13 20 true;
         RTriple 0 19 true;
         RTriple 2 18 true;
         RTriple 10 13 true;
         RTriple 4 17 false;
         RTriple 13 24 false;
         RTriple 2 23 true;
         RTriple 6 33 false;
         RTriple 13 22 true;
         RTriple 4 17 true;
         RTriple 6 15 true;
         RTriple 4 20 false;
         RTriple 2 23 false;
         RTriple 10 24 false;
         RTriple 4 20 true;
         RTriple 4 31 false;
         RTriple 13 38 false;
         RTriple 2 37 true;
         RTriple 6 47 false;
         RTriple 13 36 true;
         RTriple 4 31 true;
         RTriple 8 28 true;
         RTriple 2 32 false;
         RTriple 13 33 false;
         RTriple 2 32 true;
         RTriple 13 31 true;
         RTriple 4 32 false;
         RTriple 2 35 false;
         RTriple 0 36 false;
         RTriple 13 37 false;
         RTriple 4 32 true;
         RTriple 13 31 true;
         RTriple 0 30 true;
         RTriple 4 31 false;
         RTriple 13 36 false;
         RTriple 4 31 true;
         RTriple 1 41 false;
         RTriple 13 30 true;
         RTriple 1 29 true;
         RTriple 3 38 false;
         RTriple 0 37 true;
         RTriple 10 39 false;
         RTriple 9 48 false;
         RTriple 8 49 false;
         RTriple 10 39 true;
         RTriple 4 41 false;
         RTriple 8 42 false;
         RTriple 10 32 true;
         RTriple 2 31 true;
         RTriple 6 29 true;
         RTriple 2 30 false;
         RTriple 0 31 false;
         RTriple 13 32 false;
         RTriple 4 27 true;
         RTriple 8 28 false;
         RTriple 10 18 true;
         RTriple 2 17 true;
         RTriple 1 19 true;
         RTriple 2 18 true;
         RTriple 0 20 false;
         RTriple 11 21 false;
         RTriple 3 16 true;
         RTriple 8 26 false;
         RTriple 10 16 true;
         RTriple 6 15 true;
         RTriple 13 18 false;
         RTriple 4 13 true;
         RTriple 13 12 true;
         RTriple 6 8 true;
         RTriple 4 12 false;
         RTriple 4 18 false;
         RTriple 2 21 false;
         RTriple 10 22 false;
         RTriple 4 18 true;
         RTriple 4 29 false;
         RTriple 13 36 false;
         RTriple 2 35 true;
         RTriple 6 45 false;
         RTriple 13 34 true;
         RTriple 4 29 true;
         RTriple 8 26 true;
         RTriple 5 27 false;
         RTriple 10 16 true;
         RTriple 13 17 false;
         RTriple 4 12 true;
         RTriple 13 11 true;
         RTriple 3 8 true;
         RTriple 2 12 false;
         RTriple 13 13 false;
         RTriple 2 12 true;
         RTriple 13 11 true;
         RTriple 4 12 false;
         RTriple 2 15 false;
         RTriple 0 16 false;
         RTriple 13 17 false;
         RTriple 4 12 true;
         RTriple 13 11 true;
         RTriple 0 10 true;
         RTriple 4 11 false;
         RTriple 13 16 false;
         RTriple 4 11 true;
         RTriple 1 21 false;
         RTriple 13 10 true;
         RTriple 1 9 true;
         RTriple 4 14 false;
         RTriple 10 18 false;
         RTriple 4 14 true;
         RTriple 8 22 false;
         RTriple 10 12 true;
         RTriple 2 11 true;
         RTriple 6 9 true;
         RTriple 13 13 false;
         RTriple 2 12 true;
         RTriple 13 11 true;
         RTriple 1 14 true;
         RTriple 2 13 true;
         RTriple 3 22 false;
         RTriple 13 12 true;
         RTriple 0 11 true;
         RTriple 0 14 false;
         RTriple 5 9 true;
         RTriple 0 8 true;
         RTriple 10 11 false;
         RTriple 0 20 false;
         RTriple 8 21 false;
         RTriple 10 11 true;
         RTriple 8 9 true;
         RTriple 0 8 true;
         RTriple 6 12 false;
         RTriple 1 11 true;
         RTriple 8 9 true;
         RTriple 2 11 false;
         RTriple 4 13 false;
         RTriple 13 18 false;
         RTriple 4 13 true;
         RTriple 10 26 false;
         RTriple 6 39 false;
         RTriple 1 38 true;
         RTriple 8 36 true;
         RTriple 11 25 true;
         RTriple 2 28 false;
         RTriple 0 29 false;
         RTriple 13 30 false;
         RTriple 4 25 true;
         RTriple 6 35 false;
         RTriple 9 25 true;
         RTriple 6 23 true;
         RTriple 13 12 true;
         RTriple 4 8 true];
     rm_rel 3
     [:: RTriple 21 1 true;
         RTriple 0 0 true;
         RTriple 0 1 true;
         RTriple 1 0 true];
     rm_rel 3
     [:: RTriple 18 1 true;
         RTriple 0 0 true;
         RTriple 0 1 true;
         RTriple 2 0 true];
     rm_rel 3
     [:: RTriple 19 0 true;
         RTriple 0 2 true;
         RTriple 1 1 true;
         RTriple 0 0 true];
     rm_rel 3
     [:: RTriple 17 1 true;
         RTriple 1 0 true;
         RTriple 1 1 true;
         RTriple 2 0 true];
     rm_rel 3
     [:: RTriple 15 0 true;
         RTriple 0 2 true;
         RTriple 2 1 true;
         RTriple 0 0 true];
     rm_rel 3
     [:: RTriple 15 0 true;
         RTriple 1 2 true;
         RTriple 2 1 true;
         RTriple 1 0 true];
     rm_rel 3
     [:: RTriple 8 1 true;
         RTriple 0 0 true;
         RTriple 1 4 true;
         RTriple 2 3 true;
         RTriple 0 2 true;
         RTriple 1 1 true;
         RTriple 2 0 true];
     rm_rel 3
     [:: RTriple 8 1 true;
         RTriple 0 0 true;
         RTriple 2 4 true;
         RTriple 1 3 true;
         RTriple 0 2 true;
         RTriple 2 1 true;
         RTriple 1 0 true];
     rm_rel 3
     [:: RTriple 7 2 true;
         RTriple 0 1 true;
         RTriple 1 0 true;
         RTriple 2 3 true;
         RTriple 1 2 true;
         RTriple 0 1 true;
         RTriple 2 0 true];
     rm_rel 3
     [:: RTriple 5 0 true;
         RTriple 1 5 true;
         RTriple 2 4 true;
         RTriple 0 3 true;
         RTriple 1 2 true;
         RTriple 2 1 true;
         RTriple 0 0 true];
     rm_rel 3
     [:: RTriple 4 2 true;
         RTriple 0 1 true;
         RTriple 2 0 true;
         RTriple 1 3 true;
         RTriple 2 2 true;
         RTriple 0 1 true;
         RTriple 1 0 true];
     rm_rel 3
     [:: RTriple 4 0 true;
         RTriple 2 5 true;
         RTriple 1 4 true;
         RTriple 0 3 true;
         RTriple 2 2 true;
         RTriple 1 1 true;
         RTriple 0 0 true]].

Definition not_S4_order := [::0;1;2].

(*
Eval compute in size (prelat not_S4).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat not_S4)].
Eval compute in size (prelat not_S4_rws).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat not_S4_rws)].
Eval compute in size not_S4_cert.

Time Eval compute in foldl (fun acc s => acc + size_int s) 0
  (traject (enum_normal_next_trie not_S4_rws) [:: [::]] 30).
*)


Theorem isopres_not_S4 : isopres not_S4 not_S4_rws.
Proof.
have wfc : wfpres_cert not_S4 not_S4_cert by vm_cast_no_check is_true_true.
suff -> : not_S4_rws = final_pres wfc by apply: iso_final_pres.
apply/eqP; rewrite -eqpresE pgen_final_pres prelat_final_pres.
by vm_cast_no_check is_true_true.
Time Qed.

Theorem not_S4_rws_convergent : convergent (prelat not_S4_rws).
Proof.
apply: diamond.
  apply: (rgen_pres_terminating
            (newgK := reorderK (l := not_S4_order) is_true_true)).
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
have pgenOk : all (<%O^~ PArray.max_length) (pgen not_S4_rws) by [].
apply: (spair_confluence_loop_trieP pgenOk (fuel := 10)).
rewrite spair_confluence_loop_trieE.
by native_cast_no_check is_true_true.
Time Qed.


Theorem not_iso_S4 : isopres S4_Moore not_S4 -> False.
Proof.
move=> isoS4.
have {}: isopres S4_rws not_S4_rws.
  apply: (isopres_trans (isopres_sym isopres_S4)).
  exact: (isopres_trans isoS4 isopres_not_S4).
evar (rew_S4 : word int -> option (word int)).
have rew_S4P : rewrites1_Ok (prelat S4_rws) rew_S4.
  exact: (trie_rewrites1P (trielen := 3)).
evar (rew_not_S4 : word int -> option (word int)).
have rew_not_S4P : rewrites1_Ok (prelat not_S4_rws) rew_not_S4.
  exact: (trie_rewrites1P (trielen := 3)).
apply: (size_non_isopres rew_S4P rew_not_S4P
          S4_rws_convergent not_S4_rws_convergent (boundP := 10) (boundQ := 15)).
- by native_cast_no_check is_true_true.
- rewrite ltnNge -flatten_is_longerE.
  by native_cast_no_check is_true_true.
Time Qed.
