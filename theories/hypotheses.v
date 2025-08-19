(** * Dealing with admitted results *)
(******************************************************************************)
(*      Copyright (C) 2025      Florent Hivert <florent.hivert@lri.fr>        *)
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
From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq eqtype
  choice path bigop tuple.


Require Import present int_seq monoids factor well_founded criteria compress.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Essai.

Variable Alph : choiceType.

Definition WPDec (P : pres Alph) :=
  forall dec : seq Alph -> seq Alph -> bool,
  forall u v, u \in words_of P -> v \in words_of P ->
    (dec u v) <-> (u = v %[mod P]).

Definition WPDecProof (P : pres Alph) := forall (T : Type) (H : T), WPDec P.

Variable Hyp_list : seq (forall P, WPDecProof P).

Definition get_Hyp (m : bitseq) := (mask m Hyp_list).

Fixpoint fold_hyp s res :=
  if s is Hyp :: s' then Hyp -> fold_hyp s' res else res.

Definition get_Hyp (m : bitseq) :=
  fold_hyp (mask m Hyp_list).



    reflect (u = v %[mod P]) (dec u v).

Definition Hyp_list : seq Type := [::
   Hyp_cycle_free_1rel_dec;
   Hyp_left_cycle_free_1rel_same_number_occ_dec;
   Hyp_c3_monoid_dec;
   Hyp_is_Watier_dec;
   Hyp_special_dec;
   Hyp_strong_compress_dec;
   Hyp_reduce2letters_dec
  ].

Fixpoint fold_hyp s res :=
  if s is Hyp :: s' then Hyp -> fold_hyp s' res else res.

Definition get_Hyp (m : bitseq) :=
  fold_hyp (mask m Hyp_list).

Eval compute in FoldHyp HypList True.


Variable P : pres int.
Variable H : Hyp_cycle_free_1rel_dec.

Check (H (P := P)).


Definition bla := map (fun H => H  P) HypList.

Check WPdecidable P : Prop.

