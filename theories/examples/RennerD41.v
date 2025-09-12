(** * Presentation of the Renner monoid of Cartan type D4 *)
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

Definition not_RennerD41 := make_pres [::0;1;2;3;4;5;6;7;8;9]
    [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::3;3], [::]);
      ([::1;3], [::3;1]);
      ([::0;3], [::3;0]);
      ([::0;1], [::1;0]);
      ([::1;2;1], [::2;1;2]);
      ([::2;3;2], [::3;2;3]);
      ([::0;2;0], [::2;0;2]);
      ([::2;4], [::4;2]);
      ([::2;5], [::5;2]);
      ([::2;6], [::6;2]);
      ([::3;4], [::4;3]);
      ([::3;5], [::5;3]);
      ([::3;7], [::7;3]);
      ([::3;6], [::6;3]);
      ([::0;6], [::6;0]);
      ([::1;4], [::4;1]);
      ([::1;7], [::7;1]);
      ([::1;7], [::7]);
      ([::0;7], [::7;0]);
      ([::0;7], [::7]);
      ([::1;8], [::8;1]);
      ([::1;8], [::8]);
      ([::0;8], [::8;0]);
      ([::0;8], [::8]);
      ([::1;9], [::9;1]);
      ([::1;9], [::9]);
      ([::0;9], [::9;0]);
      ([::0;9], [::9]);
      ([::2;8], [::8;2]);
      ([::2;8], [::8]);
      ([::2;9], [::9;2]);
      ([::2;9], [::9]);
      ([::3;9], [::9;3]);
      ([::3;9], [::9]);
      ([::4;4], [::4;4]);
      ([::4;4], [::4]);
      ([::4;5], [::5;4]);
      ([::4;5], [::5]);
      ([::4;7], [::7;4]);
      ([::4;7], [::7]);
      ([::4;8], [::8;4]);
      ([::4;8], [::8]);
      ([::4;9], [::9;4]);
      ([::4;9], [::9]);
      ([::5;4], [::4;5]);
      ([::5;4], [::5]);
      ([::5;5], [::5;5]);
      ([::5;5], [::5]);
      ([::5;7], [::7;5]);
      ([::5;7], [::7]);
      ([::5;8], [::8;5]);
      ([::5;8], [::8]);
      ([::5;9], [::9;5]);
      ([::5;9], [::9]);
      ([::7;4], [::4;7]);
      ([::7;4], [::7]);
      ([::7;5], [::5;7]);
      ([::7;5], [::7]);
      ([::7;7], [::7;7]);
      ([::7;7], [::7]);
      ([::7;8], [::8;7]);
      ([::7;8], [::8]);
      ([::7;9], [::9;7]);
      ([::7;9], [::9]);
      ([::6;7], [::7;6]);
      ([::6;7], [::7]);
      ([::8;4], [::4;8]);
      ([::8;4], [::8]);
      ([::8;5], [::5;8]);
      ([::8;5], [::8]);
      ([::8;7], [::7;8]);
      ([::8;7], [::8]);
      ([::8;8], [::8;8]);
      ([::8;8], [::8]);
      ([::8;9], [::9;8]);
      ([::8;9], [::9]);
      ([::6;8], [::8;6]);
      ([::6;8], [::8]);
      ([::9;4], [::4;9]);
      ([::9;4], [::9]);
      ([::9;5], [::5;9]);
      ([::9;5], [::9]);
      ([::9;7], [::7;9]);
      ([::9;7], [::9]);
      ([::9;8], [::8;9]);
      ([::9;8], [::9]);
      ([::9;9], [::9;9]);
      ([::9;9], [::9]);
      ([::6;9], [::9;6]);
      ([::6;9], [::9]);
      ([::6;6], [::6]);
      ([::6;4], [::5]);
      ([::4;6], [::5]);
      ([::7;2;7], [::8]);
      ([::8;3;8], [::9]);
      ([::4;0;4], [::7]);
      ([::6;1;6], [::7]);
      ([::4;0;2;1;6], [::8]);
      ([::6;1;2;0;4], [::8])].

Definition RennerD41_Gay :=
  make_pres (pgen not_RennerD41)
    (take 100 (prelat not_RennerD41) ++ (* Exchange the two last relations *)
       [:: ([::6;1;2;0;4], [::8]);
           ([::4;0;2;1;6], [::8]);
           ([::6;1;2;3;0;2;1;6], [::9]);
           ([::4;0;2;3;1;2;0;4], [::9])]).

Definition RennerD41_Gay_rws := make_pres [::0;1;2;3;4;5;6;7;8;9]
  [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::3;3], [::]);
      ([::1;7], [::7]);
      ([::0;7], [::7]);
      ([::1;8], [::8]);
      ([::0;8], [::8]);
      ([::1;9], [::9]);
      ([::0;9], [::9]);
      ([::2;8], [::8]);
      ([::2;9], [::9]);
      ([::3;9], [::9]);
      ([::4;4], [::4]);
      ([::4;5], [::5]);
      ([::4;7], [::7]);
      ([::4;8], [::8]);
      ([::4;9], [::9]);
      ([::5;4], [::5]);
      ([::5;5], [::5]);
      ([::5;7], [::7]);
      ([::5;8], [::8]);
      ([::5;9], [::9]);
      ([::7;4], [::7]);
      ([::7;5], [::7]);
      ([::7;7], [::7]);
      ([::7;8], [::8]);
      ([::7;9], [::9]);
      ([::6;7], [::7]);
      ([::8;4], [::8]);
      ([::8;5], [::8]);
      ([::8;7], [::8]);
      ([::8;8], [::8]);
      ([::8;9], [::9]);
      ([::6;8], [::8]);
      ([::9;4], [::9]);
      ([::9;5], [::9]);
      ([::9;7], [::9]);
      ([::9;8], [::9]);
      ([::9;9], [::9]);
      ([::6;9], [::9]);
      ([::6;6], [::6]);
      ([::6;4], [::5]);
      ([::4;6], [::5]);
      ([::7;2;7], [::8]);
      ([::8;3;8], [::9]);
      ([::4;0;4], [::7]);
      ([::6;1;6], [::7]);
      ([::6;1;2;0;4], [::8]);
      ([::4;0;2;1;6], [::8]);
      ([::9;6], [::9]);
      ([::8;6], [::8]);
      ([::7;6], [::7]);
      ([::9;3], [::9]);
      ([::9;2], [::9]);
      ([::8;2], [::8]);
      ([::9;0], [::9]);
      ([::9;1], [::9]);
      ([::8;0], [::8]);
      ([::8;1], [::8]);
      ([::7;0], [::7]);
      ([::7;1], [::7]);
      ([::4;1], [::1;4]);
      ([::6;0], [::0;6]);
      ([::6;3], [::3;6]);
      ([::7;3], [::3;7]);
      ([::5;3], [::3;5]);
      ([::4;3], [::3;4]);
      ([::6;2], [::2;6]);
      ([::5;2], [::2;5]);
      ([::4;2], [::2;4]);
      ([::2;0;2], [::0;2;0]);
      ([::3;2;3], [::2;3;2]);
      ([::2;1;2], [::1;2;1]);
      ([::1;0], [::0;1]);
      ([::3;0], [::0;3]);
      ([::6;1;2;0;3;2;1;6], [::9]);
      ([::3;1], [::1;3]);
      ([::4;0;2;1;3;2;0;4], [::9]);
      ([::5;6], [::5]);
      ([::6;5], [::5]);
      ([::4;0;2;1;5], [::8]);
      ([::5;0;2;1;6], [::8]);
      ([::6;1;5], [::7]);
      ([::5;0;4], [::7]);
      ([::6;1;2;0;5], [::8]);
      ([::5;1;2;0;4], [::8]);
      ([::5;1;6], [::7]);
      ([::4;0;5], [::7]);
      ([::7;2;1;6], [::8]);
      ([::6;1;2;7], [::8]);
      ([::4;0;2;7], [::8]);
      ([::7;2;0;4], [::8]);
      ([::0;3;7], [::3;7]);
      ([::1;3;7], [::3;7]);
      ([::4;0;2;1;3;6], [::8;3]);
      ([::8;3;6], [::8;3]);
      ([::4;0;6], [::5;0]);
      ([::6;1;4], [::5;1]);
      ([::5;1;4], [::5;1]);
      ([::5;0;2;1;3;2;0;4], [::9]);
      ([::8;3;2;0;4], [::9]);
      ([::7;2;1;3;2;0;4], [::9]);
      ([::4;0;2;1;3;2;7], [::9]);
      ([::4;0;2;1;3;2;0;5], [::9]);
      ([::1;3;8], [::3;8]);
      ([::4;0;2;3;8], [::9]);
      ([::6;1;3], [::3;6;1]);
      ([::5;1;3], [::3;5;1]);
      ([::3;2;1;3], [::2;3;2;1]);
      ([::8;3;2;1;6], [::9]);
      ([::7;2;0;3;2;1;6], [::9]);
      ([::6;1;2;0;3;2;7], [::9]);
      ([::5;1;2;0;3;2;1;6], [::9]);
      ([::6;1;2;0;3;2;1;5], [::9]);
      ([::0;3;8], [::3;8]);
      ([::6;1;2;3;8], [::9]);
      ([::5;0;3], [::3;5;0]);
      ([::4;0;3], [::3;4;0]);
      ([::3;2;0;3], [::2;3;2;0]);
      ([::4;0;1], [::1;4;0]);
      ([::6;1;2;1], [::2;6;1;2]);
      ([::5;1;2;1], [::2;5;1;2]);
      ([::2;0;1;2;1], [::0;2;0;1;2]);
      ([::2;0;1;2;0], [::1;2;0;1;2]);
      ([::7;2;3;2], [::3;7;2;3]);
      ([::5;0;2;0], [::2;5;0;2]);
      ([::4;0;2;0], [::2;4;0;2]);
      ([::4;0;2;4], [::7;2]);
      ([::7;2;4], [::7;2]);
      ([::7;2;5], [::7;2]);
      ([::6;1;2;6], [::7;2]);
      ([::7;2;6], [::7;2]);
      ([::6;1;2;0;3;4], [::8;3]);
      ([::8;3;4], [::8;3]);
      ([::8;3;5], [::8;3]);
      ([::7;2;3;7], [::8;3]);
      ([::8;3;7], [::8;3]);
      ([::7;2;1;5], [::8]);
      ([::5;1;5], [::7]);
      ([::6;1;2;5], [::7;2]);
      ([::5;0;2;7], [::8]);
      ([::5;0;2;1;5], [::8]);
      ([::5;0;2;1;3;6], [::8;3]);
      ([::5;0;1;2;1;6], [::8]);
      ([::4;0;2;1;3;5], [::8;3]);
      ([::5;0;6], [::5;0]);
      ([::7;2;0;1;6], [::8]);
      ([::7;2;1;3;6], [::8;3]);
      ([::5;0;5], [::7]);
      ([::4;0;2;5], [::7;2]);
      ([::5;1;2;7], [::8]);
      ([::5;0;1;6], [::7]);
      ([::5;1;2;6], [::7;2]);
      ([::7;2;0;5], [::8]);
      ([::5;1;2;0;5], [::8]);
      ([::5;1;2;0;3;4], [::8;3]);
      ([::5;0;1;2;0;4], [::8]);
      ([::6;1;2;0;3;5], [::8;3]);
      ([::5;0;1;4], [::7]);
      ([::5;0;2;4], [::7;2]);
      ([::4;0;2;3;7], [::8;3]);
      ([::4;0;2;1;3;2;6], [::8;3;2]);
      ([::8;3;2;0;1;6], [::9]);
      ([::8;3;2;0;5], [::9]);
      ([::8;3;2;7], [::9]);
      ([::7;2;0;1;4], [::8]);
      ([::7;2;0;3;4], [::8;3]);
      ([::6;1;2;3;7], [::8;3]);
      ([::5;1;2;4], [::5;1;2]);
      ([::5;0;1;2;1;3;2;0;4], [::9]);
      ([::5;0;1;2;1;5], [::8]);
      ([::5;0;1;5], [::7]);
      ([::5;0;1;2;7], [::8]);
      ([::5;0;1;2;1;3;6], [::8;3]);
      ([::6;1;2;4], [::5;1;2]);
      ([::8;3;2;0;1;4], [::9]);
      ([::5;0;1;2;0;1;4], [::8]);
      ([::4;0;2;6], [::5;0;2]);
      ([::5;0;1;2;0;3;2;1;6], [::9]);
      ([::5;0;1;2;0;5], [::8]);
      ([::8;3;2;6], [::8;3;2]);
      ([::5;0;1;2;1;3;2;0;5], [::9]);
      ([::7;2;1;3;2;7], [::9]);
      ([::5;0;2;1;3;2;7], [::9]);
      ([::5;0;1;2;1;3;2;7], [::9]);
      ([::7;2;3;8], [::9]);
      ([::7;2;1;3;2;0;5], [::9]);
      ([::7;2;0;1;3;2;0;4], [::9]);
      ([::5;0;2;3;8], [::9]);
      ([::5;0;2;1;3;2;0;5], [::9]);
      ([::6;1;2;3;2], [::3;6;1;2;3]);
      ([::5;0;1;3], [::3;5;0;1]);
      ([::5;0;1;2;3;8], [::9]);
      ([::5;1;2;0;3;2;7], [::9]);
      ([::7;2;0;3;2;7], [::9]);
      ([::5;0;1;2;0;3;2;7], [::9]);
      ([::7;2;0;3;2;1;5], [::9]);
      ([::7;2;0;1;3;2;1;6], [::9]);
      ([::8;3;2;1;5], [::9]);
      ([::3;2;0;1;3], [::2;3;2;0;1]);
      ([::5;1;2;3;2], [::3;5;1;2;3]);
      ([::8;3;2;0;1;2;6], [::9]);
      ([::5;0;1;2;0;1;3;2;1;6], [::9]);
      ([::5;1;2;0;3;2;1;5], [::9]);
      ([::8;3;2;0;1;5], [::9]);
      ([::5;0;1;2;0;3;2;1;5], [::9]);
      ([::5;1;2;3;8], [::9]);
      ([::4;0;2;3;2], [::3;4;0;2;3]);
      ([::5;0;2;3;2], [::3;5;0;2;3]);
      ([::7;2;1;3;2;1], [::3;7;2;1;3;2]);
      ([::1;2;0;1;2;7], [::2;0;1;2;7]);
      ([::1;2;0;1;2;3;7], [::2;0;1;2;3;7]);
      ([::1;2;0;1;2;3;8], [::2;0;1;2;3;8]);
      ([::0;2;0;1;2;7], [::2;0;1;2;7]);
      ([::0;2;0;1;2;3;7], [::2;0;1;2;3;7]);
      ([::0;2;0;1;2;3;8], [::2;0;1;2;3;8]);
      ([::5;1;2;0;1], [::2;5;1;2;0]);
      ([::6;1;2;0;1], [::2;6;1;2;0]);
      ([::7;2;1;4], [::7;2;1]);
      ([::7;2;3;4], [::7;2;3]);
      ([::7;2;0;1;5], [::8]);
      ([::7;2;0;1;3;6], [::8;3]);
      ([::7;2;0;6], [::7;2;0]);
      ([::7;2;0;1;3;2;7], [::9]);
      ([::7;2;0;1;3;2;0;5], [::9]);
      ([::7;2;0;1;3;2;0;1;4], [::9]);
      ([::4;0;2;1;4], [::7;2;1]);
      ([::4;0;2;3;4], [::7;2;3]);
      ([::5;0;1;2;4], [::7;2]);
      ([::5;0;1;2;0;1;2], [::2;5;0;1;2;0;1]);
      ([::7;2;0;3;2;0], [::3;7;2;0;3;2]);
      ([::8;3;2;4], [::8;3;2]);
      ([::7;2;0;1;3;4], [::8;3]);
      ([::7;2;3;6], [::7;2;3]);
      ([::7;2;0;1;3;2;1;5], [::9]);
      ([::7;2;0;1;3;2;0;1;6], [::9]);
      ([::6;1;2;0;6], [::7;2;0]);
      ([::6;1;2;3;6], [::7;2;3]);
      ([::5;0;1;2;6], [::7;2]);
      ([::7;2;3;5], [::7;2;3]);
      ([::8;3;2;5], [::8;3;2]);
      ([::6;1;2;0;3;2;4], [::8;3;2]);
      ([::5;0;1;2;0;3;4], [::8;3]);
      ([::5;0;1;2;5], [::7;2]);
      ([::5;1;2;5], [::7;2]);
      ([::7;2;1;3;5], [::8;3]);
      ([::5;0;2;3;7], [::8;3]);
      ([::5;0;2;1;3;2;6], [::8;3;2]);
      ([::5;0;2;1;3;5], [::8;3]);
      ([::6;1;2;3;5], [::7;2;3]);
      ([::5;0;2;6], [::5;0;2]);
      ([::4;0;2;1;3;2;5], [::8;3;2]);
      ([::5;0;1;2;1;3;5], [::8;3]);
      ([::7;2;0;1;3;5], [::8;3]);
      ([::5;0;1;2;0;1;6], [::8]);
      ([::7;2;0;1;2;6], [::8]);
      ([::5;0;2;5], [::7;2]);
      ([::7;2;1;3;2;6], [::8;3;2]);
      ([::5;1;2;3;7], [::8;3]);
      ([::4;0;2;3;5], [::7;2;3]);
      ([::7;2;0;3;5], [::8;3]);
      ([::5;1;2;0;6], [::7;2;0]);
      ([::5;1;2;3;6], [::7;2;3]);
      ([::7;2;0;1;2;4], [::8]);
      ([::5;1;2;0;3;5], [::8;3]);
      ([::5;1;2;0;3;2;4], [::8;3;2]);
      ([::6;1;2;0;3;2;5], [::8;3;2]);
      ([::5;0;1;2;0;3;5], [::8;3]);
      ([::5;0;1;2;1;3;2;6], [::8;3;2]);
      ([::8;3;2;1;4], [::8;3;2;1]);
      ([::8;3;2;0;1;2;7], [::9]);
      ([::8;3;2;0;1;2;5], [::9]);
      ([::7;2;0;1;3;2;6], [::8;3;2]);
      ([::5;0;1;2;3;7], [::8;3]);
      ([::5;0;2;1;4], [::7;2;1]);
      ([::5;0;2;3;4], [::7;2;3]);
      ([::4;0;2;1;3;2;0;6], [::8;3;2;0]);
      ([::7;2;0;3;2;4], [::8;3;2]);
      ([::5;0;1;2;0;1;3;2;0;4], [::9]);
      ([::7;2;0;1;2;3;2;0;4], [::9]);
      ([::5;1;2;3;4], [::5;1;2;3]);
      ([::5;0;1;2;0;1;5], [::8]);
      ([::5;0;1;2;0;1;3;6], [::8;3]);
      ([::5;0;1;2;0;1;3;2;7], [::9]);
      ([::5;0;1;2;0;1;3;2;0;5], [::9]);
      ([::5;0;1;2;0;1;3;2;0;1;4], [::9]);
      ([::5;0;1;2;0;1;3;5], [::8;3]);
      ([::5;0;1;2;0;1;3;2;6], [::8;3;2]);
      ([::7;2;0;1;2;5], [::8]);
      ([::7;2;0;1;2;3;6], [::8;3]);
      ([::7;2;0;1;2;7], [::8]);
      ([::8;3;2;0;1;2;4], [::9]);
      ([::6;1;2;3;4], [::5;1;2;3]);
      ([::7;2;0;1;2;3;2;1;6], [::9]);
      ([::4;0;2;3;6], [::5;0;2;3]);
      ([::5;0;1;2;0;1;3;2;1;5], [::9]);
      ([::5;0;1;2;0;1;3;2;0;1;6], [::9]);
      ([::5;0;1;2;0;1;3;4], [::8;3]);
      ([::5;0;1;2;0;6], [::7;2;0]);
      ([::5;0;1;2;1;4], [::7;2;1]);
      ([::8;3;2;0;6], [::8;3;2;0]);
      ([::7;2;0;1;2;3;2;0;5], [::9]);
      ([::7;2;0;1;2;3;2;7], [::9]);
      ([::7;2;0;1;2;3;8], [::9]);
      ([::5;0;1;2;3;2], [::3;5;0;1;2;3]);
      ([::6;1;2;0;3;2;0], [::3;6;1;2;0;3;2]);
      ([::7;2;0;1;3;2;0;1;5], [::9]);
      ([::5;0;1;2;0;1;3;2;0;1;5], [::9]);
      ([::7;2;0;1;2;3;2;0;1;4], [::9]);
      ([::8;3;2;0;1;2;3;6], [::9]);
      ([::5;1;2;0;3;2;0], [::3;5;1;2;0;3;2]);
      ([::3;2;0;1;2;3;2], [::2;3;2;0;1;2;3]);
      ([::7;2;0;1;2;3;2;0;1;6], [::9]);
      ([::7;2;0;1;2;3;2;1;5], [::9]);
      ([::5;0;2;1;3;2;1], [::3;5;0;2;1;3;2]);
      ([::4;0;2;1;3;2;1], [::3;4;0;2;1;3;2]);
      ([::1;3;2;0;1;2;7], [::3;2;0;1;2;7]);
      ([::7;2;1;3;2;0;1], [::3;7;2;1;3;2;0]);
      ([::7;2;0;1;3;2;0;1;2], [::3;7;2;0;1;3;2;0;1]);
      ([::0;3;2;0;1;2;7], [::3;2;0;1;2;7]);
      ([::1;3;2;0;1;2;3;8], [::3;2;0;1;2;3;8]);
      ([::1;3;2;0;1;2;3;7], [::3;2;0;1;2;3;7]);
      ([::0;3;2;0;1;2;3;8], [::3;2;0;1;2;3;8]);
      ([::0;3;2;0;1;2;3;7], [::3;2;0;1;2;3;7]);
      ([::7;2;0;3;2;5], [::8;3;2]);
      ([::7;2;0;3;2;6], [::7;2;0;3;2]);
      ([::7;2;1;3;4], [::7;2;1;3]);
      ([::7;2;0;1;2;3;5], [::8;3]);
      ([::7;2;0;1;2;3;7], [::8;3]);
      ([::7;2;0;1;2;3;2;6], [::8;3;2]);
      ([::7;2;0;1;2;3;2;0;1;5], [::9]);
      ([::7;2;0;3;6], [::7;2;0;3]);
      ([::7;2;0;1;2;3;4], [::8;3]);
      ([::7;2;0;3;2;1;4], [::8;3;2;1]);
      ([::4;0;2;1;3;4], [::7;2;1;3]);
      ([::5;0;1;2;3;4], [::7;2;3]);
      ([::7;2;1;3;2;5], [::8;3;2]);
      ([::7;2;1;3;2;4], [::7;2;1;3;2]);
      ([::7;2;0;1;3;2;4], [::8;3;2]);
      ([::7;2;1;3;2;0;6], [::8;3;2;0]);
      ([::6;1;2;0;3;6], [::7;2;0;3]);
      ([::5;0;1;2;3;6], [::7;2;3]);
      ([::7;2;0;1;2;3;2;0;1;2;6], [::9]);
      ([::7;2;0;1;2;3;2;4], [::8;3;2]);
      ([::8;3;2;0;1;2;3;4], [::9]);
      ([::8;3;2;0;1;2;3;5], [::9]);
      ([::8;3;2;0;1;2;3;7], [::9]);
      ([::8;3;2;0;1;2;3;8], [::9]);
      ([::6;1;2;0;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;3;2;4], [::8;3;2]);
      ([::5;0;1;2;0;1;3;2;4], [::8;3;2]);
      ([::5;0;1;2;3;5], [::7;2;3]);
      ([::7;2;0;1;3;2;5], [::8;3;2]);
      ([::5;1;2;3;5], [::7;2;3]);
      ([::5;0;2;1;3;2;5], [::8;3;2]);
      ([::5;0;2;1;3;2;0;6], [::8;3;2;0]);
      ([::5;0;1;2;0;1;3;2;5], [::8;3;2]);
      ([::7;2;0;1;2;3;2;5], [::8;3;2]);
      ([::5;0;2;3;6], [::5;0;2;3]);
      ([::5;0;1;2;1;3;2;5], [::8;3;2]);
      ([::5;0;2;3;5], [::7;2;3]);
      ([::5;1;2;0;3;6], [::7;2;0;3]);
      ([::5;1;2;0;3;2;5], [::8;3;2]);
      ([::5;1;2;0;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;3;2;5], [::8;3;2]);
      ([::5;0;1;2;1;3;2;0;6], [::8;3;2;0]);
      ([::7;2;0;1;3;2;0;6], [::8;3;2;0]);
      ([::5;0;2;1;3;4], [::7;2;1;3]);
      ([::5;0;1;2;0;1;3;2;0;6], [::8;3;2;0]);
      ([::7;2;0;1;2;3;2;0;6], [::8;3;2;0]);
      ([::7;2;0;1;2;3;2;0;1;2;4], [::9]);
      ([::5;1;2;0;3;2;6], [::7;2;0;3;2]);
      ([::7;2;0;1;2;3;2;0;1;2;7], [::9]);
      ([::7;2;0;1;2;3;2;0;1;2;5], [::9]);
      ([::5;0;1;2;1;3;4], [::7;2;1;3]);
      ([::5;0;1;2;0;3;6], [::7;2;0;3]);
      ([::5;0;2;1;3;2;4], [::7;2;1;3;2]);
      ([::5;0;2;1;3;2;0;1], [::3;5;0;2;1;3;2;0]);
      ([::5;0;1;2;0;3;2;6], [::7;2;0;3;2]);
      ([::5;0;1;2;1;3;2;4], [::7;2;1;3;2]);
      ([::7;2;0;1;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;3;2;0], [::3;5;0;1;2;0;3;2]);
      ([::5;0;1;2;1;3;2;1], [::3;5;0;1;2;1;3;2]);
      ([::2;3;2;0;1;2;3;8], [::3;2;0;1;2;3;8]);
      ([::4;0;2;1;3;2;0;1], [::3;4;0;2;1;3;2;0]);
      ([::0;2;0;1;2;3;2;0;1;2;7], [::2;0;1;2;3;2;0;1;2;7]);
      ([::7;2;0;1;2;3;2;0;1;2;3], [::3;7;2;0;1;2;3;2;0;1;2]);
      ([::1;2;0;1;2;3;2;0;1;2;7], [::2;0;1;2;3;2;0;1;2;7]);
      ([::0;2;0;1;2;3;2;0;1;2;3;7], [::2;0;1;2;3;2;0;1;2;3;7]);
      ([::1;2;0;1;2;3;2;0;1;2;3;7], [::2;0;1;2;3;2;0;1;2;3;7]);
      ([::7;2;0;1;2;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;3;2;1;4], [::8;3;2;1]);
      ([::4;0;2;1;3;2;4], [::7;2;1;3;2]);
      ([::6;1;2;0;3;2;6], [::7;2;0;3;2]);
      ([::5;0;1;2;0;1;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;1;3;2;0;1], [::3;5;0;1;2;1;3;2;0]);
      ([::5;0;1;2;0;1;3;2;0;1;2], [::3;5;0;1;2;0;1;3;2;0;1])].


Definition RennerD41_Gay_cert : pres_cert :=
  [:: add_rel [::9;6] [::9]
     [:: RTriple 91 0 false;
         RTriple 92 0 true];
     add_rel [::8;6] [::8]
     [:: RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::7;6] [::7]
     [:: RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::9;3] [::9]
     [:: RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::9;2] [::9]
     [:: RTriple 33 0 false;
         RTriple 34 0 true];
     add_rel [::8;2] [::8]
     [:: RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::9;0] [::9]
     [:: RTriple 29 0 false;
         RTriple 30 0 true];
     add_rel [::9;1] [::9]
     [:: RTriple 27 0 false;
         RTriple 28 0 true];
     add_rel [::8;0] [::8]
     [:: RTriple 25 0 false;
         RTriple 26 0 true];
     add_rel [::8;1] [::8]
     [:: RTriple 23 0 false;
         RTriple 24 0 true];
     add_rel [::7;0] [::7]
     [:: RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::7;1] [::7]
     [:: RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::4;1] [::1;4]
     [:: RTriple 18 0 false];
     add_rel [::6;0] [::0;6]
     [:: RTriple 17 0 false];
     add_rel [::6;3] [::3;6]
     [:: RTriple 16 0 false];
     add_rel [::7;3] [::3;7]
     [:: RTriple 15 0 false];
     add_rel [::5;3] [::3;5]
     [:: RTriple 14 0 false];
     add_rel [::4;3] [::3;4]
     [:: RTriple 13 0 false];
     add_rel [::6;2] [::2;6]
     [:: RTriple 12 0 false];
     add_rel [::5;2] [::2;5]
     [:: RTriple 11 0 false];
     add_rel [::4;2] [::2;4]
     [:: RTriple 10 0 false];
     add_rel [::2;0;2] [::0;2;0]
     [:: RTriple 9 0 false];
     add_rel [::3;2;3] [::2;3;2]
     [:: RTriple 8 0 false];
     add_rel [::2;1;2] [::1;2;1]
     [:: RTriple 7 0 false];
     add_rel [::1;0] [::0;1]
     [:: RTriple 6 0 false];
     add_rel [::3;0] [::0;3]
     [:: RTriple 5 0 false];
     add_rel [::6;1;2;0;3;2;1;6] [::9]
     [:: RTriple 5 3 true;
         RTriple 102 0 true];
     add_rel [::3;1] [::1;3]
     [:: RTriple 4 0 false];
     add_rel [::4;0;2;1;3;2;0;4] [::9]
     [:: RTriple 4 3 true;
         RTriple 38 7 false;
         RTriple 103 0 true;
         RTriple 81 0 true;
         RTriple 46 0 true];
     add_rel [::5;6] [::5]
     [:: RTriple 48 0 false;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::6;5] [::5]
     [:: RTriple 94 1 false;
         RTriple 93 0 true;
         RTriple 94 0 true];
     add_rel [::4;0;2;1;5] [::8]
     [:: RTriple 94 4 false;
         RTriple 101 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::5;0;2;1;6] [::8]
     [:: RTriple 94 0 false;
         RTriple 101 1 true;
         RTriple 80 0 true];
     add_rel [::6;1;5] [::7]
     [:: RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;0;4] [::7]
     [:: RTriple 94 0 false;
         RTriple 98 1 true;
         RTriple 68 0 true];
     add_rel [::6;1;2;0;5] [::8]
     [:: RTriple 40 4 false;
         RTriple 100 0 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;0;4] [::8]
     [:: RTriple 95 0 false;
         RTriple 100 1 true;
         RTriple 44 0 true];
     add_rel [::5;1;6] [::7]
     [:: RTriple 95 0 false;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::4;0;5] [::7]
     [:: RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;1;6] [::8]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 101 1 true;
         RTriple 64 0 true];
     add_rel [::6;1;2;7] [::8]
     [:: RTriple 22 3 false;
         RTriple 98 4 false;
         RTriple 100 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::4;0;2;7] [::8]
     [:: RTriple 20 3 false;
         RTriple 99 4 false;
         RTriple 101 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::7;2;0;4] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::0;3;7] [::3;7]
     [:: RTriple 5 0 true;
         RTriple 22 1 true];
     add_rel [::1;3;7] [::3;7]
     [:: RTriple 15 1 true;
         RTriple 20 0 true;
         RTriple 119 0 true];
     add_rel [::4;0;2;1;3;6] [::8;3]
     [:: RTriple 16 4 true;
         RTriple 101 0 true];
     add_rel [::8;3;6] [::8;3]
     [:: RTriple 16 1 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::4;0;6] [::5;0]
     [:: RTriple 17 1 true;
         RTriple 95 0 true];
     add_rel [::6;1;4] [::5;1]
     [:: RTriple 18 1 true;
         RTriple 94 0 true];
     add_rel [::5;1;4] [::5;1]
     [:: RTriple 18 1 true;
         RTriple 48 0 true];
     add_rel [::5;0;2;1;3;2;0;4] [::9]
     [:: RTriple 48 0 false;
         RTriple 4 4 true;
         RTriple 103 1 true;
         RTriple 56 0 true];
     add_rel [::8;3;2;0;4] [::9]
     [:: RTriple 32 0 false;
         RTriple 24 1 false;
         RTriple 23 1 true;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 4 4 true;
         RTriple 103 1 true;
         RTriple 78 0 true];
     add_rel [::7;2;1;3;2;0;4] [::9]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 4 4 true;
         RTriple 103 1 true;
         RTriple 66 0 true];
     add_rel [::4;0;2;1;3;2;7] [::9]
     [:: RTriple 4 3 true;
         RTriple 22 6 false;
         RTriple 98 7 false;
         RTriple 103 0 true;
         RTriple 29 0 false;
         RTriple 30 0 true;
         RTriple 81 0 true;
         RTriple 46 0 true];
     add_rel [::4;0;2;1;3;2;0;5] [::9]
     [:: RTriple 4 3 true;
         RTriple 95 7 false;
         RTriple 103 0 true;
         RTriple 91 0 false;
         RTriple 92 0 true];
     add_rel [::1;3;8] [::3;8]
     [:: RTriple 4 0 true;
         RTriple 24 1 true];
     add_rel [::4;0;2;3;8] [::9]
     [:: RTriple 24 4 false;
         RTriple 32 5 false;
         RTriple 26 6 false;
         RTriple 101 7 false;
         RTriple 103 0 true;
         RTriple 29 0 false;
         RTriple 30 0 true;
         RTriple 33 0 false;
         RTriple 27 1 false;
         RTriple 28 1 true;
         RTriple 34 0 true;
         RTriple 91 0 false;
         RTriple 92 0 true];
     add_rel [::6;1;3] [::3;6;1]
     [:: RTriple 4 1 true;
         RTriple 118 0 true];
     add_rel [::5;1;3] [::3;5;1]
     [:: RTriple 4 1 true;
         RTriple 120 0 true];
     add_rel [::3;2;1;3] [::2;3;2;1]
     [:: RTriple 4 2 true;
         RTriple 126 0 true];
     add_rel [::8;3;2;1;6] [::9]
     [:: RTriple 32 0 false;
         RTriple 26 1 false;
         RTriple 80 2 false;
         RTriple 17 1 true;
         RTriple 12 0 true;
         RTriple 25 2 true;
         RTriple 31 1 true;
         RTriple 24 1 false;
         RTriple 23 1 true;
         RTriple 79 0 true;
         RTriple 5 4 true;
         RTriple 102 1 true;
         RTriple 78 0 true];
     add_rel [::7;2;0;3;2;1;6] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 5 5 true;
         RTriple 102 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true];
     add_rel [::6;1;2;0;3;2;7] [::9]
     [:: RTriple 5 3 true;
         RTriple 20 6 false;
         RTriple 99 7 false;
         RTriple 102 0 true;
         RTriple 27 0 false;
         RTriple 28 0 true;
         RTriple 91 0 false;
         RTriple 92 0 true];
     add_rel [::5;1;2;0;3;2;1;6] [::9]
     [:: RTriple 95 0 false;
         RTriple 5 4 true;
         RTriple 102 1 true;
         RTriple 46 0 true];
     add_rel [::6;1;2;0;3;2;1;5] [::9]
     [:: RTriple 5 3 true;
         RTriple 94 7 false;
         RTriple 102 0 true;
         RTriple 81 0 true;
         RTriple 46 0 true];
     add_rel [::0;3;8] [::3;8]
     [:: RTriple 5 0 true;
         RTriple 26 1 true];
     add_rel [::6;1;2;3;8] [::9]
     [:: RTriple 0 3 false;
         RTriple 5 4 true;
         RTriple 5 3 true;
         RTriple 25 5 true;
         RTriple 32 5 false;
         RTriple 24 6 false;
         RTriple 100 7 false;
         RTriple 102 0 true;
         RTriple 27 0 false;
         RTriple 28 0 true;
         RTriple 33 0 false;
         RTriple 29 1 false;
         RTriple 30 1 true;
         RTriple 34 0 true;
         RTriple 81 0 true;
         RTriple 46 0 true;
         RTriple 29 0 false;
         RTriple 30 0 true];
     add_rel [::5;0;3] [::3;5;0]
     [:: RTriple 5 1 true;
         RTriple 120 0 true];
     add_rel [::4;0;3] [::3;4;0]
     [:: RTriple 5 1 true;
         RTriple 121 0 true];
     add_rel [::3;2;0;3] [::2;3;2;0]
     [:: RTriple 5 2 true;
         RTriple 126 0 true];
     add_rel [::4;0;1] [::1;4;0]
     [:: RTriple 6 1 true;
         RTriple 116 0 true];
     add_rel [::6;1;2;1] [::2;6;1;2]
     [:: RTriple 7 1 true;
         RTriple 122 0 true];
     add_rel [::5;1;2;1] [::2;5;1;2]
     [:: RTriple 7 1 true;
         RTriple 123 0 true];
     add_rel [::2;0;1;2;1] [::0;2;0;1;2]
     [:: RTriple 7 2 true;
         RTriple 125 0 true];
     add_rel [::2;0;1;2;0] [::1;2;0;1;2]
     [:: RTriple 6 1 true;
         RTriple 9 2 true;
         RTriple 127 0 true;
         RTriple 128 2 true];
     add_rel [::7;2;3;2] [::3;7;2;3]
     [:: RTriple 8 1 true;
         RTriple 119 0 true];
     add_rel [::5;0;2;0] [::2;5;0;2]
     [:: RTriple 9 1 true;
         RTriple 123 0 true];
     add_rel [::4;0;2;0] [::2;4;0;2]
     [:: RTriple 9 1 true;
         RTriple 124 0 true];
     add_rel [::4;0;2;4] [::7;2]
     [:: RTriple 10 2 true;
         RTriple 98 0 true];
     add_rel [::7;2;4] [::7;2]
     [:: RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::7;2;5] [::7;2]
     [:: RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::6;1;2;6] [::7;2]
     [:: RTriple 12 2 true;
         RTriple 99 0 true];
     add_rel [::7;2;6] [::7;2]
     [:: RTriple 12 1 true;
         RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::6;1;2;0;3;4] [::8;3]
     [:: RTriple 13 4 true;
         RTriple 100 0 true];
     add_rel [::8;3;4] [::8;3]
     [:: RTriple 13 1 true;
         RTriple 70 0 true];
     add_rel [::8;3;5] [::8;3]
     [:: RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::7;2;3;7] [::8;3]
     [:: RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::8;3;7] [::8;3]
     [:: RTriple 15 1 true;
         RTriple 74 0 true];
     add_rel [::7;2;1;5] [::8]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 94 5 false;
         RTriple 101 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 64 0 true];
     add_rel [::5;1;5] [::7]
     [:: RTriple 95 0 false;
         RTriple 94 3 false;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::6;1;2;5] [::7;2]
     [:: RTriple 94 3 false;
         RTriple 12 2 true;
         RTriple 99 0 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;0;2;7] [::8]
     [:: RTriple 94 0 false;
         RTriple 20 4 false;
         RTriple 68 5 false;
         RTriple 101 1 true;
         RTriple 80 0 true;
         RTriple 73 0 true;
         RTriple 64 0 true];
     add_rel [::5;0;2;1;5] [::8]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 94 5 false;
         RTriple 101 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;2;1;3;6] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 16 5 true;
         RTriple 101 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;1;6] [::8]
     [:: RTriple 94 0 false;
         RTriple 7 3 true;
         RTriple 12 5 true;
         RTriple 101 1 true;
         RTriple 80 0 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::4;0;2;1;3;5] [::8;3]
     [:: RTriple 14 4 true;
         RTriple 94 4 false;
         RTriple 101 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::5;0;6] [::5;0]
     [:: RTriple 48 0 false;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::7;2;0;1;6] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 101 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;1;3;6] [::8;3]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 16 5 true;
         RTriple 101 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;5] [::7]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 40 3 false;
         RTriple 98 1 true;
         RTriple 59 1 true;
         RTriple 52 1 true;
         RTriple 52 0 true];
     add_rel [::4;0;2;5] [::7;2]
     [:: RTriple 11 2 true;
         RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::5;1;2;7] [::8]
     [:: RTriple 95 0 false;
         RTriple 22 4 false;
         RTriple 42 5 false;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 73 0 true;
         RTriple 64 0 true];
     add_rel [::5;0;1;6] [::7]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 99 2 true;
         RTriple 22 1 true;
         RTriple 42 0 true];
     add_rel [::5;1;2;6] [::7;2]
     [:: RTriple 95 0 false;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::7;2;0;5] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 40 6 false;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;0;5] [::8]
     [:: RTriple 95 0 false;
         RTriple 40 5 false;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;0;3;4] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 13 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;4] [::8]
     [:: RTriple 95 0 false;
         RTriple 6 2 true;
         RTriple 9 3 true;
         RTriple 10 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::6;1;2;0;3;5] [::8;3]
     [:: RTriple 14 4 true;
         RTriple 40 4 false;
         RTriple 100 0 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;4] [::7]
     [:: RTriple 94 0 false;
         RTriple 18 3 true;
         RTriple 98 1 true;
         RTriple 68 0 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::5;0;2;4] [::7;2]
     [:: RTriple 94 0 false;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 68 0 true];
     add_rel [::4;0;2;3;7] [::8;3]
     [:: RTriple 15 3 true;
         RTriple 20 3 false;
         RTriple 99 4 false;
         RTriple 101 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::4;0;2;1;3;2;6] [::8;3;2]
     [:: RTriple 12 5 true;
         RTriple 16 4 true;
         RTriple 101 0 true];
     add_rel [::8;3;2;0;1;6] [::9]
     [:: RTriple 32 0 false;
         RTriple 26 1 false;
         RTriple 25 1 true;
         RTriple 31 0 true;
         RTriple 96 0 false;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 8 3 true;
         RTriple 119 2 true;
         RTriple 20 3 false;
         RTriple 19 3 true;
         RTriple 99 3 false;
         RTriple 102 5 true;
         RTriple 28 4 true;
         RTriple 92 3 true;
         RTriple 36 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::8;3;2;0;5] [::9]
     [:: RTriple 32 0 false;
         RTriple 24 1 false;
         RTriple 23 1 true;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 4 4 true;
         RTriple 40 8 false;
         RTriple 103 1 true;
         RTriple 78 0 true;
         RTriple 83 0 true;
         RTriple 56 0 true];
     add_rel [::8;3;2;7] [::9]
     [:: RTriple 32 0 false;
         RTriple 24 1 false;
         RTriple 23 1 true;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 4 4 true;
         RTriple 22 7 false;
         RTriple 42 8 false;
         RTriple 103 1 true;
         RTriple 78 0 true;
         RTriple 85 0 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;4] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 18 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true];
     add_rel [::7;2;0;3;4] [::8;3]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::6;1;2;3;7] [::8;3]
     [:: RTriple 15 3 true;
         RTriple 22 3 false;
         RTriple 98 4 false;
         RTriple 100 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::5;1;2;4] [::5;1;2]
     [:: RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 48 0 true];
     add_rel [::5;0;1;2;1;3;2;0;4] [::9]
     [:: RTriple 48 0 false;
         RTriple 7 3 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 129 7 true;
         RTriple 13 8 true;
         RTriple 103 1 true;
         RTriple 56 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;1;5] [::8]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 94 6 false;
         RTriple 101 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;5] [::7]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 40 4 false;
         RTriple 98 2 true;
         RTriple 59 2 true;
         RTriple 52 2 true;
         RTriple 20 1 true;
         RTriple 52 0 true];
     add_rel [::5;0;1;2;7] [::8]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 22 5 false;
         RTriple 98 6 false;
         RTriple 100 2 true;
         RTriple 25 2 false;
         RTriple 26 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;1;3;6] [::8;3]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 16 6 true;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::6;1;2;4] [::5;1;2]
     [:: RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 94 0 true];
     add_rel [::8;3;2;0;1;4] [::9]
     [:: RTriple 32 0 false;
         RTriple 24 1 false;
         RTriple 23 1 true;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 4 4 true;
         RTriple 18 8 true;
         RTriple 103 1 true;
         RTriple 78 0 true;
         RTriple 27 0 false;
         RTriple 28 0 true];
     add_rel [::5;0;1;2;0;1;4] [::8]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 18 6 true;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::4;0;2;6] [::5;0;2]
     [:: RTriple 12 2 true;
         RTriple 17 1 true;
         RTriple 95 0 true];
     add_rel [::5;0;1;2;0;3;2;1;6] [::9]
     [:: RTriple 95 0 false;
         RTriple 6 2 true;
         RTriple 9 3 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 131 7 true;
         RTriple 16 8 true;
         RTriple 102 1 true;
         RTriple 46 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;0;5] [::8]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 40 6 false;
         RTriple 100 2 true;
         RTriple 71 2 true;
         RTriple 54 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::8;3;2;6] [::8;3;2]
     [:: RTriple 12 2 true;
         RTriple 16 1 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;1;3;2;0;5] [::9]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 4 5 true;
         RTriple 95 9 false;
         RTriple 103 2 true;
         RTriple 91 2 false;
         RTriple 92 2 true;
         RTriple 28 1 true;
         RTriple 56 0 true];
     add_rel [::7;2;1;3;2;7] [::9]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 4 4 true;
         RTriple 22 7 false;
         RTriple 42 8 false;
         RTriple 103 1 true;
         RTriple 66 0 true;
         RTriple 85 0 true;
         RTriple 66 0 true];
     add_rel [::5;0;2;1;3;2;7] [::9]
     [:: RTriple 48 0 false;
         RTriple 4 4 true;
         RTriple 22 7 false;
         RTriple 42 8 false;
         RTriple 103 1 true;
         RTriple 56 0 true;
         RTriple 85 0 true;
         RTriple 66 0 true];
     add_rel [::5;0;1;2;1;3;2;7] [::9]
     [:: RTriple 48 0 false;
         RTriple 7 3 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 22 8 false;
         RTriple 129 7 true;
         RTriple 15 8 true;
         RTriple 98 8 false;
         RTriple 103 1 true;
         RTriple 56 0 true;
         RTriple 29 0 false;
         RTriple 30 0 true;
         RTriple 121 1 true;
         RTriple 35 0 false;
         RTriple 36 0 true;
         RTriple 81 0 true;
         RTriple 46 0 true];
     add_rel [::7;2;3;8] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 26 6 false;
         RTriple 32 7 false;
         RTriple 24 8 false;
         RTriple 80 9 false;
         RTriple 102 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true;
         RTriple 87 0 true;
         RTriple 78 0 true];
     add_rel [::7;2;1;3;2;0;5] [::9]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 4 4 true;
         RTriple 40 8 false;
         RTriple 103 1 true;
         RTriple 66 0 true;
         RTriple 83 0 true;
         RTriple 56 0 true];
     add_rel [::7;2;0;1;3;2;0;4] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 9 2 true;
         RTriple 123 1 true;
         RTriple 48 2 false;
         RTriple 4 6 true;
         RTriple 103 3 true;
         RTriple 56 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;0;2;3;8] [::9]
     [:: RTriple 48 0 false;
         RTriple 24 5 false;
         RTriple 32 6 false;
         RTriple 26 7 false;
         RTriple 44 8 false;
         RTriple 103 1 true;
         RTriple 56 0 true;
         RTriple 87 0 true;
         RTriple 78 0 true];
     add_rel [::5;0;2;1;3;2;0;5] [::9]
     [:: RTriple 48 0 false;
         RTriple 4 4 true;
         RTriple 40 8 false;
         RTriple 103 1 true;
         RTriple 56 0 true;
         RTriple 83 0 true;
         RTriple 56 0 true];
     add_rel [::6;1;2;3;2] [::3;6;1;2;3]
     [:: RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 118 0 true];
     add_rel [::5;0;1;3] [::3;5;0;1]
     [:: RTriple 4 2 true;
         RTriple 5 1 true;
         RTriple 120 0 true];
     add_rel [::5;0;1;2;3;8] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 26 6 false;
         RTriple 32 7 false;
         RTriple 24 8 false;
         RTriple 100 9 false;
         RTriple 102 2 true;
         RTriple 27 2 false;
         RTriple 28 2 true;
         RTriple 33 2 false;
         RTriple 29 3 false;
         RTriple 30 3 true;
         RTriple 34 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::5;1;2;0;3;2;7] [::9]
     [:: RTriple 95 0 false;
         RTriple 5 4 true;
         RTriple 20 7 false;
         RTriple 99 8 false;
         RTriple 102 1 true;
         RTriple 27 1 false;
         RTriple 28 1 true;
         RTriple 91 1 false;
         RTriple 92 1 true;
         RTriple 46 0 true];
     add_rel [::7;2;0;3;2;7] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 5 5 true;
         RTriple 20 8 false;
         RTriple 68 9 false;
         RTriple 102 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true;
         RTriple 85 0 true;
         RTriple 66 0 true];
     add_rel [::5;0;1;2;0;3;2;7] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 5 5 true;
         RTriple 20 8 false;
         RTriple 99 9 false;
         RTriple 102 2 true;
         RTriple 27 2 false;
         RTriple 28 2 true;
         RTriple 91 2 false;
         RTriple 92 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::7;2;0;3;2;1;5] [::9]
     [:: RTriple 68 0 false;
         RTriple 20 1 false;
         RTriple 19 1 true;
         RTriple 67 0 true;
         RTriple 5 4 true;
         RTriple 94 8 false;
         RTriple 102 1 true;
         RTriple 81 1 true;
         RTriple 46 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;3;2;1;6] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 4 6 true;
         RTriple 5 5 true;
         RTriple 7 7 true;
         RTriple 12 9 true;
         RTriple 102 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true;
         RTriple 33 0 false;
         RTriple 34 0 true];
     add_rel [::8;3;2;1;5] [::9]
     [:: RTriple 32 0 false;
         RTriple 26 1 false;
         RTriple 80 2 false;
         RTriple 17 1 true;
         RTriple 12 0 true;
         RTriple 25 2 true;
         RTriple 31 1 true;
         RTriple 24 1 false;
         RTriple 23 1 true;
         RTriple 79 0 true;
         RTriple 5 4 true;
         RTriple 94 8 false;
         RTriple 102 1 true;
         RTriple 81 1 true;
         RTriple 46 1 true;
         RTriple 78 0 true];
     add_rel [::3;2;0;1;3] [::2;3;2;0;1]
     [:: RTriple 4 3 true;
         RTriple 5 2 true;
         RTriple 126 0 true];
     add_rel [::5;1;2;3;2] [::3;5;1;2;3]
     [:: RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 120 0 true];
     add_rel [::8;3;2;0;1;2;6] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 80 0 false;
         RTriple 79 0 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 8 3 true;
         RTriple 4 2 true;
         RTriple 118 1 true;
         RTriple 12 9 true;
         RTriple 102 2 true;
         RTriple 33 2 false;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::5;0;1;2;0;1;3;2;1;6] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 4 6 true;
         RTriple 5 5 true;
         RTriple 7 7 true;
         RTriple 12 9 true;
         RTriple 102 2 true;
         RTriple 33 2 false;
         RTriple 34 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::5;1;2;0;3;2;1;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 5 4 true;
         RTriple 94 8 false;
         RTriple 102 1 true;
         RTriple 81 1 true;
         RTriple 46 1 true;
         RTriple 46 0 true];
     add_rel [::8;3;2;0;1;5] [::9]
     [:: RTriple 32 0 false;
         RTriple 26 1 false;
         RTriple 25 1 true;
         RTriple 31 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 80 0 false;
         RTriple 79 0 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 8 3 true;
         RTriple 4 2 true;
         RTriple 118 1 true;
         RTriple 94 9 false;
         RTriple 102 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::5;0;1;2;0;3;2;1;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 5 5 true;
         RTriple 94 9 false;
         RTriple 102 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::5;1;2;3;8] [::9]
     [:: RTriple 95 0 false;
         RTriple 26 5 false;
         RTriple 32 6 false;
         RTriple 24 7 false;
         RTriple 100 8 false;
         RTriple 102 1 true;
         RTriple 27 1 false;
         RTriple 28 1 true;
         RTriple 33 1 false;
         RTriple 29 2 false;
         RTriple 30 2 true;
         RTriple 34 1 true;
         RTriple 81 1 true;
         RTriple 46 1 true;
         RTriple 46 0 true];
     add_rel [::4;0;2;3;2] [::3;4;0;2;3]
     [:: RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true];
     add_rel [::5;0;2;3;2] [::3;5;0;2;3]
     [:: RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 120 0 true];
     add_rel [::7;2;1;3;2;1] [::3;7;2;1;3;2]
     [:: RTriple 4 2 true;
         RTriple 7 3 true;
         RTriple 8 1 true;
         RTriple 119 0 true;
         RTriple 131 3 true];
     add_rel [::1;2;0;1;2;7] [::2;0;1;2;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 125 2 true;
         RTriple 128 1 true;
         RTriple 22 4 true];
     add_rel [::1;2;0;1;2;3;7] [::2;0;1;2;3;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 125 2 true;
         RTriple 128 1 true;
         RTriple 5 4 true;
         RTriple 22 5 true];
     add_rel [::1;2;0;1;2;3;8] [::2;0;1;2;3;8]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 125 2 true;
         RTriple 128 1 true;
         RTriple 5 4 true;
         RTriple 26 5 true];
     add_rel [::0;2;0;1;2;7] [::2;0;1;2;7]
     [:: RTriple 9 0 true;
         RTriple 127 2 true;
         RTriple 20 4 true];
     add_rel [::0;2;0;1;2;3;7] [::2;0;1;2;3;7]
     [:: RTriple 9 0 true;
         RTriple 127 2 true;
         RTriple 15 5 true;
         RTriple 20 4 true;
         RTriple 119 4 true];
     add_rel [::0;2;0;1;2;3;8] [::2;0;1;2;3;8]
     [:: RTriple 9 0 true;
         RTriple 127 2 true;
         RTriple 4 4 true;
         RTriple 24 5 true];
     add_rel [::5;1;2;0;1] [::2;5;1;2;0]
     [:: RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 123 0 true];
     add_rel [::6;1;2;0;1] [::2;6;1;2;0]
     [:: RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 122 0 true];
     add_rel [::7;2;1;4] [::7;2;1]
     [:: RTriple 18 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::7;2;3;4] [::7;2;3]
     [:: RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::7;2;0;1;5] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 94 6 false;
         RTriple 101 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;3;6] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 16 6 true;
         RTriple 101 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;6] [::7;2;0]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 17 3 true;
         RTriple 95 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;0;1;3;2;7] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 4 5 true;
         RTriple 22 8 false;
         RTriple 98 9 false;
         RTriple 103 2 true;
         RTriple 29 2 false;
         RTriple 30 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;3;2;0;5] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 4 5 true;
         RTriple 95 9 false;
         RTriple 103 2 true;
         RTriple 91 2 false;
         RTriple 92 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;3;2;0;1;4] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 4 5 true;
         RTriple 18 9 true;
         RTriple 103 2 true;
         RTriple 27 2 false;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::4;0;2;1;4] [::7;2;1]
     [:: RTriple 18 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true];
     add_rel [::4;0;2;3;4] [::7;2;3]
     [:: RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true];
     add_rel [::5;0;1;2;4] [::7;2]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 10 4 true;
         RTriple 98 2 true;
         RTriple 20 1 true;
         RTriple 52 0 true];
     add_rel [::5;0;1;2;0;1;2] [::2;5;0;1;2;0;1]
     [:: RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 9 1 true;
         RTriple 123 0 true;
         RTriple 127 3 true;
         RTriple 128 5 true];
     add_rel [::7;2;0;3;2;0] [::3;7;2;0;3;2]
     [:: RTriple 5 2 true;
         RTriple 9 3 true;
         RTriple 8 1 true;
         RTriple 119 0 true;
         RTriple 129 3 true];
     add_rel [::8;3;2;4] [::8;3;2]
     [:: RTriple 96 0 false;
         RTriple 119 2 true;
         RTriple 10 4 true;
         RTriple 57 3 true;
         RTriple 42 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;0;1;3;4] [::8;3]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 122 1 true;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;3;6] [::7;2;3]
     [:: RTriple 16 2 true;
         RTriple 12 1 true;
         RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::7;2;0;1;3;2;1;5] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 122 1 true;
         RTriple 5 5 true;
         RTriple 94 9 false;
         RTriple 102 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;3;2;0;1;6] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 122 1 true;
         RTriple 5 5 true;
         RTriple 6 8 true;
         RTriple 17 9 true;
         RTriple 102 2 true;
         RTriple 29 2 false;
         RTriple 30 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::6;1;2;0;6] [::7;2;0]
     [:: RTriple 17 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true];
     add_rel [::6;1;2;3;6] [::7;2;3]
     [:: RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true];
     add_rel [::5;0;1;2;6] [::7;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 12 4 true;
         RTriple 99 2 true;
         RTriple 22 1 true;
         RTriple 42 0 true];
     add_rel [::7;2;3;5] [::7;2;3]
     [:: RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::8;3;2;5] [::8;3;2]
     [:: RTriple 96 0 false;
         RTriple 119 2 true;
         RTriple 11 4 true;
         RTriple 59 3 true;
         RTriple 52 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::6;1;2;0;3;2;4] [::8;3;2]
     [:: RTriple 10 5 true;
         RTriple 13 4 true;
         RTriple 100 0 true];
     add_rel [::5;0;1;2;0;3;4] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;5] [::7;2]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 11 4 true;
         RTriple 40 4 false;
         RTriple 98 2 true;
         RTriple 59 2 true;
         RTriple 52 2 true;
         RTriple 20 1 true;
         RTriple 52 0 true];
     add_rel [::5;1;2;5] [::7;2]
     [:: RTriple 95 0 false;
         RTriple 94 4 false;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::7;2;1;3;5] [::8;3]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 14 5 true;
         RTriple 94 5 false;
         RTriple 101 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;2;3;7] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 15 4 true;
         RTriple 98 4 false;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 68 0 true;
         RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;1;3;2;6] [::8;3;2]
     [:: RTriple 94 0 false;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 101 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;1;3;5] [::8;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 14 5 true;
         RTriple 94 5 false;
         RTriple 101 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 54 0 true];
     add_rel [::6;1;2;3;5] [::7;2;3]
     [:: RTriple 94 4 false;
         RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true;
         RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;0;2;6] [::5;0;2]
     [:: RTriple 48 0 false;
         RTriple 12 3 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::4;0;2;1;3;2;5] [::8;3;2]
     [:: RTriple 11 5 true;
         RTriple 14 4 true;
         RTriple 94 4 false;
         RTriple 101 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;1;3;5] [::8;3]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 14 6 true;
         RTriple 94 6 false;
         RTriple 101 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::7;2;0;1;3;5] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 14 6 true;
         RTriple 94 6 false;
         RTriple 101 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;1;2;0;1;6] [::8]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 6 5 true;
         RTriple 17 6 true;
         RTriple 101 2 true;
         RTriple 25 2 false;
         RTriple 26 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::7;2;0;1;2;6] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 101 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;2;5] [::7;2]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 11 3 true;
         RTriple 40 3 false;
         RTriple 98 1 true;
         RTriple 59 1 true;
         RTriple 52 1 true;
         RTriple 52 0 true];
     add_rel [::7;2;1;3;2;6] [::8;3;2]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 101 1 true;
         RTriple 64 0 true];
     add_rel [::5;1;2;3;7] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 22 5 false;
         RTriple 129 4 true;
         RTriple 15 5 true;
         RTriple 98 5 false;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 70 0 true];
     add_rel [::4;0;2;3;5] [::7;2;3]
     [:: RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;0;3;5] [::8;3]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 40 7 false;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;0;6] [::7;2;0]
     [:: RTriple 95 0 false;
         RTriple 17 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::5;1;2;3;6] [::7;2;3]
     [:: RTriple 95 0 false;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::7;2;0;1;2;4] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 10 7 true;
         RTriple 18 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::5;1;2;0;3;5] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 40 6 false;
         RTriple 13 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;0;3;2;4] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true];
     add_rel [::6;1;2;0;3;2;5] [::8;3;2]
     [:: RTriple 11 5 true;
         RTriple 14 4 true;
         RTriple 40 4 false;
         RTriple 100 0 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;2;0;3;5] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 14 6 true;
         RTriple 40 6 false;
         RTriple 100 2 true;
         RTriple 71 2 true;
         RTriple 54 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;1;3;2;6] [::8;3;2]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 12 7 true;
         RTriple 16 6 true;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::8;3;2;1;4] [::8;3;2;1]
     [:: RTriple 96 0 false;
         RTriple 119 2 true;
         RTriple 18 5 true;
         RTriple 10 4 true;
         RTriple 57 3 true;
         RTriple 42 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::8;3;2;0;1;2;7] [::9]
     [:: RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 96 0 false;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 119 2 true;
         RTriple 52 3 false;
         RTriple 51 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 129 5 true;
         RTriple 9 3 true;
         RTriple 123 2 true;
         RTriple 48 3 false;
         RTriple 22 10 false;
         RTriple 42 11 false;
         RTriple 103 4 true;
         RTriple 56 3 true;
         RTriple 85 3 true;
         RTriple 66 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::8;3;2;0;1;2;5] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 80 0 false;
         RTriple 79 0 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 8 3 true;
         RTriple 4 2 true;
         RTriple 118 1 true;
         RTriple 11 9 true;
         RTriple 94 9 false;
         RTriple 102 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 33 2 false;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::7;2;0;1;3;2;6] [::8;3;2]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 12 7 true;
         RTriple 16 6 true;
         RTriple 101 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;1;2;3;7] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 6 2 true;
         RTriple 22 6 false;
         RTriple 129 5 true;
         RTriple 9 3 true;
         RTriple 15 6 true;
         RTriple 98 6 false;
         RTriple 10 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 31 0 false;
         RTriple 32 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 70 0 true];
     add_rel [::5;0;2;1;4] [::7;2;1]
     [:: RTriple 94 0 false;
         RTriple 18 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 68 0 true];
     add_rel [::5;0;2;3;4] [::7;2;3]
     [:: RTriple 94 0 false;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 68 0 true];
     add_rel [::4;0;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 17 6 true;
         RTriple 12 5 true;
         RTriple 16 4 true;
         RTriple 101 0 true];
     add_rel [::7;2;0;3;2;4] [::8;3;2]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 10 7 true;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;4] [::9]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 6 5 true;
         RTriple 5 6 true;
         RTriple 4 5 true;
         RTriple 9 7 true;
         RTriple 10 9 true;
         RTriple 103 2 true;
         RTriple 33 2 false;
         RTriple 34 2 true;
         RTriple 28 1 true;
         RTriple 56 0 true];
     add_rel [::7;2;0;1;2;3;2;0;4] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 9 2 true;
         RTriple 123 1 true;
         RTriple 48 2 false;
         RTriple 8 7 true;
         RTriple 4 6 true;
         RTriple 129 9 true;
         RTriple 13 10 true;
         RTriple 103 3 true;
         RTriple 56 2 true;
         RTriple 35 2 false;
         RTriple 36 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;1;2;3;4] [::5;1;2;3]
     [:: RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 48 0 true];
     add_rel [::5;0;1;2;0;1;5] [::8]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 40 7 false;
         RTriple 100 3 true;
         RTriple 71 3 true;
         RTriple 54 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;1;3;6] [::8;3]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 16 7 true;
         RTriple 101 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;2;0;1;3;2;7] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 5 6 true;
         RTriple 20 9 false;
         RTriple 99 10 false;
         RTriple 102 3 true;
         RTriple 27 3 false;
         RTriple 28 3 true;
         RTriple 91 3 false;
         RTriple 92 3 true;
         RTriple 34 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;5] [::9]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 4 6 true;
         RTriple 95 10 false;
         RTriple 103 3 true;
         RTriple 91 3 false;
         RTriple 92 3 true;
         RTriple 34 2 true;
         RTriple 28 1 true;
         RTriple 56 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;4] [::9]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 4 6 true;
         RTriple 18 10 true;
         RTriple 103 3 true;
         RTriple 27 3 false;
         RTriple 28 3 true;
         RTriple 34 2 true;
         RTriple 28 1 true;
         RTriple 56 0 true];
     add_rel [::5;0;1;2;0;1;3;5] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 14 7 true;
         RTriple 40 7 false;
         RTriple 100 3 true;
         RTriple 71 3 true;
         RTriple 54 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;1;3;2;6] [::8;3;2]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 101 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::7;2;0;1;2;5] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 94 7 false;
         RTriple 101 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;6] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 16 7 true;
         RTriple 101 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;7] [::8]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 20 6 false;
         RTriple 99 7 false;
         RTriple 101 3 true;
         RTriple 23 3 false;
         RTriple 24 3 true;
         RTriple 79 3 false;
         RTriple 80 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::8;3;2;0;1;2;4] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 4 4 true;
         RTriple 6 7 true;
         RTriple 7 5 true;
         RTriple 8 3 true;
         RTriple 5 2 true;
         RTriple 121 1 true;
         RTriple 125 7 true;
         RTriple 128 6 true;
         RTriple 129 5 true;
         RTriple 131 6 true;
         RTriple 6 5 true;
         RTriple 5 6 true;
         RTriple 4 5 true;
         RTriple 9 7 true;
         RTriple 10 9 true;
         RTriple 103 2 true;
         RTriple 33 2 false;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::6;1;2;3;4] [::5;1;2;3]
     [:: RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 94 0 true];
     add_rel [::7;2;0;1;2;3;2;1;6] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 8 7 true;
         RTriple 4 6 true;
         RTriple 5 5 true;
         RTriple 131 9 true;
         RTriple 7 7 true;
         RTriple 16 10 true;
         RTriple 12 9 true;
         RTriple 102 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true;
         RTriple 33 0 false;
         RTriple 34 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::4;0;2;3;6] [::5;0;2;3]
     [:: RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 17 1 true;
         RTriple 95 0 true];
     add_rel [::5;0;1;2;0;1;3;2;1;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 4 6 true;
         RTriple 5 5 true;
         RTriple 7 7 true;
         RTriple 11 9 true;
         RTriple 94 9 false;
         RTriple 102 2 true;
         RTriple 81 2 true;
         RTriple 46 2 true;
         RTriple 33 2 false;
         RTriple 34 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;6] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 5 6 true;
         RTriple 6 9 true;
         RTriple 17 10 true;
         RTriple 102 3 true;
         RTriple 29 3 false;
         RTriple 30 3 true;
         RTriple 34 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::5;0;1;2;0;1;3;4] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 13 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;6] [::7;2;0]
     [:: RTriple 48 0 false;
         RTriple 95 0 false;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 9 4 true;
         RTriple 124 3 true;
         RTriple 12 6 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 94 4 false;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 125 1 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::5;0;1;2;1;4] [::7;2;1]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 94 3 true;
         RTriple 11 2 true;
         RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 127 1 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::8;3;2;0;6] [::8;3;2;0]
     [:: RTriple 96 0 false;
         RTriple 119 2 true;
         RTriple 42 3 false;
         RTriple 41 3 true;
         RTriple 124 4 true;
         RTriple 17 6 true;
         RTriple 95 5 true;
         RTriple 11 4 true;
         RTriple 59 3 true;
         RTriple 52 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;0;1;2;3;2;0;5] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 4 6 true;
         RTriple 95 10 false;
         RTriple 103 3 true;
         RTriple 91 3 false;
         RTriple 92 3 true;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;2;3;2;7] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 9 2 true;
         RTriple 123 1 true;
         RTriple 48 2 false;
         RTriple 8 7 true;
         RTriple 4 6 true;
         RTriple 22 10 false;
         RTriple 129 9 true;
         RTriple 15 10 true;
         RTriple 98 10 false;
         RTriple 103 3 true;
         RTriple 56 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true;
         RTriple 29 0 false;
         RTriple 30 0 true;
         RTriple 121 1 true;
         RTriple 35 0 false;
         RTriple 36 0 true;
         RTriple 81 0 true;
         RTriple 46 0 true];
     add_rel [::7;2;0;1;2;3;8] [::9]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 24 7 false;
         RTriple 32 8 false;
         RTriple 26 9 false;
         RTriple 101 10 false;
         RTriple 103 3 true;
         RTriple 29 3 false;
         RTriple 30 3 true;
         RTriple 33 3 false;
         RTriple 27 4 false;
         RTriple 28 4 true;
         RTriple 34 3 true;
         RTriple 91 3 false;
         RTriple 92 3 true;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;0;1;2;3;2] [::3;5;0;1;2;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 118 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true;
         RTriple 17 2 true;
         RTriple 95 1 true];
     add_rel [::6;1;2;0;3;2;0] [::3;6;1;2;0;3;2]
     [:: RTriple 5 3 true;
         RTriple 9 4 true;
         RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 118 0 true;
         RTriple 129 4 true];
     add_rel [::7;2;0;1;3;2;0;1;5] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 5 5 true;
         RTriple 9 6 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 95 3 false;
         RTriple 94 11 false;
         RTriple 102 4 true;
         RTriple 81 4 true;
         RTriple 46 4 true;
         RTriple 46 3 true;
         RTriple 36 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 5 6 true;
         RTriple 6 9 true;
         RTriple 94 11 false;
         RTriple 17 10 true;
         RTriple 102 3 true;
         RTriple 29 3 false;
         RTriple 30 3 true;
         RTriple 81 3 true;
         RTriple 46 3 true;
         RTriple 34 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;4] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 9 2 true;
         RTriple 123 1 true;
         RTriple 127 4 true;
         RTriple 4 6 true;
         RTriple 6 9 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 120 2 true;
         RTriple 48 3 false;
         RTriple 131 8 true;
         RTriple 7 6 true;
         RTriple 8 8 true;
         RTriple 4 7 true;
         RTriple 129 10 true;
         RTriple 13 11 true;
         RTriple 103 4 true;
         RTriple 56 3 true;
         RTriple 35 3 false;
         RTriple 36 3 true;
         RTriple 36 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::8;3;2;0;1;2;3;6] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 96 0 false;
         RTriple 5 5 true;
         RTriple 9 6 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 119 2 true;
         RTriple 52 3 false;
         RTriple 51 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 129 5 true;
         RTriple 127 7 true;
         RTriple 131 6 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 123 2 true;
         RTriple 95 3 false;
         RTriple 5 7 true;
         RTriple 16 11 true;
         RTriple 102 4 true;
         RTriple 46 3 true;
         RTriple 35 3 false;
         RTriple 36 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::5;1;2;0;3;2;0] [::3;5;1;2;0;3;2]
     [:: RTriple 5 3 true;
         RTriple 9 4 true;
         RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 120 0 true;
         RTriple 129 4 true];
     add_rel [::3;2;0;1;2;3;2] [::2;3;2;0;1;2;3]
     [:: RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 5 2 true;
         RTriple 126 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;6] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 5 6 true;
         RTriple 9 7 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 120 2 true;
         RTriple 95 3 false;
         RTriple 6 5 true;
         RTriple 129 8 true;
         RTriple 9 6 true;
         RTriple 8 8 true;
         RTriple 5 7 true;
         RTriple 131 10 true;
         RTriple 16 11 true;
         RTriple 102 4 true;
         RTriple 46 3 true;
         RTriple 35 3 false;
         RTriple 36 3 true;
         RTriple 36 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;2;3;2;1;5] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 95 2 false;
         RTriple 125 5 true;
         RTriple 128 4 true;
         RTriple 117 3 true;
         RTriple 5 7 true;
         RTriple 94 11 false;
         RTriple 102 4 true;
         RTriple 81 4 true;
         RTriple 46 4 true;
         RTriple 30 3 true;
         RTriple 46 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;0;2;1;3;2;1] [::3;5;0;2;1;3;2]
     [:: RTriple 4 3 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 120 0 true;
         RTriple 131 4 true];
     add_rel [::4;0;2;1;3;2;1] [::3;4;0;2;1;3;2]
     [:: RTriple 4 3 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true;
         RTriple 131 4 true];
     add_rel [::1;3;2;0;1;2;7] [::3;2;0;1;2;7]
     [:: RTriple 4 0 true;
         RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 125 3 true;
         RTriple 128 2 true;
         RTriple 22 5 true];
     add_rel [::7;2;1;3;2;0;1] [::3;7;2;1;3;2;0]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 123 3 true;
         RTriple 8 1 true;
         RTriple 119 0 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 59 1 true;
         RTriple 52 1 true;
         RTriple 131 3 true];
     add_rel [::7;2;0;1;3;2;0;1;2] [::3;7;2;0;1;3;2;0;1]
     [:: RTriple 4 3 true;
         RTriple 5 2 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 125 6 true;
         RTriple 128 5 true;
         RTriple 9 3 true;
         RTriple 8 1 true;
         RTriple 119 0 true;
         RTriple 129 3 true;
         RTriple 127 5 true;
         RTriple 131 4 true;
         RTriple 128 7 true];
     add_rel [::0;3;2;0;1;2;7] [::3;2;0;1;2;7]
     [:: RTriple 5 0 true;
         RTriple 9 1 true;
         RTriple 127 3 true;
         RTriple 20 5 true];
     add_rel [::1;3;2;0;1;2;3;8] [::3;2;0;1;2;3;8]
     [:: RTriple 4 0 true;
         RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 125 3 true;
         RTriple 128 2 true;
         RTriple 5 5 true;
         RTriple 26 6 true];
     add_rel [::1;3;2;0;1;2;3;7] [::3;2;0;1;2;3;7]
     [:: RTriple 4 0 true;
         RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 125 3 true;
         RTriple 128 2 true;
         RTriple 5 5 true;
         RTriple 22 6 true];
     add_rel [::0;3;2;0;1;2;3;8] [::3;2;0;1;2;3;8]
     [:: RTriple 5 0 true;
         RTriple 9 1 true;
         RTriple 127 3 true;
         RTriple 4 5 true;
         RTriple 24 6 true];
     add_rel [::0;3;2;0;1;2;3;7] [::3;2;0;1;2;3;7]
     [:: RTriple 5 0 true;
         RTriple 9 1 true;
         RTriple 127 3 true;
         RTriple 15 6 true;
         RTriple 20 5 true;
         RTriple 119 5 true];
     add_rel [::7;2;0;3;2;5] [::8;3;2]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 5 3 true;
         RTriple 121 2 true;
         RTriple 11 5 true;
         RTriple 40 5 false;
         RTriple 98 3 true;
         RTriple 59 3 true;
         RTriple 52 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 5 3 true;
         RTriple 121 2 true;
         RTriple 12 5 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 129 2 true];
     add_rel [::7;2;1;3;4] [::7;2;1;3]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 18 4 true;
         RTriple 48 3 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 131 2 true];
     add_rel [::7;2;0;1;2;3;5] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 14 7 true;
         RTriple 94 7 false;
         RTriple 101 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;7] [::8;3]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 15 6 true;
         RTriple 20 6 false;
         RTriple 99 7 false;
         RTriple 101 3 true;
         RTriple 23 3 false;
         RTriple 24 3 true;
         RTriple 79 3 false;
         RTriple 80 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;2;6] [::8;3;2]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 101 3 true;
         RTriple 24 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;5] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 4 6 true;
         RTriple 40 11 false;
         RTriple 18 10 true;
         RTriple 103 3 true;
         RTriple 27 3 false;
         RTriple 28 3 true;
         RTriple 83 3 true;
         RTriple 56 3 true;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;3;6] [::7;2;0;3]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 5 3 true;
         RTriple 121 2 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 129 2 true];
     add_rel [::7;2;0;1;2;3;4] [::8;3]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 95 2 false;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 117 2 true;
         RTriple 13 7 true;
         RTriple 100 3 true;
         RTriple 26 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 124 1 true;
         RTriple 5 3 true;
         RTriple 121 2 true;
         RTriple 18 6 true;
         RTriple 10 5 true;
         RTriple 98 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::4;0;2;1;3;4] [::7;2;1;3]
     [:: RTriple 4 3 true;
         RTriple 18 4 true;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 131 2 true];
     add_rel [::5;0;1;2;3;4] [::7;2;3]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 13 5 true;
         RTriple 10 4 true;
         RTriple 98 2 true;
         RTriple 20 1 true;
         RTriple 52 0 true];
     add_rel [::7;2;1;3;2;5] [::8;3;2]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 122 1 true;
         RTriple 4 3 true;
         RTriple 118 2 true;
         RTriple 94 6 false;
         RTriple 12 5 true;
         RTriple 99 3 true;
         RTriple 10 4 true;
         RTriple 57 3 true;
         RTriple 42 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 48 3 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 131 2 true];
     add_rel [::7;2;0;1;3;2;4] [::8;3;2]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 122 1 true;
         RTriple 10 7 true;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 122 1 true;
         RTriple 4 3 true;
         RTriple 118 2 true;
         RTriple 17 6 true;
         RTriple 12 5 true;
         RTriple 99 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::6;1;2;0;3;6] [::7;2;0;3]
     [:: RTriple 5 3 true;
         RTriple 17 4 true;
         RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true;
         RTriple 129 2 true];
     add_rel [::5;0;1;2;3;6] [::7;2;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 16 5 true;
         RTriple 12 4 true;
         RTriple 99 2 true;
         RTriple 22 1 true;
         RTriple 42 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;6] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 95 2 false;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 117 2 true;
         RTriple 5 6 true;
         RTriple 6 9 true;
         RTriple 12 11 true;
         RTriple 17 10 true;
         RTriple 102 3 true;
         RTriple 29 3 false;
         RTriple 30 3 true;
         RTriple 33 3 false;
         RTriple 34 3 true;
         RTriple 30 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;2;3;2;4] [::8;3;2]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 95 2 false;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 117 2 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 100 3 true;
         RTriple 26 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::8;3;2;0;1;2;3;4] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 96 0 false;
         RTriple 4 5 true;
         RTriple 6 8 true;
         RTriple 7 6 true;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 119 2 true;
         RTriple 52 3 false;
         RTriple 51 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 125 7 true;
         RTriple 128 6 true;
         RTriple 129 5 true;
         RTriple 9 3 true;
         RTriple 123 2 true;
         RTriple 48 3 false;
         RTriple 13 11 true;
         RTriple 103 4 true;
         RTriple 56 3 true;
         RTriple 35 3 false;
         RTriple 36 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::8;3;2;0;1;2;3;5] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 96 0 false;
         RTriple 5 5 true;
         RTriple 9 6 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 119 2 true;
         RTriple 52 3 false;
         RTriple 51 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 129 5 true;
         RTriple 127 7 true;
         RTriple 131 6 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 123 2 true;
         RTriple 95 3 false;
         RTriple 4 10 true;
         RTriple 126 8 true;
         RTriple 125 6 true;
         RTriple 128 5 true;
         RTriple 117 4 true;
         RTriple 5 8 true;
         RTriple 94 12 false;
         RTriple 102 5 true;
         RTriple 81 5 true;
         RTriple 46 5 true;
         RTriple 30 4 true;
         RTriple 46 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::8;3;2;0;1;2;3;7] [::9]
     [:: RTriple 32 0 false;
         RTriple 31 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 96 0 false;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 119 2 true;
         RTriple 52 3 false;
         RTriple 51 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 129 5 true;
         RTriple 9 3 true;
         RTriple 123 2 true;
         RTriple 48 3 false;
         RTriple 22 11 false;
         RTriple 129 10 true;
         RTriple 15 11 true;
         RTriple 98 11 false;
         RTriple 103 4 true;
         RTriple 56 3 true;
         RTriple 29 3 false;
         RTriple 30 3 true;
         RTriple 121 4 true;
         RTriple 35 3 false;
         RTriple 36 3 true;
         RTriple 81 3 true;
         RTriple 46 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::8;3;2;0;1;2;3;8] [::9]
     [:: RTriple 96 0 false;
         RTriple 119 2 true;
         RTriple 52 3 false;
         RTriple 51 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 123 2 true;
         RTriple 95 3 false;
         RTriple 117 4 true;
         RTriple 26 9 false;
         RTriple 32 10 false;
         RTriple 24 11 false;
         RTriple 100 12 false;
         RTriple 102 5 true;
         RTriple 27 5 false;
         RTriple 28 5 true;
         RTriple 33 5 false;
         RTriple 29 6 false;
         RTriple 30 6 true;
         RTriple 34 5 true;
         RTriple 81 5 true;
         RTriple 46 5 true;
         RTriple 30 4 true;
         RTriple 46 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::6;1;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 18 6 true;
         RTriple 10 5 true;
         RTriple 13 4 true;
         RTriple 100 0 true];
     add_rel [::5;0;1;2;0;3;2;4] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 10 7 true;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;1;3;2;4] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;3;5] [::7;2;3]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 14 5 true;
         RTriple 11 4 true;
         RTriple 40 4 false;
         RTriple 98 2 true;
         RTriple 59 2 true;
         RTriple 52 2 true;
         RTriple 20 1 true;
         RTriple 52 0 true];
     add_rel [::7;2;0;1;3;2;5] [::8;3;2]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 6 3 true;
         RTriple 5 4 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 48 3 false;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 116 3 true;
         RTriple 131 2 true;
         RTriple 11 6 true;
         RTriple 40 6 false;
         RTriple 98 4 true;
         RTriple 59 4 true;
         RTriple 52 4 true;
         RTriple 15 3 true;
         RTriple 20 2 true;
         RTriple 96 0 true];
     add_rel [::5;1;2;3;5] [::7;2;3]
     [:: RTriple 95 0 false;
         RTriple 94 5 false;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;0;2;1;3;2;5] [::8;3;2]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 11 6 true;
         RTriple 14 5 true;
         RTriple 94 5 false;
         RTriple 101 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 94 0 false;
         RTriple 17 7 true;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 101 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;0;1;3;2;5] [::8;3;2]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 11 8 true;
         RTriple 14 7 true;
         RTriple 94 7 false;
         RTriple 101 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::7;2;0;1;2;3;2;5] [::8;3;2]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 6 3 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 48 3 false;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 116 3 true;
         RTriple 131 2 true;
         RTriple 14 7 true;
         RTriple 11 6 true;
         RTriple 40 6 false;
         RTriple 98 4 true;
         RTriple 59 4 true;
         RTriple 52 4 true;
         RTriple 15 3 true;
         RTriple 20 2 true;
         RTriple 96 0 true;
         RTriple 126 1 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::5;0;2;3;6] [::5;0;2;3]
     [:: RTriple 48 0 false;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::5;0;1;2;1;3;2;5] [::8;3;2]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 11 7 true;
         RTriple 14 6 true;
         RTriple 94 6 false;
         RTriple 101 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;2;3;5] [::7;2;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 14 4 true;
         RTriple 11 3 true;
         RTriple 40 3 false;
         RTriple 98 1 true;
         RTriple 59 1 true;
         RTriple 52 1 true;
         RTriple 52 0 true];
     add_rel [::5;1;2;0;3;6] [::7;2;0;3]
     [:: RTriple 95 0 false;
         RTriple 5 4 true;
         RTriple 17 5 true;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 129 2 true];
     add_rel [::5;1;2;0;3;2;5] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 40 7 false;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true;
         RTriple 96 0 false;
         RTriple 119 2 true;
         RTriple 11 4 true;
         RTriple 59 3 true;
         RTriple 52 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::5;1;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 95 0 false;
         RTriple 18 7 true;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 100 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;3;2;5] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 11 7 true;
         RTriple 14 6 true;
         RTriple 40 6 false;
         RTriple 100 2 true;
         RTriple 71 2 true;
         RTriple 54 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 17 8 true;
         RTriple 12 7 true;
         RTriple 16 6 true;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::7;2;0;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 120 2 true;
         RTriple 95 3 false;
         RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 117 3 true;
         RTriple 17 7 true;
         RTriple 12 6 true;
         RTriple 99 4 true;
         RTriple 22 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::5;0;2;1;3;4] [::7;2;1;3]
     [:: RTriple 94 0 false;
         RTriple 4 4 true;
         RTriple 18 5 true;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 68 0 true;
         RTriple 131 2 true];
     add_rel [::5;0;1;2;0;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 17 9 true;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 101 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 54 0 true];
     add_rel [::7;2;0;1;2;3;2;0;6] [::8;3;2;0]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 6 3 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 48 3 false;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 122 1 true;
         RTriple 118 2 true;
         RTriple 116 4 true;
         RTriple 129 8 true;
         RTriple 9 6 true;
         RTriple 124 5 true;
         RTriple 16 9 true;
         RTriple 12 8 true;
         RTriple 17 7 true;
         RTriple 95 6 true;
         RTriple 94 6 false;
         RTriple 12 5 true;
         RTriple 99 3 true;
         RTriple 10 4 true;
         RTriple 57 3 true;
         RTriple 42 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 125 2 true;
         RTriple 129 1 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 5 3 true;
         RTriple 126 1 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;4] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 4 6 true;
         RTriple 10 11 true;
         RTriple 18 10 true;
         RTriple 103 3 true;
         RTriple 27 3 false;
         RTriple 28 3 true;
         RTriple 33 3 false;
         RTriple 34 3 true;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;1;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 48 0 false;
         RTriple 95 0 false;
         RTriple 116 2 true;
         RTriple 124 3 true;
         RTriple 5 5 true;
         RTriple 121 4 true;
         RTriple 12 7 true;
         RTriple 17 6 true;
         RTriple 95 5 true;
         RTriple 94 5 false;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 129 2 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;7] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 42 0 false;
         RTriple 41 0 true;
         RTriple 9 2 true;
         RTriple 124 1 true;
         RTriple 127 4 true;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 4 6 true;
         RTriple 42 12 false;
         RTriple 10 11 true;
         RTriple 18 10 true;
         RTriple 103 3 true;
         RTriple 27 3 false;
         RTriple 28 3 true;
         RTriple 33 3 false;
         RTriple 34 3 true;
         RTriple 85 3 true;
         RTriple 66 3 true;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;5] [::9]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 5 6 true;
         RTriple 9 7 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 120 2 true;
         RTriple 95 3 false;
         RTriple 117 4 true;
         RTriple 11 12 true;
         RTriple 94 12 false;
         RTriple 102 5 true;
         RTriple 81 5 true;
         RTriple 46 5 true;
         RTriple 33 5 false;
         RTriple 34 5 true;
         RTriple 30 4 true;
         RTriple 46 3 true;
         RTriple 36 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;0;1;2;1;3;4] [::7;2;1;3]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 13 6 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 94 3 true;
         RTriple 11 2 true;
         RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 127 1 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::5;0;1;2;0;3;6] [::7;2;0;3]
     [:: RTriple 48 0 false;
         RTriple 95 0 false;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 9 4 true;
         RTriple 124 3 true;
         RTriple 16 7 true;
         RTriple 12 6 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 94 4 false;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 125 1 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::5;0;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 122 2 true;
         RTriple 4 4 true;
         RTriple 118 3 true;
         RTriple 10 6 true;
         RTriple 18 5 true;
         RTriple 94 4 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 131 2 true];
     add_rel [::5;0;2;1;3;2;0;1] [::3;5;0;2;1;3;2;0]
     [:: RTriple 4 3 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 120 0 true;
         RTriple 131 4 true];
     add_rel [::5;0;1;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 48 0 false;
         RTriple 95 0 false;
         RTriple 6 3 true;
         RTriple 116 2 true;
         RTriple 9 4 true;
         RTriple 124 3 true;
         RTriple 8 6 true;
         RTriple 5 5 true;
         RTriple 121 4 true;
         RTriple 16 8 true;
         RTriple 12 7 true;
         RTriple 17 6 true;
         RTriple 95 5 true;
         RTriple 94 5 false;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 129 2 true;
         RTriple 126 3 true;
         RTriple 125 1 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::5;0;1;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 118 3 true;
         RTriple 13 7 true;
         RTriple 10 6 true;
         RTriple 18 5 true;
         RTriple 94 4 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 40 2 false;
         RTriple 98 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 131 2 true;
         RTriple 126 3 true;
         RTriple 127 1 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::7;2;0;1;3;2;1;4] [::8;3;2;1]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 123 1 true;
         RTriple 6 3 true;
         RTriple 5 4 true;
         RTriple 4 3 true;
         RTriple 120 2 true;
         RTriple 48 3 false;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 116 3 true;
         RTriple 131 2 true;
         RTriple 18 7 true;
         RTriple 10 6 true;
         RTriple 98 4 true;
         RTriple 15 3 true;
         RTriple 20 2 true;
         RTriple 96 0 true];
     add_rel [::5;0;1;2;0;3;2;0] [::3;5;0;1;2;0;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 5 5 true;
         RTriple 9 6 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 118 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 129 5 true];
     add_rel [::5;0;1;2;1;3;2;1] [::3;5;0;1;2;1;3;2]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 4 5 true;
         RTriple 7 6 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 118 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 131 5 true];
     add_rel [::2;3;2;0;1;2;3;8] [::3;2;0;1;2;3;8]
     [:: RTriple 8 0 true;
         RTriple 129 2 true;
         RTriple 131 3 true;
         RTriple 126 4 true;
         RTriple 32 6 true];
     add_rel [::4;0;2;1;3;2;0;1] [::3;4;0;2;1;3;2;0]
     [:: RTriple 4 3 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true;
         RTriple 131 4 true];
     add_rel [::0;2;0;1;2;3;2;0;1;2;7] [::2;0;1;2;3;2;0;1;2;7]
     [:: RTriple 9 0 true;
         RTriple 127 2 true;
         RTriple 4 4 true;
         RTriple 6 7 true;
         RTriple 7 5 true;
         RTriple 125 7 true;
         RTriple 128 6 true;
         RTriple 22 9 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;3] [::3;7;2;0;1;2;3;2;0;1;2]
     [:: RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 5 2 true;
         RTriple 129 6 true;
         RTriple 131 7 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 126 8 true;
         RTriple 125 6 true;
         RTriple 128 5 true;
         RTriple 9 3 true;
         RTriple 8 1 true;
         RTriple 119 0 true;
         RTriple 129 3 true;
         RTriple 127 5 true;
         RTriple 131 4 true;
         RTriple 128 7 true;
         RTriple 4 8 true;
         RTriple 5 7 true;
         RTriple 126 5 true];
     add_rel [::1;2;0;1;2;3;2;0;1;2;7] [::2;0;1;2;3;2;0;1;2;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 125 2 true;
         RTriple 128 1 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 127 7 true;
         RTriple 20 9 true];
     add_rel [::0;2;0;1;2;3;2;0;1;2;3;7] [::2;0;1;2;3;2;0;1;2;3;7]
     [:: RTriple 9 0 true;
         RTriple 127 2 true;
         RTriple 4 4 true;
         RTriple 6 7 true;
         RTriple 7 5 true;
         RTriple 125 7 true;
         RTriple 128 6 true;
         RTriple 5 9 true;
         RTriple 22 10 true];
     add_rel [::1;2;0;1;2;3;2;0;1;2;3;7] [::2;0;1;2;3;2;0;1;2;3;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 125 2 true;
         RTriple 128 1 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 127 7 true;
         RTriple 15 10 true;
         RTriple 20 9 true;
         RTriple 119 9 true];
     add_rel [::7;2;0;1;2;3;2;1;4] [::8;3;2;1]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 123 1 true;
         RTriple 95 2 false;
         RTriple 10 1 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 125 4 true;
         RTriple 128 3 true;
         RTriple 117 2 true;
         RTriple 18 9 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 100 3 true;
         RTriple 26 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;1;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 18 8 true;
         RTriple 10 7 true;
         RTriple 13 6 true;
         RTriple 100 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::4;0;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 4 3 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 131 2 true];
     add_rel [::6;1;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 5 3 true;
         RTriple 12 5 true;
         RTriple 17 4 true;
         RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true;
         RTriple 129 2 true];
     add_rel [::5;0;1;2;0;1;3;2;1;4] [::8;3;2;1]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 122 2 true;
         RTriple 18 9 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;1;3;2;0;1] [::3;5;0;1;2;1;3;2;0]
     [:: RTriple 95 0 false;
         RTriple 117 1 true;
         RTriple 4 5 true;
         RTriple 6 8 true;
         RTriple 7 6 true;
         RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 118 2 true;
         RTriple 5 1 true;
         RTriple 121 0 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 131 5 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;2] [::3;5;0;1;2;0;1;3;2;0;1]
     [:: RTriple 48 0 false;
         RTriple 6 2 true;
         RTriple 116 1 true;
         RTriple 9 3 true;
         RTriple 124 2 true;
         RTriple 4 6 true;
         RTriple 6 9 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 121 3 true;
         RTriple 125 9 true;
         RTriple 128 8 true;
         RTriple 129 7 true;
         RTriple 9 5 true;
         RTriple 124 4 true;
         RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 120 0 true;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 18 2 true;
         RTriple 48 1 true;
         RTriple 129 4 true;
         RTriple 126 5 true;
         RTriple 125 3 true;
         RTriple 128 2 true;
         RTriple 127 7 true;
         RTriple 131 6 true;
         RTriple 128 9 true];
     rm_rel 4
     [:: RTriple 130 0 false];
     rm_rel 4
     [:: RTriple 127 0 false];
     rm_rel 4
     [:: RTriple 125 0 false];
     rm_rel 4
     [:: RTriple 123 0 false];
     rm_rel 4
     [:: RTriple 121 0 false];
     rm_rel 4
     [:: RTriple 119 0 false];
     rm_rel 4
     [:: RTriple 117 0 false];
     rm_rel 4
     [:: RTriple 115 0 false];
     rm_rel 4
     [:: RTriple 113 0 false];
     rm_rel 4
     [:: RTriple 111 0 false];
     rm_rel 4
     [:: RTriple 109 0 false];
     rm_rel 4
     [:: RTriple 107 0 false];
     rm_rel 4
     [:: RTriple 105 0 false];
     rm_rel 4
     [:: RTriple 103 0 false];
     rm_rel 4
     [:: RTriple 101 0 false];
     rm_rel 4
     [:: RTriple 4 0 true;
         RTriple 99 0 false];
     rm_rel 5
     [:: RTriple 5 0 true;
         RTriple 97 0 false];
     rm_rel 6
     [:: RTriple 6 0 true;
         RTriple 95 0 false];
     rm_rel 7
     [:: RTriple 7 0 true;
         RTriple 93 0 false];
     rm_rel 8
     [:: RTriple 8 0 true;
         RTriple 91 0 false];
     rm_rel 9
     [:: RTriple 9 0 true;
         RTriple 89 0 false];
     rm_rel 10
     [:: RTriple 10 0 true;
         RTriple 87 0 false];
     rm_rel 11
     [:: RTriple 11 0 true;
         RTriple 85 0 false];
     rm_rel 12
     [:: RTriple 12 0 true;
         RTriple 83 0 false];
     rm_rel 13
     [::];
     rm_rel 14
     [:: RTriple 14 0 true;
         RTriple 22 0 false];
     rm_rel 15
     [:: RTriple 15 0 true;
         RTriple 31 0 false];
     rm_rel 16
     [:: RTriple 16 0 true;
         RTriple 42 0 false];
     rm_rel 17
     [:: RTriple 17 0 true;
         RTriple 53 0 false];
     rm_rel 18
     [:: RTriple 18 0 true;
         RTriple 14 0 false];
     rm_rel 19
     [::];
     rm_rel 20
     [:: RTriple 20 0 true;
         RTriple 28 0 false];
     rm_rel 21
     [:: RTriple 21 0 true;
         RTriple 39 0 false];
     rm_rel 22
     [:: RTriple 22 0 true;
         RTriple 50 0 false];
     rm_rel 23
     [:: RTriple 23 0 true;
         RTriple 15 0 false];
     rm_rel 24
     [:: RTriple 24 0 true;
         RTriple 20 0 false];
     rm_rel 25
     [::];
     rm_rel 26
     [:: RTriple 26 0 true;
         RTriple 36 0 false];
     rm_rel 27
     [:: RTriple 27 0 true;
         RTriple 47 0 false];
     rm_rel 28
     [:: RTriple 28 0 true;
         RTriple 66 0 false];
     rm_rel 29
     [:: RTriple 29 0 true;
         RTriple 16 0 false];
     rm_rel 30
     [:: RTriple 30 0 true;
         RTriple 21 0 false];
     rm_rel 31
     [:: RTriple 31 0 true;
         RTriple 26 0 false];
     rm_rel 32
     [::];
     rm_rel 33
     [:: RTriple 33 0 true;
         RTriple 43 0 false];
     rm_rel 34
     [:: RTriple 34 0 true;
         RTriple 59 0 false];
     rm_rel 35
     [:: RTriple 35 0 true;
         RTriple 17 0 false];
     rm_rel 36
     [:: RTriple 36 0 true;
         RTriple 22 0 false];
     rm_rel 37
     [:: RTriple 37 0 true;
         RTriple 27 0 false];
     rm_rel 38
     [:: RTriple 38 0 true;
         RTriple 33 0 false];
     rm_rel 39
     [::];
     rm_rel 40
     [:: RTriple 40 0 true;
         RTriple 52 0 false];
     rm_rel 50
     [:: RTriple 76 3 true;
         RTriple 77 0 true];
     rm_rel 50
     [:: RTriple 77 3 true;
         RTriple 78 0 true]].

Definition RennerD41_Gay_order := [::0;1;2;3;4;5;6;7;8;9].

(*
Eval compute in size (prelat RennerD41_Gay).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat RennerD41_Gay)].
Eval compute in size (prelat RennerD41_Gay_rws).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat RennerD41_Gay_rws)].
Eval compute in size RennerD41_Gay_cert.
*)

Theorem isopres_RennerD41_Gay : isopres RennerD41_Gay RennerD41_Gay_rws.
Proof.
have wfc : wfpres_cert RennerD41_Gay RennerD41_Gay_cert
  by vm_cast_no_check is_true_true.
suff -> : RennerD41_Gay_rws = final_pres wfc by apply: iso_final_pres.
apply/eqP; rewrite -eqpresE pgen_final_pres prelat_final_pres.
by vm_cast_no_check is_true_true.
Time Qed.

Theorem RennerD41_Gay_rws_convergent : convergent (prelat RennerD41_Gay_rws).
Proof.
apply: diamond.
  apply: (rgen_pres_terminating
            (newgK := reorderK (l := RennerD41_Gay_order) is_true_true)).
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
have pgenOk : all (<%O^~ PArray.max_length) (pgen RennerD41_Gay_rws) by [].
apply: (spair_confluence_loop_trieP pgenOk (fuel := 10)).
rewrite spair_confluence_loop_trieE.
by native_cast_no_check is_true_true.
Time Qed.


Definition not_RennerD41_rws := make_pres [::0;1;2;3;4;5;6;7;8;9]
  [:: ([::0;0], [::]);
      ([::1;1], [::]);
      ([::2;2], [::]);
      ([::3;3], [::]);
      ([::1;7], [::7]);
      ([::0;7], [::7]);
      ([::1;8], [::8]);
      ([::0;8], [::8]);
      ([::1;9], [::9]);
      ([::0;9], [::9]);
      ([::2;8], [::8]);
      ([::2;9], [::9]);
      ([::3;9], [::9]);
      ([::4;4], [::4]);
      ([::4;5], [::5]);
      ([::4;7], [::7]);
      ([::4;8], [::8]);
      ([::4;9], [::9]);
      ([::5;4], [::5]);
      ([::5;5], [::5]);
      ([::5;7], [::7]);
      ([::5;8], [::8]);
      ([::5;9], [::9]);
      ([::7;4], [::7]);
      ([::7;5], [::7]);
      ([::7;7], [::7]);
      ([::7;8], [::8]);
      ([::7;9], [::9]);
      ([::6;7], [::7]);
      ([::8;4], [::8]);
      ([::8;5], [::8]);
      ([::8;7], [::8]);
      ([::8;8], [::8]);
      ([::8;9], [::9]);
      ([::6;8], [::8]);
      ([::9;4], [::9]);
      ([::9;5], [::9]);
      ([::9;7], [::9]);
      ([::9;8], [::9]);
      ([::9;9], [::9]);
      ([::6;9], [::9]);
      ([::6;6], [::6]);
      ([::6;4], [::5]);
      ([::4;6], [::5]);
      ([::7;2;7], [::8]);
      ([::8;3;8], [::9]);
      ([::4;0;4], [::7]);
      ([::6;1;6], [::7]);
      ([::4;0;2;1;6], [::8]);
      ([::6;1;2;0;4], [::8]);
      ([::1;0], [::0;1]);
      ([::2;0;2], [::0;2;0]);
      ([::2;1;2], [::1;2;1]);
      ([::3;0], [::0;3]);
      ([::3;1], [::1;3]);
      ([::3;2;3], [::2;3;2]);
      ([::4;1], [::1;4]);
      ([::4;2], [::2;4]);
      ([::4;3], [::3;4]);
      ([::5;2], [::2;5]);
      ([::5;3], [::3;5]);
      ([::6;0], [::0;6]);
      ([::6;2], [::2;6]);
      ([::6;3], [::3;6]);
      ([::7;0], [::7]);
      ([::7;1], [::7]);
      ([::7;3], [::3;7]);
      ([::7;6], [::7]);
      ([::8;0], [::8]);
      ([::8;1], [::8]);
      ([::8;2], [::8]);
      ([::8;6], [::8]);
      ([::9;0], [::9]);
      ([::9;1], [::9]);
      ([::9;2], [::9]);
      ([::9;3], [::9]);
      ([::9;6], [::9]);
      ([::0;3;7], [::3;7]);
      ([::0;3;8], [::3;8]);
      ([::1;3;7], [::3;7]);
      ([::1;3;8], [::3;8]);
      ([::2;0;1;2;1], [::0;2;0;1;2]);
      ([::2;0;1;2;0], [::1;2;0;1;2]);
      ([::3;2;0;3], [::2;3;2;0]);
      ([::3;2;1;3], [::2;3;2;1]);
      ([::4;0;1], [::1;4;0]);
      ([::4;0;2;0], [::2;4;0;2]);
      ([::4;0;2;7], [::8]);
      ([::4;0;2;4], [::7;2]);
      ([::4;0;3], [::3;4;0]);
      ([::4;0;5], [::7]);
      ([::4;0;6], [::5;0]);
      ([::5;0;2;0], [::2;5;0;2]);
      ([::5;0;2;1;6], [::8]);
      ([::5;0;3], [::3;5;0]);
      ([::5;0;4], [::7]);
      ([::5;1;2;0;4], [::8]);
      ([::5;1;2;1], [::2;5;1;2]);
      ([::5;1;3], [::3;5;1]);
      ([::5;1;4], [::5;1]);
      ([::5;1;6], [::7]);
      ([::5;6], [::5]);
      ([::6;1;2;0;3;4], [::8;3]);
      ([::6;1;2;0;5], [::8]);
      ([::6;1;2;7], [::8]);
      ([::6;1;2;6], [::7;2]);
      ([::7;2;1;6], [::8]);
      ([::7;2;0;4], [::8]);
      ([::4;0;2;1;3;6], [::8;3]);
      ([::4;0;2;1;5], [::8]);
      ([::6;1;2;1], [::2;6;1;2]);
      ([::6;1;3], [::3;6;1]);
      ([::6;1;4], [::5;1]);
      ([::6;1;5], [::7]);
      ([::6;5], [::5]);
      ([::7;2;3;2], [::3;7;2;3]);
      ([::7;2;3;7], [::8;3]);
      ([::7;2;4], [::7;2]);
      ([::7;2;5], [::7;2]);
      ([::7;2;6], [::7;2]);
      ([::8;3;4], [::8;3]);
      ([::8;3;5], [::8;3]);
      ([::8;3;6], [::8;3]);
      ([::8;3;7], [::8;3]);
      ([::0;2;0;1;2;3;7], [::2;0;1;2;3;7]);
      ([::0;2;0;1;2;3;8], [::2;0;1;2;3;8]);
      ([::0;2;0;1;2;7], [::2;0;1;2;7]);
      ([::1;2;0;1;2;3;7], [::2;0;1;2;3;7]);
      ([::1;2;0;1;2;3;8], [::2;0;1;2;3;8]);
      ([::1;2;0;1;2;7], [::2;0;1;2;7]);
      ([::3;2;0;1;3], [::2;3;2;0;1]);
      ([::4;0;2;1;4], [::7;2;1]);
      ([::4;0;2;3;2], [::3;4;0;2;3]);
      ([::4;0;2;3;4], [::7;2;3]);
      ([::4;0;2;3;7], [::8;3]);
      ([::4;0;2;5], [::7;2]);
      ([::7;2;0;6], [::7;2;0]);
      ([::4;0;2;6], [::5;0;2]);
      ([::5;0;1;2;0;1;2], [::2;5;0;1;2;0;1]);
      ([::5;0;1;2;0;4], [::8]);
      ([::5;0;1;6], [::7]);
      ([::5;0;2;4], [::7;2]);
      ([::5;0;2;7], [::8]);
      ([::5;0;5], [::7]);
      ([::5;0;6], [::5;0]);
      ([::7;2;0;1;6], [::8]);
      ([::7;2;0;5], [::8]);
      ([::5;0;1;3], [::3;5;0;1]);
      ([::5;0;1;4], [::7]);
      ([::5;0;1;2;1;6], [::8]);
      ([::5;0;2;1;3;6], [::8;3]);
      ([::5;0;2;1;5], [::8]);
      ([::5;0;2;3;2], [::3;5;0;2;3]);
      ([::5;0;1;2;4], [::7;2]);
      ([::5;0;1;2;7], [::8]);
      ([::5;0;1;5], [::7]);
      ([::5;1;2;0;1], [::2;5;1;2;0]);
      ([::5;1;2;0;3;4], [::8;3]);
      ([::5;1;2;0;5], [::8]);
      ([::5;1;2;7], [::8]);
      ([::5;1;2;3;2], [::3;5;1;2;3]);
      ([::5;0;1;2;0;1;4], [::8]);
      ([::5;0;1;2;0;3;4], [::8;3]);
      ([::5;0;1;2;0;5], [::8]);
      ([::5;1;2;4], [::5;1;2]);
      ([::5;1;2;6], [::7;2]);
      ([::5;1;5], [::7]);
      ([::6;1;2;0;3;2;4], [::8;3;2]);
      ([::6;1;2;0;3;5], [::8;3]);
      ([::6;1;2;3;7], [::8;3]);
      ([::8;3;2;4], [::8;3;2]);
      ([::8;3;2;7], [::9]);
      ([::7;2;0;1;4], [::8]);
      ([::7;2;0;3;4], [::8;3]);
      ([::8;3;2;1;6], [::9]);
      ([::6;1;2;3;8], [::9]);
      ([::4;0;2;1;3;2;6], [::8;3;2]);
      ([::4;0;2;1;3;5], [::8;3]);
      ([::8;3;2;6], [::8;3;2]);
      ([::4;0;2;3;8], [::9]);
      ([::5;0;1;2;6], [::7;2]);
      ([::5;0;1;2;1;3;6], [::8;3]);
      ([::6;1;2;0;6], [::7;2;0]);
      ([::6;1;2;3;6], [::7;2;3]);
      ([::6;1;2;5], [::7;2]);
      ([::7;2;1;3;6], [::8;3]);
      ([::7;2;0;1;3;6], [::8;3]);
      ([::7;2;0;1;3;4], [::8;3]);
      ([::7;2;0;1;5], [::8]);
      ([::7;2;1;5], [::8]);
      ([::8;3;2;0;1;4], [::9]);
      ([::8;3;2;0;4], [::9]);
      ([::8;3;2;0;5], [::9]);
      ([::5;0;1;2;1;5], [::8]);
      ([::6;1;2;0;1], [::2;6;1;2;0]);
      ([::6;1;2;3;2], [::3;6;1;2;3]);
      ([::6;1;2;4], [::5;1;2]);
      ([::7;2;1;4], [::7;2;1]);
      ([::8;3;2;1;5], [::9]);
      ([::7;2;0;3;2;0], [::3;7;2;0;3;2]);
      ([::7;2;1;3;2;1], [::3;7;2;1;3;2]);
      ([::7;2;3;4], [::7;2;3]);
      ([::8;3;2;5], [::8;3;2]);
      ([::7;2;3;8], [::9]);
      ([::7;2;3;5], [::7;2;3]);
      ([::7;2;3;6], [::7;2;3]);
      ([::0;3;2;0;1;2;3;7], [::3;2;0;1;2;3;7]);
      ([::0;3;2;0;1;2;3;8], [::3;2;0;1;2;3;8]);
      ([::0;3;2;0;1;2;7], [::3;2;0;1;2;7]);
      ([::1;3;2;0;1;2;3;7], [::3;2;0;1;2;3;7]);
      ([::1;3;2;0;1;2;3;8], [::3;2;0;1;2;3;8]);
      ([::1;3;2;0;1;2;7], [::3;2;0;1;2;7]);
      ([::3;2;0;1;2;3;2], [::2;3;2;0;1;2;3]);
      ([::5;0;1;2;1;4], [::7;2;1]);
      ([::7;2;0;1;2;3;6], [::8;3]);
      ([::7;2;0;1;2;4], [::8]);
      ([::7;2;0;1;2;5], [::8]);
      ([::8;3;2;1;4], [::8;3;2;1]);
      ([::4;0;2;1;3;4], [::7;2;1;3]);
      ([::4;0;2;1;3;2;1], [::3;4;0;2;1;3;2]);
      ([::4;0;2;3;5], [::7;2;3]);
      ([::7;2;0;3;6], [::7;2;0;3]);
      ([::5;0;2;1;4], [::7;2;1]);
      ([::5;0;2;3;4], [::7;2;3]);
      ([::5;0;1;2;3;4], [::7;2;3]);
      ([::5;0;1;2;3;7], [::8;3]);
      ([::5;0;1;2;3;2], [::3;5;0;1;2;3]);
      ([::7;2;0;1;2;6], [::8]);
      ([::7;2;0;1;2;3;4], [::8;3]);
      ([::7;2;0;1;2;3;7], [::8;3]);
      ([::7;2;0;1;2;7], [::8]);
      ([::7;2;0;3;2;1;6], [::9]);
      ([::7;2;0;3;2;1;4], [::8;3;2;1]);
      ([::7;2;0;3;2;1;5], [::9]);
      ([::7;2;0;3;2;4], [::8;3;2]);
      ([::7;2;0;3;2;7], [::9]);
      ([::7;2;0;3;5], [::8;3]);
      ([::7;2;0;3;2;6], [::7;2;0;3;2]);
      ([::4;0;2;3;6], [::5;0;2;3]);
      ([::8;3;2;0;6], [::8;3;2;0]);
      ([::5;0;1;2;0;1;3;4], [::8;3]);
      ([::5;0;1;2;0;1;5], [::8]);
      ([::5;0;2;3;7], [::8;3]);
      ([::5;0;2;5], [::7;2]);
      ([::5;0;2;6], [::5;0;2]);
      ([::5;0;1;2;5], [::7;2]);
      ([::7;2;0;3;2;5], [::8;3;2]);
      ([::8;3;2;0;1;6], [::9]);
      ([::5;0;1;2;0;1;6], [::8]);
      ([::5;0;2;1;3;2;6], [::8;3;2]);
      ([::5;0;2;1;3;5], [::8;3]);
      ([::5;0;2;3;8], [::9]);
      ([::5;0;2;1;3;2;1], [::3;5;0;2;1;3;2]);
      ([::5;1;2;3;7], [::8;3]);
      ([::5;1;2;3;8], [::9]);
      ([::5;1;2;0;3;2;4], [::8;3;2]);
      ([::5;1;2;0;3;5], [::8;3]);
      ([::5;0;1;2;0;3;2;4], [::8;3;2]);
      ([::5;0;1;2;0;3;5], [::8;3]);
      ([::5;0;1;2;3;8], [::9]);
      ([::5;1;2;0;3;2;0], [::3;5;1;2;0;3;2]);
      ([::5;0;1;2;0;1;3;6], [::8;3]);
      ([::5;1;2;0;6], [::7;2;0]);
      ([::5;1;2;3;4], [::5;1;2;3]);
      ([::5;1;2;3;6], [::7;2;3]);
      ([::5;1;2;5], [::7;2]);
      ([::5;0;1;2;0;6], [::7;2;0]);
      ([::5;0;1;2;0;1;3;2;4], [::8;3;2]);
      ([::5;0;1;2;0;1;3;5], [::8;3]);
      ([::6;1;2;0;3;2;1;4], [::8;3;2;1]);
      ([::6;1;2;0;3;2;5], [::8;3;2]);
      ([::6;1;2;0;3;2;7], [::9]);
      ([::7;2;0;1;2;3;2;4], [::8;3;2]);
      ([::7;2;0;1;2;3;5], [::8;3]);
      ([::7;2;0;1;3;2;4], [::8;3;2]);
      ([::7;2;0;1;3;5], [::8;3]);
      ([::8;3;2;0;1;5], [::9]);
      ([::4;0;2;1;3;2;0;6], [::8;3;2;0]);
      ([::4;0;2;1;3;2;5], [::8;3;2]);
      ([::4;0;2;1;3;2;7], [::9]);
      ([::5;0;1;2;1;3;2;6], [::8;3;2]);
      ([::5;0;1;2;0;1;3;2;6], [::8;3;2]);
      ([::7;2;1;3;2;6], [::8;3;2]);
      ([::7;2;0;1;2;3;8], [::9]);
      ([::7;2;0;1;3;2;6], [::8;3;2]);
      ([::7;2;0;1;2;3;2;6], [::8;3;2]);
      ([::7;2;0;1;3;2;1;6], [::9]);
      ([::8;3;2;0;1;2;6], [::9]);
      ([::8;3;2;0;1;2;4], [::9]);
      ([::5;0;1;2;1;3;5], [::8;3]);
      ([::7;2;1;3;5], [::8;3]);
      ([::5;0;1;2;3;6], [::7;2;3]);
      ([::6;1;2;0;3;6], [::7;2;0;3]);
      ([::6;1;2;3;5], [::7;2;3]);
      ([::7;2;1;3;4], [::7;2;1;3]);
      ([::7;2;0;1;3;2;0;4], [::9]);
      ([::7;2;1;3;2;0;4], [::9]);
      ([::7;2;1;3;2;0;5], [::9]);
      ([::7;2;1;3;2;0;6], [::8;3;2;0]);
      ([::7;2;1;3;2;7], [::9]);
      ([::7;2;1;3;2;5], [::8;3;2]);
      ([::7;2;1;3;2;0;1], [::3;7;2;1;3;2;0]);
      ([::6;1;2;0;3;2;0], [::3;6;1;2;0;3;2]);
      ([::6;1;2;3;4], [::5;1;2;3]);
      ([::7;2;1;3;2;4], [::7;2;1;3;2]);
      ([::7;2;0;1;3;2;0;1;2], [::3;7;2;0;1;3;2;0;1]);
      ([::8;3;2;0;1;2;3;4], [::9]);
      ([::8;3;2;0;1;2;5], [::9]);
      ([::8;3;2;0;1;2;3;6], [::9]);
      ([::8;3;2;0;1;2;7], [::9]);
      ([::7;2;0;1;3;2;0;1;4], [::9]);
      ([::7;2;0;1;2;3;2;0;4], [::9]);
      ([::7;2;0;1;3;2;0;5], [::9]);
      ([::7;2;0;1;2;3;2;1;6], [::9]);
      ([::7;2;0;1;3;2;1;5], [::9]);
      ([::7;2;0;1;3;2;7], [::9]);
      ([::1;2;0;1;2;3;2;0;1;2;3;7], [::2;0;1;2;3;2;0;1;2;3;7]);
      ([::0;2;0;1;2;3;2;0;1;2;3;7], [::2;0;1;2;3;2;0;1;2;3;7]);
      ([::1;2;0;1;2;3;2;0;1;2;7], [::2;0;1;2;3;2;0;1;2;7]);
      ([::0;2;0;1;2;3;2;0;1;2;7], [::2;0;1;2;3;2;0;1;2;7]);
      ([::2;3;2;0;1;2;3;8], [::3;2;0;1;2;3;8]);
      ([::5;0;1;2;1;3;4], [::7;2;1;3]);
      ([::7;2;0;1;3;2;1;4], [::8;3;2;1]);
      ([::7;2;0;1;2;3;2;1;4], [::8;3;2;1]);
      ([::7;2;0;1;2;3;2;1;5], [::9]);
      ([::7;2;0;1;3;2;5], [::8;3;2]);
      ([::8;3;2;0;1;2;3;5], [::9]);
      ([::8;3;2;0;1;2;3;7], [::9]);
      ([::8;3;2;0;1;2;3;8], [::9]);
      ([::4;0;2;1;3;2;0;1], [::3;4;0;2;1;3;2;0]);
      ([::4;0;2;1;3;2;4], [::7;2;1;3;2]);
      ([::5;0;2;1;3;4], [::7;2;1;3]);
      ([::5;0;1;2;0;1;3;2;0;1;2], [::3;5;0;1;2;0;1;3;2;0;1]);
      ([::7;2;0;1;2;3;2;7], [::9]);
      ([::5;0;2;3;5], [::7;2;3]);
      ([::5;0;1;2;3;5], [::7;2;3]);
      ([::5;0;1;2;1;3;2;1], [::3;5;0;1;2;1;3;2]);
      ([::7;2;0;1;3;2;0;6], [::8;3;2;0]);
      ([::7;2;0;1;2;3;2;5], [::8;3;2]);
      ([::7;2;0;1;2;3;2;0;5], [::9]);
      ([::5;0;1;2;0;3;2;0], [::3;5;0;1;2;0;3;2]);
      ([::5;0;2;1;3;2;0;1], [::3;5;0;2;1;3;2;0]);
      ([::5;0;1;2;0;1;3;2;0;4], [::9]);
      ([::5;0;1;2;1;3;2;0;5], [::9]);
      ([::5;0;2;1;3;2;0;6], [::8;3;2;0]);
      ([::5;0;1;2;1;3;2;7], [::9]);
      ([::5;0;2;1;3;2;4], [::7;2;1;3;2]);
      ([::5;0;2;1;3;2;5], [::8;3;2]);
      ([::5;0;1;2;0;3;6], [::7;2;0;3]);
      ([::7;2;0;1;2;3;2;0;1;2;4], [::9]);
      ([::7;2;0;1;2;3;2;0;1;4], [::9]);
      ([::7;2;0;1;2;3;2;0;1;5], [::9]);
      ([::7;2;0;1;3;2;0;1;5], [::9]);
      ([::7;2;0;1;3;2;0;1;6], [::9]);
      ([::5;0;1;2;1;3;2;0;4], [::9]);
      ([::5;0;2;1;3;2;0;4], [::9]);
      ([::5;0;2;1;3;2;0;5], [::9]);
      ([::5;0;2;1;3;2;7], [::9]);
      ([::5;0;2;3;6], [::5;0;2;3]);
      ([::5;1;2;0;3;2;5], [::8;3;2]);
      ([::5;1;2;0;3;2;7], [::9]);
      ([::5;1;2;0;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;3;2;5], [::8;3;2]);
      ([::5;0;1;2;0;3;2;7], [::9]);
      ([::7;2;0;1;2;3;2;0;1;6], [::9]);
      ([::5;1;2;0;3;6], [::7;2;0;3]);
      ([::5;0;1;2;0;1;3;2;1;6], [::9]);
      ([::5;0;1;2;0;3;2;1;5], [::9]);
      ([::5;0;1;2;0;3;2;1;6], [::9]);
      ([::5;1;2;0;3;2;1;5], [::9]);
      ([::5;1;2;0;3;2;1;6], [::9]);
      ([::5;1;2;0;3;2;6], [::7;2;0;3;2]);
      ([::5;0;1;2;0;3;2;6], [::7;2;0;3;2]);
      ([::5;1;2;3;5], [::7;2;3]);
      ([::5;0;1;2;0;1;3;2;1;4], [::8;3;2;1]);
      ([::5;0;1;2;0;1;3;2;5], [::8;3;2]);
      ([::5;0;1;2;0;1;3;2;7], [::9]);
      ([::5;0;1;2;0;1;3;2;0;1;4], [::9]);
      ([::5;0;1;2;0;1;3;2;0;5], [::9]);
      ([::6;1;2;0;3;2;1;5], [::9]);
      ([::7;2;0;1;2;3;2;0;1;2;5], [::9]);
      ([::7;2;0;1;2;3;2;0;1;2;7], [::9]);
      ([::5;0;1;2;0;1;3;2;0;6], [::8;3;2;0]);
      ([::5;0;1;2;0;1;3;2;0;1;6], [::9]);
      ([::7;2;0;1;2;3;2;0;6], [::8;3;2;0]);
      ([::4;0;2;1;3;2;0;5], [::9]);
      ([::5;0;1;2;1;3;2;0;6], [::8;3;2;0]);
      ([::5;0;1;2;0;1;3;2;1;5], [::9]);
      ([::5;0;1;2;1;3;2;5], [::8;3;2]);
      ([::7;2;0;1;2;3;2;0;1;2;6], [::9]);
      ([::6;1;2;0;3;2;6], [::7;2;0;3;2]);
      ([::5;0;1;2;1;3;2;4], [::7;2;1;3;2]);
      ([::7;2;0;1;2;3;2;0;1;2;3], [::3;7;2;0;1;2;3;2;0;1;2]);
      ([::5;0;1;2;1;3;2;0;1], [::3;5;0;1;2;1;3;2;0]);
      ([::5;0;1;2;0;1;3;2;0;1;5], [::9])].

Definition not_RennerD41_cert : pres_cert := [:: add_rel [::1;0] [::0;1]
     [:: RTriple 6 0 false];
     add_rel [::2;0;2] [::0;2;0]
     [:: RTriple 9 0 false];
     add_rel [::2;1;2] [::1;2;1]
     [:: RTriple 7 0 false];
     add_rel [::3;0] [::0;3]
     [:: RTriple 5 0 false];
     add_rel [::3;1] [::1;3]
     [:: RTriple 4 0 false];
     add_rel [::3;2;3] [::2;3;2]
     [:: RTriple 8 0 false];
     add_rel [::4;1] [::1;4]
     [:: RTriple 18 0 false];
     add_rel [::4;2] [::2;4]
     [:: RTriple 10 0 false];
     add_rel [::4;3] [::3;4]
     [:: RTriple 13 0 false];
     add_rel [::5;2] [::2;5]
     [:: RTriple 11 0 false];
     add_rel [::5;3] [::3;5]
     [:: RTriple 14 0 false];
     add_rel [::6;0] [::0;6]
     [:: RTriple 17 0 false];
     add_rel [::6;2] [::2;6]
     [:: RTriple 12 0 false];
     add_rel [::6;3] [::3;6]
     [:: RTriple 16 0 false];
     add_rel [::7;0] [::7]
     [:: RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::7;1] [::7]
     [:: RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::7;3] [::3;7]
     [:: RTriple 15 0 false];
     add_rel [::7;6] [::7]
     [:: RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::8;0] [::8]
     [:: RTriple 25 0 false;
         RTriple 26 0 true];
     add_rel [::8;1] [::8]
     [:: RTriple 23 0 false;
         RTriple 24 0 true];
     add_rel [::8;2] [::8]
     [:: RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::8;6] [::8]
     [:: RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::9;0] [::9]
     [:: RTriple 29 0 false;
         RTriple 30 0 true];
     add_rel [::9;1] [::9]
     [:: RTriple 27 0 false;
         RTriple 28 0 true];
     add_rel [::9;2] [::9]
     [:: RTriple 33 0 false;
         RTriple 34 0 true];
     add_rel [::9;3] [::9]
     [:: RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::9;6] [::9]
     [:: RTriple 91 0 false;
         RTriple 92 0 true];
     add_rel [::0;3;7] [::3;7]
     [:: RTriple 15 1 true;
         RTriple 22 0 true;
         RTriple 118 0 true];
     add_rel [::0;3;8] [::3;8]
     [:: RTriple 5 0 true;
         RTriple 26 1 true];
     add_rel [::1;3;7] [::3;7]
     [:: RTriple 15 1 true;
         RTriple 20 0 true;
         RTriple 118 0 true];
     add_rel [::1;3;8] [::3;8]
     [:: RTriple 4 0 true;
         RTriple 24 1 true];
     add_rel [::2;0;1;2;1] [::0;2;0;1;2]
     [:: RTriple 7 2 true;
         RTriple 103 0 true];
     add_rel [::2;0;1;2;0] [::1;2;0;1;2]
     [:: RTriple 6 1 true;
         RTriple 9 2 true;
         RTriple 104 0 true;
         RTriple 102 2 true];
     add_rel [::3;2;0;3] [::2;3;2;0]
     [:: RTriple 5 2 true;
         RTriple 107 0 true];
     add_rel [::3;2;1;3] [::2;3;2;1]
     [:: RTriple 4 2 true;
         RTriple 107 0 true];
     add_rel [::4;0;1] [::1;4;0]
     [:: RTriple 6 1 true;
         RTriple 108 0 true];
     add_rel [::4;0;2;0] [::2;4;0;2]
     [:: RTriple 9 1 true;
         RTriple 109 0 true];
     add_rel [::4;0;2;7] [::8]
     [:: RTriple 20 3 false;
         RTriple 99 4 false;
         RTriple 100 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::4;0;2;4] [::7;2]
     [:: RTriple 10 2 true;
         RTriple 98 0 true];
     add_rel [::4;0;3] [::3;4;0]
     [:: RTriple 5 1 true;
         RTriple 110 0 true];
     add_rel [::4;0;5] [::7]
     [:: RTriple 95 2 false;
         RTriple 98 0 true;
         RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::4;0;6] [::5;0]
     [:: RTriple 17 1 true;
         RTriple 95 0 true];
     add_rel [::5;0;2;0] [::2;5;0;2]
     [:: RTriple 9 1 true;
         RTriple 111 0 true];
     add_rel [::5;0;2;1;6] [::8]
     [:: RTriple 94 0 false;
         RTriple 100 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;3] [::3;5;0]
     [:: RTriple 5 1 true;
         RTriple 112 0 true];
     add_rel [::5;0;4] [::7]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 98 1 true;
         RTriple 52 0 true];
     add_rel [::5;1;2;0;4] [::8]
     [:: RTriple 95 0 false;
         RTriple 101 1 true;
         RTriple 44 0 true];
     add_rel [::5;1;2;1] [::2;5;1;2]
     [:: RTriple 7 1 true;
         RTriple 111 0 true];
     add_rel [::5;1;3] [::3;5;1]
     [:: RTriple 4 1 true;
         RTriple 112 0 true];
     add_rel [::5;1;4] [::5;1]
     [:: RTriple 18 1 true;
         RTriple 47 0 true;
         RTriple 40 0 true];
     add_rel [::5;1;6] [::7]
     [:: RTriple 95 0 false;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::5;6] [::5]
     [:: RTriple 94 0 false;
         RTriple 95 1 true;
         RTriple 40 1 false;
         RTriple 94 0 true;
         RTriple 50 0 true];
     add_rel [::6;1;2;0;3;4] [::8;3]
     [:: RTriple 13 4 true;
         RTriple 101 0 true];
     add_rel [::6;1;2;0;5] [::8]
     [:: RTriple 95 4 false;
         RTriple 101 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::6;1;2;7] [::8]
     [:: RTriple 22 3 false;
         RTriple 42 4 false;
         RTriple 101 0 true;
         RTriple 73 0 true;
         RTriple 64 0 true];
     add_rel [::6;1;2;6] [::7;2]
     [:: RTriple 12 2 true;
         RTriple 99 0 true];
     add_rel [::7;2;1;6] [::8]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 100 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;4] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::4;0;2;1;3;6] [::8;3]
     [:: RTriple 16 4 true;
         RTriple 100 0 true];
     add_rel [::4;0;2;1;5] [::8]
     [:: RTriple 94 4 false;
         RTriple 100 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::6;1;2;1] [::2;6;1;2]
     [:: RTriple 7 1 true;
         RTriple 114 0 true];
     add_rel [::6;1;3] [::3;6;1]
     [:: RTriple 4 1 true;
         RTriple 115 0 true];
     add_rel [::6;1;4] [::5;1]
     [:: RTriple 18 1 true;
         RTriple 94 0 true];
     add_rel [::6;1;5] [::7]
     [:: RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::6;5] [::5]
     [:: RTriple 40 1 false;
         RTriple 94 0 true;
         RTriple 50 0 true];
     add_rel [::7;2;3;2] [::3;7;2;3]
     [:: RTriple 8 1 true;
         RTriple 118 0 true];
     add_rel [::7;2;3;7] [::8;3]
     [:: RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;4] [::7;2]
     [:: RTriple 10 1 true;
         RTriple 58 0 true];
     add_rel [::7;2;5] [::7;2]
     [:: RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;6] [::7;2]
     [:: RTriple 12 1 true;
         RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::8;3;4] [::8;3]
     [:: RTriple 13 1 true;
         RTriple 70 0 true];
     add_rel [::8;3;5] [::8;3]
     [:: RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::8;3;6] [::8;3]
     [:: RTriple 16 1 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::8;3;7] [::8;3]
     [:: RTriple 15 1 true;
         RTriple 74 0 true];
     add_rel [::0;2;0;1;2;3;7] [::2;0;1;2;3;7]
     [:: RTriple 9 0 true;
         RTriple 104 2 true;
         RTriple 15 5 true;
         RTriple 20 4 true;
         RTriple 118 4 true];
     add_rel [::0;2;0;1;2;3;8] [::2;0;1;2;3;8]
     [:: RTriple 9 0 true;
         RTriple 104 2 true;
         RTriple 4 4 true;
         RTriple 24 5 true];
     add_rel [::0;2;0;1;2;7] [::2;0;1;2;7]
     [:: RTriple 9 0 true;
         RTriple 104 2 true;
         RTriple 20 4 true];
     add_rel [::1;2;0;1;2;3;7] [::2;0;1;2;3;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 103 2 true;
         RTriple 102 1 true;
         RTriple 15 5 true;
         RTriple 22 4 true;
         RTriple 118 4 true];
     add_rel [::1;2;0;1;2;3;8] [::2;0;1;2;3;8]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 103 2 true;
         RTriple 102 1 true;
         RTriple 5 4 true;
         RTriple 26 5 true];
     add_rel [::1;2;0;1;2;7] [::2;0;1;2;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 103 2 true;
         RTriple 102 1 true;
         RTriple 22 4 true];
     add_rel [::3;2;0;1;3] [::2;3;2;0;1]
     [:: RTriple 6 2 true;
         RTriple 5 3 true;
         RTriple 4 2 true;
         RTriple 107 0 true;
         RTriple 102 3 true];
     add_rel [::4;0;2;1;4] [::7;2;1]
     [:: RTriple 18 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true];
     add_rel [::4;0;2;3;2] [::3;4;0;2;3]
     [:: RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 110 0 true];
     add_rel [::4;0;2;3;4] [::7;2;3]
     [:: RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true];
     add_rel [::4;0;2;3;7] [::8;3]
     [:: RTriple 15 3 true;
         RTriple 20 3 false;
         RTriple 99 4 false;
         RTriple 100 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::4;0;2;5] [::7;2]
     [:: RTriple 40 3 false;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;0;6] [::7;2;0]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 40 3 false;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::4;0;2;6] [::5;0;2]
     [:: RTriple 12 2 true;
         RTriple 17 1 true;
         RTriple 95 0 true];
     add_rel [::5;0;1;2;0;1;2] [::2;5;0;1;2;0;1]
     [:: RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 103 4 true;
         RTriple 102 3 true;
         RTriple 9 1 true;
         RTriple 111 0 true;
         RTriple 104 3 true;
         RTriple 102 5 true];
     add_rel [::5;0;1;2;0;4] [::8]
     [:: RTriple 95 0 false;
         RTriple 6 2 true;
         RTriple 9 3 true;
         RTriple 10 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::5;0;1;6] [::7]
     [:: RTriple 95 0 false;
         RTriple 6 2 true;
         RTriple 17 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::5;0;2;4] [::7;2]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 52 0 true];
     add_rel [::5;0;2;7] [::8]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 20 4 false;
         RTriple 99 5 false;
         RTriple 100 1 true;
         RTriple 23 1 false;
         RTriple 24 1 true;
         RTriple 79 1 false;
         RTriple 80 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;5] [::7]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 40 3 false;
         RTriple 98 1 true;
         RTriple 52 0 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::5;0;6] [::5;0]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::7;2;0;1;6] [::8]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 6 4 true;
         RTriple 17 5 true;
         RTriple 100 1 true;
         RTriple 64 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true];
     add_rel [::7;2;0;5] [::8]
     [:: RTriple 68 0 false;
         RTriple 20 1 false;
         RTriple 19 1 true;
         RTriple 67 0 true;
         RTriple 95 5 false;
         RTriple 101 1 true;
         RTriple 79 1 false;
         RTriple 80 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;1;3] [::3;5;0;1]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 5 3 true;
         RTriple 110 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true;
         RTriple 18 2 true;
         RTriple 94 1 true;
         RTriple 102 2 true];
     add_rel [::5;0;1;4] [::7]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 98 2 true;
         RTriple 20 1 true;
         RTriple 68 0 true];
     add_rel [::5;0;1;2;1;6] [::8]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;1;3;6] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;1;5] [::8]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 94 5 false;
         RTriple 100 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;2;3;2] [::3;5;0;2;3]
     [:: RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 112 0 true];
     add_rel [::5;0;1;2;4] [::7;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 10 4 true;
         RTriple 98 2 true;
         RTriple 20 1 true;
         RTriple 68 0 true];
     add_rel [::5;0;1;2;7] [::8]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;5] [::7]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 94 4 false;
         RTriple 99 2 true;
         RTriple 57 2 true;
         RTriple 42 2 true;
         RTriple 22 1 true;
         RTriple 42 0 true];
     add_rel [::5;1;2;0;1] [::2;5;1;2;0]
     [:: RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 111 0 true];
     add_rel [::5;1;2;0;3;4] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true];
     add_rel [::5;1;2;0;5] [::8]
     [:: RTriple 95 0 false;
         RTriple 40 5 false;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;7] [::8]
     [:: RTriple 95 0 false;
         RTriple 22 4 false;
         RTriple 42 5 false;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 73 0 true;
         RTriple 64 0 true];
     add_rel [::5;1;2;3;2] [::3;5;1;2;3]
     [:: RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 112 0 true];
     add_rel [::5;0;1;2;0;1;4] [::8]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 18 6 true;
         RTriple 101 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;3;4] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 13 6 true;
         RTriple 101 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;5] [::8]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 95 6 false;
         RTriple 101 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;1;2;4] [::5;1;2]
     [:: RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 47 0 true;
         RTriple 40 0 true];
     add_rel [::5;1;2;6] [::7;2]
     [:: RTriple 95 0 false;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::5;1;5] [::7]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 40 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::6;1;2;0;3;2;4] [::8;3;2]
     [:: RTriple 10 5 true;
         RTriple 13 4 true;
         RTriple 101 0 true];
     add_rel [::6;1;2;0;3;5] [::8;3]
     [:: RTriple 14 4 true;
         RTriple 95 4 false;
         RTriple 101 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::6;1;2;3;7] [::8;3]
     [:: RTriple 15 3 true;
         RTriple 22 3 false;
         RTriple 98 4 false;
         RTriple 101 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 70 0 true];
     add_rel [::8;3;2;4] [::8;3;2]
     [:: RTriple 10 2 true;
         RTriple 13 1 true;
         RTriple 70 0 true];
     add_rel [::8;3;2;7] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;4] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 18 6 true;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true];
     add_rel [::7;2;0;3;4] [::8;3]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 13 6 true;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::8;3;2;1;6] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 100 2 true;
         RTriple 97 0 true];
     add_rel [::6;1;2;3;8] [::9]
     [:: RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true];
     add_rel [::4;0;2;1;3;2;6] [::8;3;2]
     [:: RTriple 12 5 true;
         RTriple 16 4 true;
         RTriple 100 0 true];
     add_rel [::4;0;2;1;3;5] [::8;3]
     [:: RTriple 14 4 true;
         RTriple 94 4 false;
         RTriple 100 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::8;3;2;6] [::8;3;2]
     [:: RTriple 74 0 false;
         RTriple 118 1 true;
         RTriple 12 3 true;
         RTriple 67 2 false;
         RTriple 68 2 true;
         RTriple 15 1 true;
         RTriple 74 0 true];
     add_rel [::4;0;2;3;8] [::9]
     [:: RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;6] [::7;2]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 12 4 true;
         RTriple 99 2 true;
         RTriple 22 1 true;
         RTriple 42 0 true];
     add_rel [::5;0;1;2;1;3;6] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 16 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::6;1;2;0;6] [::7;2;0]
     [:: RTriple 17 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true];
     add_rel [::6;1;2;3;6] [::7;2;3]
     [:: RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true];
     add_rel [::6;1;2;5] [::7;2]
     [:: RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::7;2;1;3;6] [::8;3]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;3;6] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 16 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;3;4] [::8;3]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 114 1 true;
         RTriple 13 6 true;
         RTriple 101 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;5] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 94 7 false;
         RTriple 100 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;1;5] [::8]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 94 5 false;
         RTriple 100 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 64 0 true];
     add_rel [::8;3;2;0;1;4] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 100 0 false;
         RTriple 4 5 true;
         RTriple 115 4 true;
         RTriple 18 9 true;
         RTriple 101 5 true;
         RTriple 23 5 false;
         RTriple 24 5 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::8;3;2;0;4] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 4 2 true;
         RTriple 112 1 true;
         RTriple 95 2 false;
         RTriple 101 3 true;
         RTriple 44 2 true;
         RTriple 97 0 true];
     add_rel [::8;3;2;0;5] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 100 0 false;
         RTriple 4 5 true;
         RTriple 115 4 true;
         RTriple 95 9 false;
         RTriple 101 5 true;
         RTriple 79 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;1;5] [::8]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 94 6 false;
         RTriple 100 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::6;1;2;0;1] [::2;6;1;2;0]
     [:: RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 114 0 true];
     add_rel [::6;1;2;3;2] [::3;6;1;2;3]
     [:: RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true];
     add_rel [::6;1;2;4] [::5;1;2]
     [:: RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 94 0 true];
     add_rel [::7;2;1;4] [::7;2;1]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 18 3 true;
         RTriple 94 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::8;3;2;1;5] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 94 6 false;
         RTriple 100 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;3;2;0] [::3;7;2;0;3;2]
     [:: RTriple 5 2 true;
         RTriple 9 3 true;
         RTriple 8 1 true;
         RTriple 118 0 true;
         RTriple 105 3 true];
     add_rel [::7;2;1;3;2;1] [::3;7;2;1;3;2]
     [:: RTriple 4 2 true;
         RTriple 7 3 true;
         RTriple 8 1 true;
         RTriple 118 0 true;
         RTriple 106 3 true];
     add_rel [::7;2;3;4] [::7;2;3]
     [:: RTriple 13 2 true;
         RTriple 10 1 true;
         RTriple 58 0 true];
     add_rel [::8;3;2;5] [::8;3;2]
     [:: RTriple 11 2 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::7;2;3;8] [::9]
     [:: RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;3;5] [::7;2;3]
     [:: RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;3;6] [::7;2;3]
     [:: RTriple 16 2 true;
         RTriple 12 1 true;
         RTriple 67 0 false;
         RTriple 68 0 true];
     add_rel [::0;3;2;0;1;2;3;7] [::3;2;0;1;2;3;7]
     [:: RTriple 5 0 true;
         RTriple 9 1 true;
         RTriple 104 3 true;
         RTriple 15 6 true;
         RTriple 20 5 true;
         RTriple 118 5 true];
     add_rel [::0;3;2;0;1;2;3;8] [::3;2;0;1;2;3;8]
     [:: RTriple 5 0 true;
         RTriple 9 1 true;
         RTriple 104 3 true;
         RTriple 4 5 true;
         RTriple 24 6 true];
     add_rel [::0;3;2;0;1;2;7] [::3;2;0;1;2;7]
     [:: RTriple 5 0 true;
         RTriple 9 1 true;
         RTriple 104 3 true;
         RTriple 20 5 true];
     add_rel [::1;3;2;0;1;2;3;7] [::3;2;0;1;2;3;7]
     [:: RTriple 4 0 true;
         RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 103 3 true;
         RTriple 102 2 true;
         RTriple 15 6 true;
         RTriple 22 5 true;
         RTriple 118 5 true];
     add_rel [::1;3;2;0;1;2;3;8] [::3;2;0;1;2;3;8]
     [:: RTriple 4 0 true;
         RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 103 3 true;
         RTriple 102 2 true;
         RTriple 5 5 true;
         RTriple 26 6 true];
     add_rel [::1;3;2;0;1;2;7] [::3;2;0;1;2;7]
     [:: RTriple 4 0 true;
         RTriple 6 3 true;
         RTriple 7 1 true;
         RTriple 103 3 true;
         RTriple 102 2 true;
         RTriple 22 5 true];
     add_rel [::3;2;0;1;2;3;2] [::2;3;2;0;1;2;3]
     [:: RTriple 6 2 true;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 4 2 true;
         RTriple 107 0 true;
         RTriple 102 3 true];
     add_rel [::5;0;1;2;1;4] [::7;2;1]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 94 3 true;
         RTriple 40 3 false;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 104 1 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::7;2;0;1;2;3;6] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;2;4] [::8]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 6 4 true;
         RTriple 7 2 true;
         RTriple 111 1 true;
         RTriple 95 2 false;
         RTriple 10 7 true;
         RTriple 101 3 true;
         RTriple 44 2 true;
         RTriple 31 2 false;
         RTriple 32 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;5] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 9 2 true;
         RTriple 111 1 true;
         RTriple 94 2 false;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 24 3 true;
         RTriple 80 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::8;3;2;1;4] [::8;3;2;1]
     [:: RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 112 1 true;
         RTriple 111 2 true;
         RTriple 18 4 true;
         RTriple 47 3 true;
         RTriple 40 3 true;
         RTriple 11 2 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::4;0;2;1;3;4] [::7;2;1;3]
     [:: RTriple 4 3 true;
         RTriple 18 4 true;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 106 2 true];
     add_rel [::4;0;2;1;3;2;1] [::3;4;0;2;1;3;2]
     [:: RTriple 4 3 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 110 0 true;
         RTriple 106 4 true];
     add_rel [::4;0;2;3;5] [::7;2;3]
     [:: RTriple 40 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::7;2;0;3;6] [::7;2;0;3]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 40 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 105 2 true];
     add_rel [::5;0;2;1;4] [::7;2;1]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 18 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 52 0 true];
     add_rel [::5;0;2;3;4] [::7;2;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 52 0 true];
     add_rel [::5;0;1;2;3;4] [::7;2;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 13 5 true;
         RTriple 10 4 true;
         RTriple 98 2 true;
         RTriple 20 1 true;
         RTriple 68 0 true];
     add_rel [::5;0;1;2;3;7] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 15 5 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;3;2] [::3;5;0;1;2;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 110 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true;
         RTriple 18 2 true;
         RTriple 94 1 true;
         RTriple 102 2 true];
     add_rel [::7;2;0;1;2;6] [::8]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 9 2 true;
         RTriple 111 1 true;
         RTriple 94 2 false;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 100 4 true;
         RTriple 24 3 true;
         RTriple 80 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;4] [::8;3]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 13 7 true;
         RTriple 10 6 true;
         RTriple 98 4 true;
         RTriple 99 4 false;
         RTriple 100 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::7;2;0;1;2;3;7] [::8;3]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 15 7 true;
         RTriple 20 7 false;
         RTriple 99 8 false;
         RTriple 100 4 true;
         RTriple 23 4 false;
         RTriple 24 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;2;7] [::8]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 94 2 false;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 20 7 false;
         RTriple 99 8 false;
         RTriple 100 4 true;
         RTriple 23 4 false;
         RTriple 24 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 3 true;
         RTriple 80 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;3;2;1;6] [::9]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 100 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 18 7 true;
         RTriple 10 6 true;
         RTriple 98 4 true;
         RTriple 15 3 true;
         RTriple 20 3 false;
         RTriple 99 4 false;
         RTriple 100 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::7;2;0;3;2;1;5] [::9]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;3;2;4] [::8;3;2]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 99 0 false;
         RTriple 10 7 true;
         RTriple 13 6 true;
         RTriple 101 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::7;2;0;3;2;7] [::9]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 20 7 false;
         RTriple 99 8 false;
         RTriple 100 4 true;
         RTriple 23 4 false;
         RTriple 24 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;3;5] [::8;3]
     [:: RTriple 68 0 false;
         RTriple 20 1 false;
         RTriple 19 1 true;
         RTriple 67 0 true;
         RTriple 14 5 true;
         RTriple 95 5 false;
         RTriple 101 1 true;
         RTriple 79 1 false;
         RTriple 80 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 12 6 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 40 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 105 2 true];
     add_rel [::4;0;2;3;6] [::5;0;2;3]
     [:: RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 17 1 true;
         RTriple 95 0 true];
     add_rel [::8;3;2;0;6] [::8;3;2;0]
     [:: RTriple 70 0 false;
         RTriple 110 1 true;
         RTriple 109 2 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 11 2 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;2;0;1;3;4] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 13 7 true;
         RTriple 101 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;1;5] [::8]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 94 7 false;
         RTriple 100 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;3;7] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 15 4 true;
         RTriple 20 4 false;
         RTriple 99 5 false;
         RTriple 100 1 true;
         RTriple 80 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::5;0;2;5] [::7;2]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 40 4 false;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 52 0 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::5;0;2;6] [::5;0;2]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 12 3 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::5;0;1;2;5] [::7;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 40 5 false;
         RTriple 10 4 true;
         RTriple 98 2 true;
         RTriple 11 3 true;
         RTriple 59 2 true;
         RTriple 52 2 true;
         RTriple 20 1 true;
         RTriple 68 0 true];
     add_rel [::7;2;0;3;2;5] [::8;3;2]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 40 7 false;
         RTriple 10 6 true;
         RTriple 98 4 true;
         RTriple 11 5 true;
         RTriple 59 4 true;
         RTriple 52 4 true;
         RTriple 15 3 true;
         RTriple 20 3 false;
         RTriple 99 4 false;
         RTriple 100 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::8;3;2;0;1;6] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 5 2 true;
         RTriple 112 1 true;
         RTriple 9 3 true;
         RTriple 111 2 true;
         RTriple 94 3 false;
         RTriple 100 4 true;
         RTriple 80 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;0;1;6] [::8]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;1;3;2;6] [::8;3;2]
     [:: RTriple 94 0 false;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;2;1;3;5] [::8;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 14 5 true;
         RTriple 94 5 false;
         RTriple 100 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;2;3;8] [::9]
     [:: RTriple 94 0 false;
         RTriple 24 5 false;
         RTriple 106 4 true;
         RTriple 80 6 false;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 80 0 true;
         RTriple 97 0 true];
     add_rel [::5;0;2;1;3;2;1] [::3;5;0;2;1;3;2]
     [:: RTriple 4 3 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 112 0 true;
         RTriple 106 4 true];
     add_rel [::5;1;2;3;7] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 15 4 true;
         RTriple 22 4 false;
         RTriple 98 5 false;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 70 0 true];
     add_rel [::5;1;2;3;8] [::9]
     [:: RTriple 95 0 false;
         RTriple 26 5 false;
         RTriple 105 4 true;
         RTriple 44 6 false;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 97 0 true];
     add_rel [::5;1;2;0;3;2;4] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true];
     add_rel [::5;1;2;0;3;5] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 40 6 false;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;2;0;3;2;4] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 10 7 true;
         RTriple 13 6 true;
         RTriple 101 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;3;5] [::8;3]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 14 6 true;
         RTriple 95 6 false;
         RTriple 101 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;3;8] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 24 6 false;
         RTriple 106 5 true;
         RTriple 80 7 false;
         RTriple 16 6 true;
         RTriple 100 2 true;
         RTriple 97 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true];
     add_rel [::5;1;2;0;3;2;0] [::3;5;1;2;0;3;2]
     [:: RTriple 5 3 true;
         RTriple 9 4 true;
         RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 112 0 true;
         RTriple 105 4 true];
     add_rel [::5;0;1;2;0;1;3;6] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 16 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;1;2;0;6] [::7;2;0]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;1;2;3;4] [::5;1;2;3]
     [:: RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 47 0 true;
         RTriple 40 0 true];
     add_rel [::5;1;2;3;6] [::7;2;3]
     [:: RTriple 95 0 false;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 99 1 true;
         RTriple 42 0 true];
     add_rel [::5;1;2;5] [::7;2]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 40 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;0;1;2;0;6] [::7;2;0]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 12 5 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 103 1 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::5;0;1;2;0;1;3;2;4] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 101 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;1;3;5] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 14 7 true;
         RTriple 94 7 false;
         RTriple 100 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::6;1;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 18 6 true;
         RTriple 10 5 true;
         RTriple 13 4 true;
         RTriple 101 0 true];
     add_rel [::6;1;2;0;3;2;5] [::8;3;2]
     [:: RTriple 11 5 true;
         RTriple 14 4 true;
         RTriple 95 4 false;
         RTriple 101 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true];
     add_rel [::6;1;2;0;3;2;7] [::9]
     [:: RTriple 42 6 false;
         RTriple 10 5 true;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;2;3;2;4] [::8;3;2]
     [:: RTriple 20 0 false;
         RTriple 19 0 true;
         RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 98 0 false;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 111 3 true;
         RTriple 109 2 true;
         RTriple 40 3 true;
         RTriple 95 3 false;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 103 4 true;
         RTriple 102 3 true;
         RTriple 113 2 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 101 3 true;
         RTriple 26 2 true;
         RTriple 32 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;5] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 14 8 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;3;2;4] [::8;3;2]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 10 7 true;
         RTriple 98 5 true;
         RTriple 20 4 true;
         RTriple 68 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;0;1;3;5] [::8;3]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 14 7 true;
         RTriple 94 7 false;
         RTriple 100 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::8;3;2;0;1;5] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 5 2 true;
         RTriple 112 1 true;
         RTriple 9 3 true;
         RTriple 111 2 true;
         RTriple 40 3 false;
         RTriple 39 3 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 54 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true];
     add_rel [::4;0;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 17 6 true;
         RTriple 12 5 true;
         RTriple 16 4 true;
         RTriple 100 0 true];
     add_rel [::4;0;2;1;3;2;5] [::8;3;2]
     [:: RTriple 11 5 true;
         RTriple 14 4 true;
         RTriple 94 4 false;
         RTriple 100 0 true;
         RTriple 69 0 true;
         RTriple 44 0 true];
     add_rel [::4;0;2;1;3;2;7] [::9]
     [:: RTriple 68 6 false;
         RTriple 12 5 true;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;1;3;2;6] [::8;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 12 7 true;
         RTriple 16 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;0;1;3;2;6] [::8;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::7;2;1;3;2;6] [::8;3;2]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 64 0 true];
     add_rel [::7;2;0;1;2;3;8] [::9]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 24 8 false;
         RTriple 106 7 true;
         RTriple 80 9 false;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 97 4 true;
         RTriple 28 3 true;
         RTriple 34 2 true;
         RTriple 30 1 true;
         RTriple 46 0 true];
     add_rel [::7;2;0;1;3;2;6] [::8;3;2]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;2;3;2;6] [::8;3;2]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 12 9 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;3;2;1;6] [::9]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 4 6 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 12 9 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::8;3;2;0;1;2;6] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 5 2 true;
         RTriple 112 1 true;
         RTriple 9 3 true;
         RTriple 111 2 true;
         RTriple 94 3 false;
         RTriple 104 6 true;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 100 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true];
     add_rel [::8;3;2;0;1;2;4] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 4 2 true;
         RTriple 112 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 111 2 true;
         RTriple 95 3 false;
         RTriple 10 8 true;
         RTriple 101 4 true;
         RTriple 44 3 true;
         RTriple 31 3 false;
         RTriple 32 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;1;3;5] [::8;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 14 6 true;
         RTriple 94 6 false;
         RTriple 100 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::7;2;1;3;5] [::8;3]
     [:: RTriple 42 0 false;
         RTriple 22 1 false;
         RTriple 21 1 true;
         RTriple 41 0 true;
         RTriple 14 5 true;
         RTriple 94 5 false;
         RTriple 100 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 64 0 true];
     add_rel [::5;0;1;2;3;6] [::7;2;3]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 16 5 true;
         RTriple 12 4 true;
         RTriple 99 2 true;
         RTriple 22 1 true;
         RTriple 42 0 true];
     add_rel [::6;1;2;0;3;6] [::7;2;0;3]
     [:: RTriple 5 3 true;
         RTriple 17 4 true;
         RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true;
         RTriple 105 2 true];
     add_rel [::6;1;2;3;5] [::7;2;3]
     [:: RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::7;2;1;3;4] [::7;2;1;3]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 18 4 true;
         RTriple 94 3 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 106 2 true];
     add_rel [::7;2;0;1;3;2;0;4] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 6 5 true;
         RTriple 9 6 true;
         RTriple 10 8 true;
         RTriple 101 4 true;
         RTriple 44 3 true;
         RTriple 31 3 false;
         RTriple 32 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;1;3;2;0;4] [::9]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 101 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;1;3;2;0;5] [::9]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 95 7 false;
         RTriple 101 3 true;
         RTriple 79 3 false;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 17 6 true;
         RTriple 12 5 true;
         RTriple 99 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;1;3;2;7] [::9]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 22 6 false;
         RTriple 42 7 false;
         RTriple 101 3 true;
         RTriple 73 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;1;3;2;5] [::8;3;2]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 11 5 true;
         RTriple 94 5 false;
         RTriple 99 3 true;
         RTriple 57 3 true;
         RTriple 42 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;1;3;2;0;1] [::3;7;2;1;3;2;0]
     [:: RTriple 4 2 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 8 1 true;
         RTriple 118 0 true;
         RTriple 106 3 true];
     add_rel [::6;1;2;0;3;2;0] [::3;6;1;2;0;3;2]
     [:: RTriple 5 3 true;
         RTriple 9 4 true;
         RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true;
         RTriple 105 4 true];
     add_rel [::6;1;2;3;4] [::5;1;2;3]
     [:: RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 18 1 true;
         RTriple 94 0 true];
     add_rel [::7;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 68 0 false;
         RTriple 67 0 true;
         RTriple 114 1 true;
         RTriple 4 3 true;
         RTriple 115 2 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 94 3 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 106 2 true];
     add_rel [::7;2;0;1;3;2;0;1;2] [::3;7;2;0;1;3;2;0;1]
     [:: RTriple 4 3 true;
         RTriple 5 2 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 103 6 true;
         RTriple 102 5 true;
         RTriple 9 3 true;
         RTriple 8 1 true;
         RTriple 118 0 true;
         RTriple 105 3 true;
         RTriple 104 5 true;
         RTriple 106 4 true;
         RTriple 102 7 true];
     add_rel [::8;3;2;0;1;2;3;4] [::9]
     [:: RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 4 2 true;
         RTriple 112 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 111 2 true;
         RTriple 95 3 false;
         RTriple 103 6 true;
         RTriple 102 5 true;
         RTriple 113 4 true;
         RTriple 13 9 true;
         RTriple 101 5 true;
         RTriple 26 4 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::8;3;2;0;1;2;5] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 5 2 true;
         RTriple 112 1 true;
         RTriple 9 3 true;
         RTriple 111 2 true;
         RTriple 94 3 false;
         RTriple 104 6 true;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 94 9 false;
         RTriple 100 5 true;
         RTriple 69 5 true;
         RTriple 44 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true];
     add_rel [::8;3;2;0;1;2;3;6] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 5 2 true;
         RTriple 112 1 true;
         RTriple 9 3 true;
         RTriple 111 2 true;
         RTriple 94 3 false;
         RTriple 104 6 true;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 16 9 true;
         RTriple 100 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::8;3;2;0;1;2;7] [::9]
     [:: RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 112 1 true;
         RTriple 111 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 20 8 false;
         RTriple 99 9 false;
         RTriple 100 5 true;
         RTriple 23 5 false;
         RTriple 24 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;3;2;0;1;4] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 113 4 true;
         RTriple 18 9 true;
         RTriple 101 5 true;
         RTriple 23 5 false;
         RTriple 24 5 true;
         RTriple 26 4 true;
         RTriple 44 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;2;3;2;0;4] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 113 4 true;
         RTriple 105 8 true;
         RTriple 13 9 true;
         RTriple 101 5 true;
         RTriple 26 4 true;
         RTriple 44 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;3;2;0;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 113 4 true;
         RTriple 95 9 false;
         RTriple 101 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 26 4 true;
         RTriple 44 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;2;3;2;1;6] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 106 8 true;
         RTriple 16 9 true;
         RTriple 100 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;3;2;1;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 94 9 false;
         RTriple 100 5 true;
         RTriple 69 5 true;
         RTriple 44 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;3;2;7] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 20 8 false;
         RTriple 99 9 false;
         RTriple 100 5 true;
         RTriple 23 5 false;
         RTriple 24 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::1;2;0;1;2;3;2;0;1;2;3;7] [::2;0;1;2;3;2;0;1;2;3;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 103 2 true;
         RTriple 102 1 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 104 7 true;
         RTriple 15 10 true;
         RTriple 20 9 true;
         RTriple 118 9 true];
     add_rel [::0;2;0;1;2;3;2;0;1;2;3;7] [::2;0;1;2;3;2;0;1;2;3;7]
     [:: RTriple 9 0 true;
         RTriple 104 2 true;
         RTriple 4 4 true;
         RTriple 6 7 true;
         RTriple 7 5 true;
         RTriple 103 7 true;
         RTriple 102 6 true;
         RTriple 15 10 true;
         RTriple 22 9 true;
         RTriple 118 9 true];
     add_rel [::1;2;0;1;2;3;2;0;1;2;7] [::2;0;1;2;3;2;0;1;2;7]
     [:: RTriple 6 2 true;
         RTriple 7 0 true;
         RTriple 103 2 true;
         RTriple 102 1 true;
         RTriple 5 4 true;
         RTriple 9 5 true;
         RTriple 104 7 true;
         RTriple 20 9 true];
     add_rel [::0;2;0;1;2;3;2;0;1;2;7] [::2;0;1;2;3;2;0;1;2;7]
     [:: RTriple 9 0 true;
         RTriple 104 2 true;
         RTriple 4 4 true;
         RTriple 6 7 true;
         RTriple 7 5 true;
         RTriple 103 7 true;
         RTriple 102 6 true;
         RTriple 22 9 true];
     add_rel [::2;3;2;0;1;2;3;8] [::3;2;0;1;2;3;8]
     [:: RTriple 8 0 true;
         RTriple 6 3 true;
         RTriple 106 2 true;
         RTriple 105 3 true;
         RTriple 102 2 true;
         RTriple 107 4 true;
         RTriple 32 6 true];
     add_rel [::5;0;1;2;1;3;4] [::7;2;1;3]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 13 6 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 94 3 true;
         RTriple 40 3 false;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 104 1 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::7;2;0;1;3;2;1;4] [::8;3;2;1]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 113 4 true;
         RTriple 7 6 true;
         RTriple 114 5 true;
         RTriple 10 8 true;
         RTriple 18 7 true;
         RTriple 94 6 true;
         RTriple 40 6 false;
         RTriple 10 5 true;
         RTriple 98 3 true;
         RTriple 11 4 true;
         RTriple 59 3 true;
         RTriple 52 3 true;
         RTriple 104 4 true;
         RTriple 19 3 false;
         RTriple 20 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;0;1;2;3;2;1;4] [::8;3;2;1]
     [:: RTriple 98 0 false;
         RTriple 109 2 true;
         RTriple 6 4 true;
         RTriple 8 6 true;
         RTriple 5 5 true;
         RTriple 4 4 true;
         RTriple 110 3 true;
         RTriple 108 4 true;
         RTriple 106 3 true;
         RTriple 18 9 true;
         RTriple 13 8 true;
         RTriple 10 7 true;
         RTriple 98 5 true;
         RTriple 15 4 true;
         RTriple 99 4 false;
         RTriple 100 0 true;
         RTriple 23 0 false;
         RTriple 24 0 true;
         RTriple 79 0 false;
         RTriple 80 0 true;
         RTriple 107 1 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::7;2;0;1;2;3;2;1;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 106 8 true;
         RTriple 14 9 true;
         RTriple 94 9 false;
         RTriple 100 5 true;
         RTriple 69 5 true;
         RTriple 44 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;3;2;5] [::8;3;2]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 11 8 true;
         RTriple 14 7 true;
         RTriple 94 7 false;
         RTriple 100 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::8;3;2;0;1;2;3;5] [::9]
     [:: RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 5 2 true;
         RTriple 112 1 true;
         RTriple 9 3 true;
         RTriple 111 2 true;
         RTriple 94 3 false;
         RTriple 104 6 true;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 14 9 true;
         RTriple 94 9 false;
         RTriple 100 5 true;
         RTriple 69 5 true;
         RTriple 44 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::8;3;2;0;1;2;3;7] [::9]
     [:: RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 112 1 true;
         RTriple 111 2 true;
         RTriple 40 3 false;
         RTriple 39 3 true;
         RTriple 11 2 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 15 7 true;
         RTriple 20 7 false;
         RTriple 99 8 false;
         RTriple 100 4 true;
         RTriple 23 4 false;
         RTriple 24 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::8;3;2;0;1;2;3;8] [::9]
     [:: RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 112 1 true;
         RTriple 111 2 true;
         RTriple 40 3 false;
         RTriple 39 3 true;
         RTriple 11 2 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 24 8 false;
         RTriple 106 7 true;
         RTriple 80 9 false;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 97 4 true;
         RTriple 28 3 true;
         RTriple 34 2 true;
         RTriple 36 1 true;
         RTriple 78 0 true];
     add_rel [::4;0;2;1;3;2;0;1] [::3;4;0;2;1;3;2;0]
     [:: RTriple 4 3 true;
         RTriple 6 6 true;
         RTriple 7 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 110 0 true;
         RTriple 106 4 true];
     add_rel [::4;0;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 4 3 true;
         RTriple 10 5 true;
         RTriple 18 4 true;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 106 2 true];
     add_rel [::5;0;2;1;3;4] [::7;2;1;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 4 4 true;
         RTriple 18 5 true;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 52 0 true;
         RTriple 106 2 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;2] [::3;5;0;1;2;0;1;3;2;0;1]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 4 6 true;
         RTriple 6 9 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 103 9 true;
         RTriple 102 8 true;
         RTriple 105 7 true;
         RTriple 9 5 true;
         RTriple 109 4 true;
         RTriple 8 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 18 2 true;
         RTriple 94 1 true;
         RTriple 105 4 true;
         RTriple 107 5 true;
         RTriple 103 3 true;
         RTriple 102 2 true;
         RTriple 104 7 true;
         RTriple 106 6 true;
         RTriple 102 9 true];
     add_rel [::7;2;0;1;2;3;2;7] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 15 8 true;
         RTriple 20 8 false;
         RTriple 99 9 false;
         RTriple 100 5 true;
         RTriple 23 5 false;
         RTriple 24 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;2;3;5] [::7;2;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 40 5 false;
         RTriple 13 4 true;
         RTriple 10 3 true;
         RTriple 98 1 true;
         RTriple 52 0 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true];
     add_rel [::5;0;1;2;3;5] [::7;2;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 40 6 false;
         RTriple 13 5 true;
         RTriple 10 4 true;
         RTriple 98 2 true;
         RTriple 14 4 true;
         RTriple 11 3 true;
         RTriple 59 2 true;
         RTriple 52 2 true;
         RTriple 20 1 true;
         RTriple 68 0 true];
     add_rel [::5;0;1;2;1;3;2;1] [::3;5;0;1;2;1;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 4 5 true;
         RTriple 7 6 true;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 110 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true;
         RTriple 18 2 true;
         RTriple 94 1 true;
         RTriple 102 2 true;
         RTriple 106 5 true];
     add_rel [::7;2;0;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 9 6 true;
         RTriple 109 5 true;
         RTriple 12 8 true;
         RTriple 17 7 true;
         RTriple 95 6 true;
         RTriple 11 5 true;
         RTriple 94 5 false;
         RTriple 99 3 true;
         RTriple 57 3 true;
         RTriple 42 3 true;
         RTriple 103 4 true;
         RTriple 21 3 false;
         RTriple 22 3 true;
         RTriple 15 2 true;
         RTriple 96 0 true];
     add_rel [::7;2;0;1;2;3;2;5] [::8;3;2]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 11 9 true;
         RTriple 14 8 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::7;2;0;1;2;3;2;0;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 113 4 true;
         RTriple 105 8 true;
         RTriple 14 9 true;
         RTriple 95 9 false;
         RTriple 101 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 26 4 true;
         RTriple 44 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;0;3;2;0] [::3;5;0;1;2;0;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 5 5 true;
         RTriple 9 6 true;
         RTriple 8 4 true;
         RTriple 5 3 true;
         RTriple 110 2 true;
         RTriple 4 1 true;
         RTriple 115 0 true;
         RTriple 18 2 true;
         RTriple 94 1 true;
         RTriple 102 2 true;
         RTriple 105 5 true];
     add_rel [::5;0;2;1;3;2;0;1] [::3;5;0;2;1;3;2;0]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 114 2 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 6 7 true;
         RTriple 7 5 true;
         RTriple 114 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 110 0 true;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 106 4 true];
     add_rel [::5;0;1;2;0;1;3;2;0;4] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 5 6 true;
         RTriple 9 7 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 105 7 true;
         RTriple 10 9 true;
         RTriple 13 8 true;
         RTriple 101 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;1;3;2;0;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 105 7 true;
         RTriple 14 8 true;
         RTriple 95 8 false;
         RTriple 101 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 94 0 false;
         RTriple 17 7 true;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;1;3;2;7] [::9]
     [:: RTriple 94 0 false;
         RTriple 7 3 true;
         RTriple 8 5 true;
         RTriple 15 7 true;
         RTriple 99 7 false;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 80 0 true;
         RTriple 115 4 true;
         RTriple 4 3 true;
         RTriple 107 1 true;
         RTriple 31 0 false;
         RTriple 32 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 100 2 true;
         RTriple 97 0 true];
     add_rel [::5;0;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 114 2 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 10 6 true;
         RTriple 18 5 true;
         RTriple 94 4 true;
         RTriple 40 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 106 2 true];
     add_rel [::5;0;2;1;3;2;5] [::8;3;2]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 11 6 true;
         RTriple 14 5 true;
         RTriple 94 5 false;
         RTriple 100 1 true;
         RTriple 69 1 true;
         RTriple 44 1 true;
         RTriple 54 0 true];
     add_rel [::5;0;1;2;0;3;6] [::7;2;0;3]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 16 6 true;
         RTriple 12 5 true;
         RTriple 17 4 true;
         RTriple 95 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 103 1 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;4] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 98 0 false;
         RTriple 111 3 true;
         RTriple 109 2 true;
         RTriple 8 7 true;
         RTriple 4 6 true;
         RTriple 5 5 true;
         RTriple 112 4 true;
         RTriple 110 3 true;
         RTriple 40 4 true;
         RTriple 95 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 113 3 true;
         RTriple 6 8 true;
         RTriple 106 7 true;
         RTriple 7 5 true;
         RTriple 114 4 true;
         RTriple 105 8 true;
         RTriple 10 10 true;
         RTriple 13 9 true;
         RTriple 101 5 true;
         RTriple 32 4 true;
         RTriple 26 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;4] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 95 3 false;
         RTriple 113 4 true;
         RTriple 6 9 true;
         RTriple 106 8 true;
         RTriple 7 6 true;
         RTriple 114 5 true;
         RTriple 105 9 true;
         RTriple 13 10 true;
         RTriple 101 6 true;
         RTriple 32 5 true;
         RTriple 26 4 true;
         RTriple 44 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 6 9 true;
         RTriple 106 8 true;
         RTriple 105 9 true;
         RTriple 102 8 true;
         RTriple 9 6 true;
         RTriple 109 5 true;
         RTriple 14 10 true;
         RTriple 94 10 false;
         RTriple 100 6 true;
         RTriple 69 6 true;
         RTriple 44 6 true;
         RTriple 32 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;3;2;0;1;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 9 6 true;
         RTriple 109 5 true;
         RTriple 94 10 false;
         RTriple 100 6 true;
         RTriple 69 6 true;
         RTriple 44 6 true;
         RTriple 32 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;3;2;0;1;6] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 9 6 true;
         RTriple 109 5 true;
         RTriple 100 6 true;
         RTriple 32 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;1;3;2;0;4] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 105 7 true;
         RTriple 13 8 true;
         RTriple 101 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;2;1;3;2;0;4] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 114 2 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 101 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::5;0;2;1;3;2;0;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 114 2 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 95 8 false;
         RTriple 101 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true];
     add_rel [::5;0;2;1;3;2;7] [::9]
     [:: RTriple 94 0 false;
         RTriple 68 7 false;
         RTriple 12 6 true;
         RTriple 16 5 true;
         RTriple 100 1 true;
         RTriple 80 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 97 0 true];
     add_rel [::5;0;2;3;6] [::5;0;2;3]
     [:: RTriple 40 0 false;
         RTriple 39 0 true;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 50 0 true];
     add_rel [::5;1;2;0;3;2;5] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 40 7 false;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 11 2 true;
         RTriple 14 1 true;
         RTriple 71 0 true;
         RTriple 54 0 true];
     add_rel [::5;1;2;0;3;2;7] [::9]
     [:: RTriple 95 0 false;
         RTriple 42 7 false;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 20 5 false;
         RTriple 99 6 false;
         RTriple 100 2 true;
         RTriple 23 2 false;
         RTriple 24 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 97 0 true];
     add_rel [::5;1;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 95 0 false;
         RTriple 18 7 true;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;3;2;1;4] [::8;3;2;1]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 18 8 true;
         RTriple 13 7 true;
         RTriple 10 6 true;
         RTriple 98 4 true;
         RTriple 15 3 true;
         RTriple 22 3 false;
         RTriple 98 4 false;
         RTriple 101 0 true;
         RTriple 25 0 false;
         RTriple 26 0 true;
         RTriple 70 0 true;
         RTriple 107 1 true;
         RTriple 31 0 false;
         RTriple 32 0 true];
     add_rel [::5;0;1;2;0;3;2;5] [::8;3;2]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 11 7 true;
         RTriple 14 6 true;
         RTriple 95 6 false;
         RTriple 101 2 true;
         RTriple 79 2 false;
         RTriple 80 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;3;2;7] [::9]
     [:: RTriple 95 0 false;
         RTriple 6 2 true;
         RTriple 9 3 true;
         RTriple 8 5 true;
         RTriple 15 7 true;
         RTriple 98 7 false;
         RTriple 10 6 true;
         RTriple 13 5 true;
         RTriple 101 1 true;
         RTriple 44 0 true;
         RTriple 110 4 true;
         RTriple 5 3 true;
         RTriple 107 1 true;
         RTriple 31 0 false;
         RTriple 32 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 4 2 true;
         RTriple 112 1 true;
         RTriple 95 2 false;
         RTriple 101 3 true;
         RTriple 44 2 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;6] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 6 9 true;
         RTriple 106 8 true;
         RTriple 105 9 true;
         RTriple 102 8 true;
         RTriple 9 6 true;
         RTriple 109 5 true;
         RTriple 16 10 true;
         RTriple 100 6 true;
         RTriple 32 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;1;2;0;3;6] [::7;2;0;3]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 105 2 true];
     add_rel [::5;0;1;2;0;1;3;2;1;6] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 4 6 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 12 9 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;0;3;2;1;5] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 14 8 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;0;3;2;1;6] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 36 0 true];
     add_rel [::5;1;2;0;3;2;1;5] [::9]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true];
     add_rel [::5;1;2;0;3;2;1;6] [::9]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 100 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true];
     add_rel [::5;1;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 12 6 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 105 2 true];
     add_rel [::5;0;1;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 16 7 true;
         RTriple 12 6 true;
         RTriple 17 5 true;
         RTriple 95 4 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true;
         RTriple 105 2 true;
         RTriple 107 3 true;
         RTriple 103 1 true;
         RTriple 21 0 false;
         RTriple 22 0 true];
     add_rel [::5;1;2;3;5] [::7;2;3]
     [:: RTriple 94 0 false;
         RTriple 108 1 true;
         RTriple 109 2 true;
         RTriple 110 3 true;
         RTriple 40 4 true;
         RTriple 14 3 true;
         RTriple 11 2 true;
         RTriple 94 2 false;
         RTriple 99 0 true;
         RTriple 57 0 true;
         RTriple 42 0 true];
     add_rel [::5;0;1;2;0;1;3;2;1;4] [::8;3;2;1]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 18 9 true;
         RTriple 10 8 true;
         RTriple 13 7 true;
         RTriple 101 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::5;0;1;2;0;1;3;2;5] [::8;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 11 8 true;
         RTriple 14 7 true;
         RTriple 94 7 false;
         RTriple 100 3 true;
         RTriple 69 3 true;
         RTriple 44 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;0;1;3;2;7] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 68 9 false;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 100 3 true;
         RTriple 26 3 false;
         RTriple 25 3 true;
         RTriple 70 3 false;
         RTriple 5 5 true;
         RTriple 110 4 true;
         RTriple 20 8 false;
         RTriple 99 9 false;
         RTriple 100 5 true;
         RTriple 23 5 false;
         RTriple 24 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 97 3 true;
         RTriple 34 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;4] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 5 6 true;
         RTriple 9 7 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 105 7 true;
         RTriple 18 10 true;
         RTriple 10 9 true;
         RTriple 13 8 true;
         RTriple 101 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 27 2 false;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;5] [::9]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 6 5 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 5 6 true;
         RTriple 9 7 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 105 7 true;
         RTriple 11 9 true;
         RTriple 14 8 true;
         RTriple 95 8 false;
         RTriple 101 4 true;
         RTriple 79 4 false;
         RTriple 80 4 true;
         RTriple 24 4 false;
         RTriple 106 3 true;
         RTriple 80 5 false;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::6;1;2;0;3;2;1;5] [::9]
     [:: RTriple 40 7 false;
         RTriple 18 6 true;
         RTriple 10 5 true;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 26 0 false;
         RTriple 25 0 true;
         RTriple 70 0 false;
         RTriple 5 2 true;
         RTriple 110 1 true;
         RTriple 94 6 false;
         RTriple 100 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 97 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;5] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 98 0 false;
         RTriple 111 3 true;
         RTriple 109 2 true;
         RTriple 8 7 true;
         RTriple 4 6 true;
         RTriple 5 5 true;
         RTriple 112 4 true;
         RTriple 110 3 true;
         RTriple 40 4 true;
         RTriple 95 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 113 3 true;
         RTriple 6 8 true;
         RTriple 106 7 true;
         RTriple 7 5 true;
         RTriple 114 4 true;
         RTriple 105 8 true;
         RTriple 11 10 true;
         RTriple 14 9 true;
         RTriple 95 9 false;
         RTriple 101 5 true;
         RTriple 79 5 false;
         RTriple 80 5 true;
         RTriple 32 4 true;
         RTriple 26 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;7] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 6 3 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 4 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 16 2 true;
         RTriple 12 1 true;
         RTriple 67 0 false;
         RTriple 68 0 true;
         RTriple 108 3 true;
         RTriple 106 2 true;
         RTriple 6 8 true;
         RTriple 106 7 true;
         RTriple 105 8 true;
         RTriple 102 7 true;
         RTriple 9 5 true;
         RTriple 109 4 true;
         RTriple 68 11 false;
         RTriple 12 10 true;
         RTriple 16 9 true;
         RTriple 100 5 true;
         RTriple 26 5 false;
         RTriple 25 5 true;
         RTriple 70 5 false;
         RTriple 5 7 true;
         RTriple 110 6 true;
         RTriple 20 10 false;
         RTriple 99 11 false;
         RTriple 100 7 true;
         RTriple 23 7 false;
         RTriple 24 7 true;
         RTriple 79 7 false;
         RTriple 80 7 true;
         RTriple 97 5 true;
         RTriple 34 4 true;
         RTriple 36 3 true;
         RTriple 28 2 true;
         RTriple 34 1 true;
         RTriple 66 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 17 9 true;
         RTriple 12 8 true;
         RTriple 16 7 true;
         RTriple 100 3 true;
         RTriple 32 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;6] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 4 6 true;
         RTriple 6 9 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 17 10 true;
         RTriple 12 9 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 29 2 false;
         RTriple 30 2 true;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::7;2;0;1;2;3;2;0;6] [::8;3;2;0]
     [:: RTriple 22 0 false;
         RTriple 21 0 true;
         RTriple 98 0 false;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 104 5 true;
         RTriple 6 4 true;
         RTriple 108 3 true;
         RTriple 17 10 true;
         RTriple 12 9 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 24 3 true;
         RTriple 32 2 true;
         RTriple 26 1 true;
         RTriple 44 0 true];
     add_rel [::4;0;2;1;3;2;0;5] [::9]
     [:: RTriple 94 7 false;
         RTriple 17 6 true;
         RTriple 12 5 true;
         RTriple 16 4 true;
         RTriple 100 0 true;
         RTriple 24 0 false;
         RTriple 23 0 true;
         RTriple 54 0 false;
         RTriple 53 0 true;
         RTriple 4 2 true;
         RTriple 112 1 true;
         RTriple 95 2 false;
         RTriple 101 3 true;
         RTriple 44 2 true;
         RTriple 97 0 true];
     add_rel [::5;0;1;2;1;3;2;0;6] [::8;3;2;0]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 17 8 true;
         RTriple 12 7 true;
         RTriple 16 6 true;
         RTriple 100 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::5;0;1;2;0;1;3;2;1;5] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 4 6 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 11 9 true;
         RTriple 14 8 true;
         RTriple 94 8 false;
         RTriple 100 4 true;
         RTriple 69 4 true;
         RTriple 44 4 true;
         RTriple 26 4 false;
         RTriple 105 3 true;
         RTriple 44 5 false;
         RTriple 13 4 true;
         RTriple 101 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::5;0;1;2;1;3;2;5] [::8;3;2]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 11 7 true;
         RTriple 14 6 true;
         RTriple 94 6 false;
         RTriple 100 2 true;
         RTriple 69 2 true;
         RTriple 44 2 true;
         RTriple 24 1 true;
         RTriple 80 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;6] [::9]
     [:: RTriple 52 0 false;
         RTriple 51 0 true;
         RTriple 111 1 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 5 3 true;
         RTriple 112 2 true;
         RTriple 94 3 false;
         RTriple 6 5 true;
         RTriple 108 4 true;
         RTriple 6 9 true;
         RTriple 106 8 true;
         RTriple 105 9 true;
         RTriple 102 8 true;
         RTriple 9 6 true;
         RTriple 109 5 true;
         RTriple 12 11 true;
         RTriple 16 10 true;
         RTriple 100 6 true;
         RTriple 32 5 true;
         RTriple 24 4 true;
         RTriple 80 3 true;
         RTriple 64 3 false;
         RTriple 15 2 true;
         RTriple 96 0 true;
         RTriple 97 0 true;
         RTriple 35 0 false;
         RTriple 33 1 false;
         RTriple 34 1 true;
         RTriple 36 0 true];
     add_rel [::6;1;2;0;3;2;6] [::7;2;0;3;2]
     [:: RTriple 5 3 true;
         RTriple 12 5 true;
         RTriple 17 4 true;
         RTriple 16 3 true;
         RTriple 12 2 true;
         RTriple 99 0 true;
         RTriple 105 2 true];
     add_rel [::5;0;1;2;1;3;2;4] [::7;2;1;3;2]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 13 7 true;
         RTriple 10 6 true;
         RTriple 18 5 true;
         RTriple 94 4 true;
         RTriple 40 4 false;
         RTriple 13 3 true;
         RTriple 10 2 true;
         RTriple 98 0 true;
         RTriple 14 2 true;
         RTriple 11 1 true;
         RTriple 59 0 true;
         RTriple 52 0 true;
         RTriple 106 2 true;
         RTriple 107 3 true;
         RTriple 104 1 true;
         RTriple 19 0 false;
         RTriple 20 0 true];
     add_rel [::7;2;0;1;2;3;2;0;1;2;3] [::3;7;2;0;1;2;3;2;0;1;2]
     [:: RTriple 8 4 true;
         RTriple 4 3 true;
         RTriple 5 2 true;
         RTriple 6 7 true;
         RTriple 106 6 true;
         RTriple 7 4 true;
         RTriple 105 7 true;
         RTriple 107 8 true;
         RTriple 103 6 true;
         RTriple 102 5 true;
         RTriple 9 3 true;
         RTriple 8 1 true;
         RTriple 118 0 true;
         RTriple 105 3 true;
         RTriple 104 5 true;
         RTriple 106 4 true;
         RTriple 5 8 true;
         RTriple 4 7 true;
         RTriple 107 5 true;
         RTriple 102 8 true];
     add_rel [::5;0;1;2;1;3;2;0;1] [::3;5;0;1;2;1;3;2;0]
     [:: RTriple 95 0 false;
         RTriple 113 1 true;
         RTriple 7 3 true;
         RTriple 114 2 true;
         RTriple 8 5 true;
         RTriple 4 4 true;
         RTriple 115 3 true;
         RTriple 6 8 true;
         RTriple 106 7 true;
         RTriple 7 5 true;
         RTriple 114 4 true;
         RTriple 8 2 true;
         RTriple 5 1 true;
         RTriple 110 0 true;
         RTriple 16 4 true;
         RTriple 12 3 true;
         RTriple 17 2 true;
         RTriple 95 1 true;
         RTriple 106 4 true;
         RTriple 107 5 true;
         RTriple 104 3 true];
     add_rel [::5;0;1;2;0;1;3;2;0;1;5] [::9]
     [:: RTriple 94 0 false;
         RTriple 6 2 true;
         RTriple 108 1 true;
         RTriple 9 3 true;
         RTriple 109 2 true;
         RTriple 4 6 true;
         RTriple 6 9 true;
         RTriple 7 7 true;
         RTriple 8 5 true;
         RTriple 5 4 true;
         RTriple 110 3 true;
         RTriple 106 7 true;
         RTriple 94 11 false;
         RTriple 17 10 true;
         RTriple 12 9 true;
         RTriple 16 8 true;
         RTriple 100 4 true;
         RTriple 24 4 false;
         RTriple 23 4 true;
         RTriple 54 4 false;
         RTriple 53 4 true;
         RTriple 4 6 true;
         RTriple 112 5 true;
         RTriple 95 6 false;
         RTriple 101 7 true;
         RTriple 44 6 true;
         RTriple 97 4 true;
         RTriple 36 3 true;
         RTriple 34 2 true;
         RTriple 28 1 true;
         RTriple 92 0 true];
     rm_rel 4
     [:: RTriple 105 0 false];
     rm_rel 4
     [:: RTriple 103 0 false];
     rm_rel 4
     [:: RTriple 99 0 false];
     rm_rel 4
     [:: RTriple 100 0 false];
     rm_rel 4
     [:: RTriple 102 0 false];
     rm_rel 4
     [:: RTriple 97 0 false];
     rm_rel 4
     [:: RTriple 102 0 false];
     rm_rel 4
     [:: RTriple 103 0 false];
     rm_rel 4
     [:: RTriple 105 0 false];
     rm_rel 4
     [:: RTriple 100 0 false];
     rm_rel 4
     [:: RTriple 101 0 false];
     rm_rel 4
     [:: RTriple 106 0 false];
     rm_rel 4
     [:: RTriple 102 0 false];
     rm_rel 4
     [:: RTriple 99 0 false];
     rm_rel 4
     [:: RTriple 93 0 false];
     rm_rel 4
     [:: RTriple 4 0 true;
         RTriple 101 0 false];
     rm_rel 5
     [:: RTriple 5 0 true;
         RTriple 99 0 false];
     rm_rel 6
     [:: RTriple 6 0 true;
         RTriple 103 0 false];
     rm_rel 7
     [:: RTriple 7 0 true;
         RTriple 101 0 false];
     rm_rel 8
     [:: RTriple 8 0 true;
         RTriple 105 0 false];
     rm_rel 9
     [:: RTriple 9 0 true;
         RTriple 103 0 false];
     rm_rel 10
     [:: RTriple 10 0 true;
         RTriple 100 0 false];
     rm_rel 11
     [:: RTriple 11 0 true;
         RTriple 103 0 false];
     rm_rel 12
     [:: RTriple 12 0 true;
         RTriple 103 0 false];
     rm_rel 13
     [::];
     rm_rel 14
     [:: RTriple 14 0 true;
         RTriple 22 0 false];
     rm_rel 15
     [:: RTriple 15 0 true;
         RTriple 31 0 false];
     rm_rel 16
     [:: RTriple 16 0 true;
         RTriple 42 0 false];
     rm_rel 17
     [:: RTriple 17 0 true;
         RTriple 53 0 false];
     rm_rel 18
     [:: RTriple 18 0 true;
         RTriple 14 0 false];
     rm_rel 19
     [::];
     rm_rel 20
     [:: RTriple 20 0 true;
         RTriple 28 0 false];
     rm_rel 21
     [:: RTriple 21 0 true;
         RTriple 39 0 false];
     rm_rel 22
     [:: RTriple 22 0 true;
         RTriple 50 0 false];
     rm_rel 23
     [:: RTriple 23 0 true;
         RTriple 15 0 false];
     rm_rel 24
     [:: RTriple 24 0 true;
         RTriple 20 0 false];
     rm_rel 25
     [::];
     rm_rel 26
     [:: RTriple 26 0 true;
         RTriple 36 0 false];
     rm_rel 27
     [:: RTriple 27 0 true;
         RTriple 47 0 false];
     rm_rel 28
     [:: RTriple 28 0 true;
         RTriple 79 0 false];
     rm_rel 29
     [:: RTriple 29 0 true;
         RTriple 16 0 false];
     rm_rel 30
     [:: RTriple 30 0 true;
         RTriple 21 0 false];
     rm_rel 31
     [:: RTriple 31 0 true;
         RTriple 26 0 false];
     rm_rel 32
     [::];
     rm_rel 33
     [:: RTriple 33 0 true;
         RTriple 43 0 false];
     rm_rel 34
     [:: RTriple 34 0 true;
         RTriple 77 0 false];
     rm_rel 35
     [:: RTriple 35 0 true;
         RTriple 17 0 false];
     rm_rel 36
     [:: RTriple 36 0 true;
         RTriple 22 0 false];
     rm_rel 37
     [:: RTriple 37 0 true;
         RTriple 27 0 false];
     rm_rel 38
     [:: RTriple 38 0 true;
         RTriple 33 0 false];
     rm_rel 39
     [::];
     rm_rel 40
     [:: RTriple 40 0 true;
         RTriple 76 0 false]].

Definition not_RennerD41_order := [::0;1;2;3;4;5;6;7;8;9].

(*
Eval compute in size (prelat not_RennerD41).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat not_RennerD41)].
Eval compute in size (prelat not_RennerD41_rws).
Eval compute in sumn [seq (size r.1 + size r.2)%N | r <- (prelat not_RennerD41_rws)].
Eval compute in size not_RennerD41_cert.
*)

Theorem isopres_not_RennerD41 : isopres not_RennerD41 not_RennerD41_rws.
Proof.
have wfc : wfpres_cert not_RennerD41 not_RennerD41_cert
  by vm_cast_no_check is_true_true.
suff -> : not_RennerD41_rws = final_pres wfc by apply: iso_final_pres.
apply/eqP; rewrite -eqpresE pgen_final_pres prelat_final_pres.
by vm_cast_no_check is_true_true.
Time Qed.

Theorem not_RennerD41_rws_convergent : convergent (prelat not_RennerD41_rws).
Proof.
apply: diamond.
  apply: (rgen_pres_terminating
            (newgK := reorderK (l := not_RennerD41_order) is_true_true)).
  apply (decreasing_wf (@lt_sizelexi_stable _ int) sizelexi_int_wf).
  by native_cast_no_check is_true_true.
have pgenOk : all (<%O^~ PArray.max_length) (pgen not_RennerD41_rws) by [].
apply: (spair_confluence_loop_trieP pgenOk (fuel := 10)).
rewrite spair_confluence_loop_trieE.
by native_cast_no_check is_true_true.
Time Qed.

Goal foldl (fun acc s => acc + size_int s) 0
  (traject (enum_normal_next_trie RennerD41_Gay_rws) [:: [::]] 24) = 10625.
Proof.
by native_cast_no_check (erefl 10625).
Time Qed.

Goal foldl (fun acc s => acc + size_int s) 0
  (traject (enum_normal_next_trie not_RennerD41_rws) [:: [::]] 18) = 12185.
Proof.
by native_cast_no_check (erefl 12185).
Time Qed.

Theorem not_iso_RennerD41 : isopres RennerD41_Gay not_RennerD41 -> False.
Proof.
move=> isoRennerD41.
have {}: isopres RennerD41_Gay_rws not_RennerD41_rws.
  apply: (isopres_trans (isopres_sym isopres_RennerD41_Gay)).
  exact: (isopres_trans isoRennerD41 isopres_not_RennerD41).
evar (rew_RennerD41 : word int -> option (word int)).
have rew_RennerD41P : rewrites1_Ok (prelat RennerD41_Gay_rws) rew_RennerD41.
  exact: (trie_rewrites1P (trielen := 10)).
evar (rew_not_RennerD41 : word int -> option (word int)).
have rew_not_RennerD41P : rewrites1_Ok (prelat not_RennerD41_rws) rew_not_RennerD41.
  exact: (trie_rewrites1P (trielen := 10)).
apply: (size_non_isopres rew_RennerD41P rew_not_RennerD41P
          RennerD41_Gay_rws_convergent not_RennerD41_rws_convergent
          (boundP := 24) (boundQ := 18)).
- by native_cast_no_check is_true_true.
- rewrite ltnNge -flatten_is_longerE.
  by native_cast_no_check is_true_true.
Time Qed.
