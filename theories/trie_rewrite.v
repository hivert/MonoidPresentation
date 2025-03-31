From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq eqtype
  choice path bigop.
(*From mathcomp Require Import order.
From mathcomp Require Import all_ssreflect. *)

Require Import monoids present trie.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Tries.

Implicit Types (u v : seq nat).

Fixpoint mkreltrie_rec res (rels : relat nat) :=
  if rels is (s, v) :: tl then mkreltrie_rec (instrie res s (Some v)) tl
  else res.
Definition mkreltrie := mkreltrie_rec emptytrie.

Fixpoint getreltrie (t : @trie (option (word nat))) v :=
  let: Trie (res, ch) := t in
  if res is Some r then Some (r, v) else
    if ch == [::] then None else
      if v is v0 :: v' then getreltrie (nth emptytrie ch v0) v'
    else None.

Lemma getrel_instrie t r1 r2 v :
  getreltrie (instrie t r1 (Some r2)) v =
    if getreltrie t v is Some (rres, suf) then
      if prefix r1 rres then 
    else None

Lemma getreltrie_recP t rels v :
  getreltrie (mkreltrie_rec t rels) v =
    if getreltrie t v is Some res then Some res else
      rewrites1_front rels v.
Proof.
rewrite /mktrie; elim: rels t v => [|[r0 r1] rels IHrels]//= t v.
  by case: getreltrie.
rewrite {}IHrels.

  
Require int_seq bbaaaabbba_abbbaa.

Definition testrels := [seq (map int_seq.int_to_nat r.1,
                            map int_seq.int_to_nat r.2) |
                         r <- prelat bbaaaabbba_abbbaa.present_final].
Definition tr := Eval native_compute in mktrie testrels.

Definition essai := [::3;0;0;1;3;1;1;1;2;3;2;2;2;1;2;1;1].

Eval compute in getreltrie tr essai ==
                  rewrites1_front testrels essai.
