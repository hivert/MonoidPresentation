From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63 PString.
From mathcomp Require Import all_ssreflect.


Require Import int_seq monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Implicit Types (a b c : char63) (x y : int) (s t u v : string).

Definition strcmp s t := if compare s t is Eq then true else false.
Fact eqstr_axiom : Equality.axiom strcmp.
Proof.
rewrite /strcmp=> u v; apply (iffP idP).
case Ecmp : (compare u v) => c //=.
  by move: Ecmp; rewrite compare_eq.
by move=> ->; rewrite compare_refl.
Qed.
HB.instance Definition _ := hasDecEq.Build string eqstr_axiom.
HB.instance Definition _ := CanIsCountable of_to_list.

Fact strcat_assoc : associative PrimString.cat.
Proof. by move=> s t u; rewrite cat_assoc. Qed.
HB.instance Definition _ := isMonoid.Build string
                              strcat_assoc cat_empty_l cat_empty_r.

Lemma lengthE s : to_nat (length s) = size (to_list s).
Proof. by rewrite length_spec. Qed.

Lemma firstnE T n (l : list T) : List.firstn n l = take n l.
Proof. by elim: n l => [|n IHn] [|l0 l] //=; rewrite IHn. Qed.
Lemma skipnE T n (l : list T) : List.skipn n l = drop n l.
Proof. by elim: n l => [|n IHn] [|l0 l] //=; rewrite IHn. Qed.

Lemma take_strE s i : to_list (sub s 0 i) = take (to_nat i) (to_list s).
Proof. by rewrite sub_spec List.skipn_O firstnE. Qed.

Definition str_prefix u v := sub v 0 (length u) == u.

Lemma str_prefixE u v : str_prefix u v = prefix (to_list u) (to_list v).
Proof.
by rewrite /str_prefix -(eqtype.inj_eq to_list_inj) take_strE lengthE prefixE.
Qed.

Fixpoint str_rewrites1_front R u :=
  if R is (r1, r2) :: R' then
    if str_prefix r1 u then
      Some (PrimString.cat r2 (sub u (length r1) (length u)))
    else
      str_rewrites1_front R' u
  else None.
Lemma str_rewrites1_frontE (R : (seq (string * string))) u :
  (all (fun r => (length r.2 <= length r.1)%O) R) ->
  omap to_list (str_rewrites1_front R u) =
    rewrites1_front [seq (to_list r.1, to_list r.2) | r <- R] (to_list u).
Proof.
elim: R => [| [r1 r2] R IHR] //= /andP[lenr] {}/IHR <-.
rewrite str_prefixE; case Hpref: prefix => //=.
rewrite cat_spec; congr Some.
rewrite sub_spec !firstnE !skipnE (lengthE r1).
have lesz : size (drop (size (to_list r1)) (to_list u)) <= to_nat (length u).
  by rewrite size_drop lengthE leq_subr.
rewrite !take_oversize // {lesz} size_cat size_drop.
have /lebP := valid_length u.
rewrite leintbE /int_to_nat => /(leq_trans _); apply.
move: lenr; rewrite leintE /int_to_nat !lengthE.
move/size_prefix/subnKC : Hpref => {2}<-.
by rewrite leq_add2r.
Qed.

(* Check string : monoidType.

Eval compute in ("aaaa"%pstring * 1 * "bbb"%pstring)%M.


Time Definition lnat := Eval native_compute in
    [seq ncons i i [:: 1 : nat] | i <- iota 0 250].
Time Definition lint := Eval native_compute in
    [seq [seq nat_to_int i | i <- l] | l <- lnat].
Time Definition lstr := Eval native_compute in
    [seq of_list [seq 64 + i | i <- l] | l <- lint].

Time Eval native_compute in count (fun l => size l == (4 : nat))
                              [seq p ++ q | p <- lnat, q <- lnat].
Time Eval native_compute in count (fun l => size l == (4 : nat))
                              [seq p ++ q | p <- lint, q <- lint].
Time Eval native_compute in count (fun s => length s == 4)
                              [seq cat p q | p <- lstr, q <- lstr].

Time Eval native_compute in count (fun lp => lp.1 == lp.2)
                              [seq (p ++ q, q ++ p) | p <- lnat, q <- lnat].
Time Eval native_compute in count (fun lp => lp.1 == lp.2)
                              [seq (p ++ q, q ++ p) | p <- lint, q <- lint].
Time Eval native_compute in count (fun lp => lp.1 == lp.2)
                              [seq (cat p q, cat q p) | p <- lstr, q <- lstr].
*)
