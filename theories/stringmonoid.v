From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.
From Coq Require Import PrimInt63 PString.


Require Import monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Implicit Types (a b c : char63).

Implicit Type (x y : int).

Fact natint_eq_axiom : Equality.axiom eqb.
Proof. by move=> i j; apply (iffP idP); rewrite -eqb_spec. Qed.
HB.instance Definition _ := hasDecEq.Build int natint_eq_axiom.

Lemma le0Z x : BinInt.Z.le 0 φ(x).
Proof. by have [] := to_Z_bounded x. Qed.

(* to_nat and of_nat are notation and not function ...*)
Definition int_to_nat (i : int) : nat := to_nat i.
Definition nat_to_int (n : nat) : int := of_nat n.
Fact int_to_natK : cancel int_to_nat nat_to_int.
Proof.
move=> i; rewrite /int_to_nat /nat_to_int.
rewrite Z2Nat.id ?of_to_Z // -to_Z_0.
exact: le0Z.
Qed.
HB.instance Definition _ := CanIsCountable int_to_natK.

Lemma int_to_nat_inj : injective int_to_nat.
Proof. exact: can_inj int_to_natK. Qed.

Check int : countType.

Fact int_disp : Order.disp_t. by []. Qed.

Lemma leintbE x y : (x ≤? y) = (int_to_nat x <= int_to_nat y).
Proof. by apply/lebP/leP; rewrite (Z2Nat.inj_le _ _ (@le0Z x) (@le0Z y)). Qed.
Lemma int_ltbE x y : (x <? y) = (int_to_nat x < int_to_nat y).
Proof. by apply/ltbP/ltP; rewrite (Z2Nat.inj_lt _ _ (@le0Z x) (@le0Z y)). Qed.

Fact int_lt_def x y : (x <? y) = (y != x) && (x ≤? y).
Proof.
by rewrite int_ltbE leintbE -(eqtype.inj_eq int_to_nat_inj) ltn_neqAle eq_sym.
Qed.
Fact leint_refl x : (x <=? x).
Proof. by rewrite leintbE leqnn. Qed.
Fact leint_anti : antisymmetric leb.
Proof. by move=> x y; rewrite !leintbE -eqn_leq => /eqP/int_to_nat_inj. Qed.
Fact leint_trans : transitive leb.
Proof. by move=> y x z; rewrite !leintbE => /leq_trans/[apply]. Qed.
HB.instance Definition _ := Order.isPOrder.Build int_disp int
                              int_lt_def leint_refl leint_anti leint_trans.

Lemma leintE x y : (x <= y)%O = (int_to_nat x <= int_to_nat y).
Proof. exact: leintbE. Qed.
Lemma int_ltE x y : (x < y)%O = (int_to_nat x < int_to_nat y).
Proof. exact: int_ltbE. Qed.

Fact leint_total : total (<=%O : rel int).
Proof. by move=> x y; rewrite !leintE -!leEnat Order.le_total. Qed.
HB.instance Definition _ := Order.POrder_isTotal.Build int_disp int leint_total.

Fact le0int x : (0 <= x)%O.
Proof. by rewrite leintE. Qed.
HB.instance Definition _ := Order.hasBottom.Build int_disp int le0int.


Implicit Types (s t u v : string).

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

Fact strcat_assoc : associative cat.
Proof. by move=> s t u; rewrite cat_assoc. Qed.
HB.instance Definition _ := isMonoid.Build string
                              strcat_assoc cat_empty_l cat_empty_r.

Lemma lengthE s : to_nat (length s) = seq.size (to_list s).
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
    if str_prefix r1 u then Some (cat r2 (sub u (length r1) (length u)))
    else str_rewrites1_front R' u
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
have lesz : seq.size (drop (seq.size (to_list r1)) (to_list u)) <= to_nat (length u).
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

Time Eval native_compute in count (fun l => seq.size l == (4 : nat))
                              [seq p ++ q | p <- lnat, q <- lnat].
Time Eval native_compute in count (fun l => seq.size l == (4 : nat))
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
