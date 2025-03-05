From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.
From Coq Require Import PrimInt63 PString.


Require Import monoids.

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

Check string : monoidType.

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

