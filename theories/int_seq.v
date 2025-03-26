From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63.
From mathcomp Require Import all_ssreflect.


Section Int.

Implicit Type (x y : int).

Local Open Scope uint63_scope.

Fact natint_eq_axiom : Equality.axiom PrimInt63.eqb.
Proof. by move=> i j; apply (iffP idP); rewrite -eqb_spec. Qed.
HB.instance Definition _ := hasDecEq.Build int natint_eq_axiom.

Lemma le0Z x : BinInt.Z.le 0 φ(x).
Proof. by have [] := to_Z_bounded x. Qed.
Lemma ltZwB x : BinInt.Z.lt φ(x) wB.
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

(* Check int : countType. *)

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

End Int.


Section Seq.

Context {T : eqType}.


Implicit Types (s : seq T) (i j : int) (n m : nat) (x : T).

Lemma firstnE n (l : list T) : List.firstn n l = take n l.
Proof. by elim: n l => [|n IHn] [|l0 l] //=; rewrite IHn. Qed.
Lemma skipnE n (l : list T) : List.skipn n l = drop n l.
Proof. by elim: n l => [|n IHn] [|l0 l] //=; rewrite IHn. Qed.


Definition size_int s : int :=
  let fix rec i s :=
    if s is s0 :: s' then rec (succ i)%uint63 s' else i
  in rec 0%uint63 s.
Fixpoint onth_int s i :=
  if s is s0 :: s' then
    if PrimInt63.eqb i 0 then Some s0 else onth_int s' (i - 1)%uint63
  else None.

Lemma size_intE s : size_int s = nat_to_int (size s).
Proof.
rewrite /size_int; set f := (X in X 0%uint63).
suff -> : forall i, f i s = (i + nat_to_int (size s))%uint63.
  apply: to_Z_inj; rewrite add_spec to_Z_0 BinInt.Z.add_0_l.
  by rewrite -of_Z_spec of_to_Z.
elim: s => [| s0 s IHs] //= m.
  apply: to_Z_inj; rewrite add_spec to_Z_0 BinInt.Z.add_0_r.
  by rewrite -of_Z_spec of_to_Z.
rewrite {}IHs; apply: to_Z_inj.
rewrite /nat_to_int !add_spec Zdiv.Zplus_mod_idemp_l.
rewrite Nat2Z.inj_succ !(of_Z_spec, Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_l).
by rewrite to_Z_1 [BinInt.Z.succ _]BinInt.Z.add_comm BinInt.Z.add_assoc.
Qed.

Lemma onth_int_mem s i x : onth_int s i = Some x -> x \in s.
Proof.
elim: s i => // s0 s IHs /= i.
case: (boolP (i =? 0)%uint63) => [_ [<-] | _]; first by rewrite inE eqxx.
by rewrite inE orbC => /IHs ->.
Qed.

End Seq.
