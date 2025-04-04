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

Fact to_natK : cancel (fun i => to_nat i) (fun n => of_nat n).
Proof. by move=> i; rewrite Z2Nat.id ?of_to_Z // -to_Z_0; exact: le0Z. Qed.
HB.instance Definition _ := CanIsCountable to_natK.

Lemma int_to_nat_inj : injective (fun i => to_nat i).
Proof. exact: can_inj to_natK. Qed.

(* Check int : countType. *)

Fact int_disp : Order.disp_t. by []. Qed.

Lemma leintbE x y : (x ≤? y) = (to_nat x <= to_nat y).
Proof. by apply/lebP/leP; rewrite (Z2Nat.inj_le _ _ (@le0Z x) (@le0Z y)). Qed.
Lemma ltintbE x y : (x <? y) = (to_nat x < to_nat y).
Proof. by apply/ltbP/ltP; rewrite (Z2Nat.inj_lt _ _ (@le0Z x) (@le0Z y)). Qed.

Fact int_lt_def x y : (x <? y) = (y != x) && (x ≤? y).
Proof.
by rewrite ltintbE leintbE -(eqtype.inj_eq int_to_nat_inj) ltn_neqAle eq_sym.
Qed.
Fact leint_refl x : (x <=? x).
Proof. by rewrite leintbE leqnn. Qed.
Fact leint_anti : antisymmetric leb.
Proof. by move=> x y; rewrite !leintbE -eqn_leq => /eqP/int_to_nat_inj. Qed.
Fact leint_trans : transitive leb.
Proof. by move=> y x z; rewrite !leintbE => /leq_trans/[apply]. Qed.
HB.instance Definition _ := Order.isPOrder.Build int_disp int
                              int_lt_def leint_refl leint_anti leint_trans.

Lemma leintE x y : (x <= y)%O = (to_nat x <= to_nat y).
Proof. exact: leintbE. Qed.
Lemma ltintE x y : (x < y)%O = (to_nat x < to_nat y).
Proof. exact: ltintbE. Qed.

Fact leint_total : total (<=%O : rel int).
Proof. by move=> x y; rewrite !leintE -!leEnat Order.le_total. Qed.
HB.instance Definition _ := Order.POrder_isTotal.Build int_disp int leint_total.

Fact le0int x : (0 <= x)%O.
Proof. by rewrite leintE. Qed.
HB.instance Definition _ := Order.hasBottom.Build int_disp int le0int.

Local Notation wBnat := (BinInt.Z.to_nat wB).

Lemma to_nat0 : to_nat 0 = 0%N.
Proof. by []. Qed.
Lemma to_nat1 : to_nat 1 = 1%N.
Proof. by []. Qed.

Lemma of_natK n : n < wBnat -> to_nat (of_nat n) = n.
Proof.
move=> ltn; rewrite of_Z_spec BinInt.Z.mod_small; first by rewrite Nat2Z.id.
split; first exact: Nat2Z.is_nonneg.
by rewrite -(Z2Nat.id wB); first exact/inj_lt/ltP.
Qed.

Lemma to_natD x y :
  to_nat x + to_nat y < wBnat -> to_nat (x + y) = (to_nat x + to_nat y)%N.
Proof.
have lex := le0Z x; have ley := le0Z y.
have lexy := BinInt.Z.add_nonneg_nonneg _ _ lex ley.
move=> lt; rewrite add_spec Zdiv.Zmod_small; first by rewrite Z2Nat.inj_add.
split; first exact: lexy.
rewrite Z2Nat.inj_lt.
- by rewrite (Z2Nat.inj_add _ _ lex ley); apply/ltP.
- exact: lexy.
- exact: BinInt.Z.lt_le_incl wB_pos.
Qed.

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

Lemma size_intE s : size_int s = of_nat (size s).
Proof.
rewrite /size_int; set f := (X in X 0%uint63).
suff -> : forall i, f i s = (i + of_nat (size s))%uint63.
  apply: to_Z_inj; rewrite add_spec to_Z_0 BinInt.Z.add_0_l.
  by rewrite -of_Z_spec of_to_Z.
elim: s => [| s0 s IHs] // m.
  apply: to_Z_inj; rewrite add_spec to_Z_0 BinInt.Z.add_0_r.
  by rewrite -of_Z_spec of_to_Z.
rewrite [LHS]/= {}IHs; apply: to_Z_inj.
rewrite !add_spec Zdiv.Zplus_mod_idemp_l.
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
