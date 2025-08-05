(** * Primitive integer and sequences *)
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
From mathcomp Require Import all_ssreflect.


Section Nat.

Implicit Type (m n p q : nat).

Lemma add_natE m n : (m + n)%coq_nat = m + n.
Proof. by []. Qed.
Lemma mul_natE m n : (m * n)%coq_nat = m * n.
Proof. by []. Qed.
Lemma mod_natE m n : m mod n = m %% n.
Proof.
case: (altP (n =P 0)) => [->|/eqP neq]; first by rewrite Nat.mod_0_r modn0.
rewrite {2}(Nat.div_mod_eq m n) add_natE mul_natE mulnC modnMDl modn_small //.
by apply/ltP; apply: Nat.mod_upper_bound.
Qed.
Lemma div_natE m n : m / n = m %/ n.
Proof.
case: (altP (n =P 0)) => [-> | /negbTE neq]; first by rewrite Nat.div_0_r divn0.
apply/eqP; have := (eqn_mul2r n (m / n) (m %/ n)); rewrite neq /= => <-.
rewrite -mul_natE -(eqn_add2r (m mod n)) mod_natE -divn_eq.
by rewrite mul_natE mulnC -mul_natE -add_natE -mod_natE -Nat.Div0.div_mod.
Qed.

End Nat.


Section Int.

Implicit Type (x y : int) (m n : nat).

Local Open Scope uint63_scope.

Fact natint_eq_axiom : Equality.axiom PrimInt63.eqb.
Proof. by move=> i j; apply (iffP idP); rewrite -eqb_spec. Qed.
HB.instance Definition _ := hasDecEq.Build int natint_eq_axiom.

Lemma le0Z x : BinInt.Z.le 0 φ(x).
Proof. by have [] := to_Z_bounded x. Qed.
Lemma ltZwB x : BinInt.Z.lt φ(x) wB.
Proof. by have [] := to_Z_bounded x. Qed.
Hint Resolve le0Z ltZwB : core.

Fact to_natK : cancel (fun i => to_nat i) (fun n => of_nat n).
Proof. by move=> i; rewrite Z2Nat.id ?of_to_Z // -to_Z_0. Qed.
HB.instance Definition _ := CanIsCountable to_natK.

Lemma to_nat_inj : injective (fun i => to_nat i).
Proof. exact: can_inj to_natK. Qed.

(* Check int : countType. *)

Fact int_disp : Order.disp_t. by []. Qed.

Lemma leintbE x y : (x ≤? y) = (to_nat x <= to_nat y).
Proof. by apply/lebP/leP; rewrite Z2Nat.inj_le. Qed.
Lemma ltintbE x y : (x <? y) = (to_nat x < to_nat y).
Proof. by apply/ltbP/ltP; rewrite Z2Nat.inj_lt. Qed.

Fact ltint_def x y : (x <? y) = (y != x) && (x ≤? y).
Proof.
by rewrite ltintbE leintbE -(inj_eq to_nat_inj) ltn_neqAle eq_sym.
Qed.
Fact leint_refl x : (x <=? x).
Proof. by rewrite leintbE leqnn. Qed.
Fact leint_anti : antisymmetric leb.
Proof. by move=> x y; rewrite !leintbE -eqn_leq => /eqP/to_nat_inj. Qed.
Fact leint_trans : transitive leb.
Proof. by move=> y x z; rewrite !leintbE => /leq_trans/[apply]. Qed.
HB.instance Definition _ := Order.isPOrder.Build int_disp int
                              ltint_def leint_refl leint_anti leint_trans.

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

Lemma maxintE x y : to_nat (max x y) = maxn (to_nat x) (to_nat y).
Proof.
rewrite max_spec Z2Nat.inj_max; apply anti_leq; apply/andP; split.
  by apply/leP; apply: Nat.max_lub; apply/leP; [apply: leq_maxl | apply: leq_maxr].
rewrite geq_max; apply/andP.
by split; apply/leP; [apply: Nat.le_max_l | apply: Nat.le_max_r].
Qed.

Lemma minintE x y : to_nat (min x y) = minn (to_nat x) (to_nat y).
Proof.
rewrite min_spec Z2Nat.inj_min; apply anti_leq; apply/andP; split.
  rewrite leq_min; apply/andP.
  by split; apply/leP; [apply: Nat.le_min_l | apply: Nat.le_min_r].
by apply/leP; apply: Nat.min_glb; apply/leP; [apply: geq_minl | apply: geq_minr].
Qed.


Notation wBnat := (BinInt.Z.to_nat wB).

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

Lemma ltwBnat i : to_nat i < wBnat.
Proof. by apply/ltP; have := ltZwB i; rewrite Z2Nat.inj_lt. Qed.

Lemma to_natDE x y : to_nat (x + y) = (to_nat x + to_nat y) %% wBnat.
Proof.
rewrite add_spec Z2Nat.inj_mod //; last exact: BinInt.Z.add_nonneg_nonneg.
by rewrite Z2Nat.inj_add // mod_natE.
Qed.
Lemma to_natD x y :
  to_nat x + to_nat y < wBnat -> to_nat (x + y) = (to_nat x + to_nat y)%N.
Proof. by move=> lt; rewrite to_natDE modn_small. Qed.

Lemma ltleint x y : (x < y)%O -> (x + 1 <= y)%O.
Proof.
move=> /[dup] ltxy; rewrite ltintE -addn1 -to_nat1 -to_natD ?leintE //.
move: ltxy; rewrite to_nat1 addn1 ltintE => /leq_ltn_trans; apply.
exact: ltwBnat.
Qed.

Lemma int_neq0 x : x != 0 -> (1 <= x)%O.
Proof.
rewrite eq_sym => /negbTE neq0; have := le0int x.
rewrite Order.POrderTheory.le_eqVlt neq0 /= => /ltleint.
by rewrite leintE to_natD.
Qed.

Lemma to_natB x y : (x <= y)%O -> to_nat (y - x) = (to_nat y - to_nat x)%N.
Proof.
move=> /lebP /Zorder.Zle_minus_le_0 le0xBy.
rewrite sub_spec BinInt.Z.mod_small ?Z2Nat.inj_sub //; split => //.
apply: (BinInt.Z.le_lt_trans _ _ _ _ (ltZwB y)).
by rewrite -BinInt.Z.le_sub_nonneg.
Qed.

Lemma succ_subint1E x : x != 0 -> (to_nat (x - 1)).+1 = to_nat x.
Proof.
move=> /int_neq0/[dup] lt1x /to_natB ->.
rewrite to_nat1 subn1 prednK //.
by move: lt1x; rewrite leintE to_nat1.
Qed.

Lemma to_natME x y : to_nat (x * y) = (to_nat x * to_nat y) %% wBnat.
Proof.
rewrite mul_spec Z2Nat.inj_mod //; last exact: BinInt.Z.mul_nonneg_nonneg.
by rewrite Z2Nat.inj_mul // mod_natE.
Qed.
Lemma to_natM x y :
  to_nat x * to_nat y < wBnat -> to_nat (x * y) = (to_nat x * to_nat y)%N.
Proof. by move=> lt; rewrite to_natME modn_small. Qed.

Lemma to_nat_mod x y : to_nat (x mod y) = (to_nat x %% to_nat y)%N.
Proof. by rewrite mod_spec Z2Nat.inj_mod // mod_natE. Qed.
Lemma to_nat_div x y : to_nat (x / y) = (to_nat x %/ to_nat y)%N.
Proof. by rewrite div_spec Z2Nat.inj_div // div_natE. Qed.

End Int.


Section Seq.

Context {T : eqType}.
Implicit Types (s : seq T) (i j : int) (n m : nat) (x : T).

Lemma firstnE n (l : list T) : List.firstn n l = take n l.
Proof. by elim: n l => [|n IHn] [|l0 l] //=; rewrite IHn. Qed.
Lemma skipnE n (l : list T) : List.skipn n l = drop n l.
Proof. by elim: n l => [|n IHn] [|l0 l] //=; rewrite IHn. Qed.

Definition remove_ith_int :=
  let fix auxrem acc s i :=
    if s is s0 :: s' then
      if (i =? 0)%uint63 then catrev acc s'
      else auxrem (s0 :: acc) s' (i - 1)%uint63
    else rev acc
  in auxrem [::].

Lemma remove_ith_intE s i :
  remove_ith_int s i = take (to_nat i) s ++ drop (to_nat i).+1 s.
Proof.
rewrite /remove_ith_int -[RHS](cat0s) -[X in X ++ _]/(rev [::]).
elim: s i [::] => [| s0 s IHs] i acc /=; first by rewrite cats0.
case: (boolP (i =? 0)%uint63) => [/eqb_correct -> | ineq0] /=.
  by rewrite catrevE drop0.
by rewrite {}IHs /= -(succ_subint1E _ ineq0) //= rev_cons -cats1 -catA cat1s.
Qed.


Definition size_int s : int :=
  let fix rec i s :=
    if s is s0 :: s' then rec (succ i)%uint63 s' else i
  in rec 0%uint63 s.
Fixpoint onth_int s i :=
  if s is s0 :: s' then
    if (i =? 0)%uint63 then Some s0 else onth_int s' (i - 1)%uint63
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

Lemma onth_int_le s i x : onth_int s i = Some x -> to_nat i < size s.
Proof.
elim: s i => // s0 s IHs /= i.
case: (boolP (i =? 0)%uint63) => [/eqb_correct -> _ //| ineq0 {}/IHs].
by rewrite -ltnS succ_subint1E.
Qed.

Lemma onth_intE s i x :
  onth_int s i = Some x -> forall x0, nth x0 s (to_nat i) = x.
Proof.
elim: s i => // s0 s IHs /= i.
case: (boolP (i =? 0)%uint63) => [/eqb_correct -> [->] x0 |].
  by rewrite to_nat0.
by move=> ineq0 {}/IHs Hrec x0; rewrite -(Hrec x0) -succ_subint1E.
Qed.

Implicit Type t : seq (seq T).
Fixpoint behead_flatten t :=
  match t with
  | (_ :: l) :: t' => l :: t'
  | [::] :: t' => behead_flatten t'
  | [::] => [::]
  end.
Fixpoint drop_flatten s t {struct s} :=
  if s is _ :: s' then drop_flatten s' (behead_flatten t)
  else t.
Fixpoint drop_size_flatten t1 t2 {struct t1} :=
  if t1 is s :: t1' then drop_size_flatten t1' (drop_flatten s t2)
  else t2.

Lemma behead_flattenE t : flatten (behead_flatten t) = behead (flatten t).
Proof. by elim: t => // -[|a l]. Qed.
Lemma drop_flattenE s t : flatten (drop_flatten s t) = drop (size s) (flatten t).
Proof.
elim: s t => [| s0 s IHs] t /=; first by rewrite drop0.
by rewrite IHs behead_flattenE -drop1 drop_drop addn1.
Qed.
Lemma drop_size_flattenE t1 t2 :
  flatten (drop_size_flatten t1 t2) = drop (size (flatten t1)) (flatten t2).
Proof.
elim: t1 t2 => [| s t IHt] t2 /=; first by rewrite drop0.
by rewrite IHt /= drop_flattenE size_cat drop_drop addnC.
Qed.

Definition all_nil :=
  all (fun s : seq T => if s is [::] then true else false).
Definition flatten_is_longer t1 t2 := all_nil (drop_size_flatten t1 t2).

Lemma all_nil_flattenP t : reflect (flatten t = [::]) (all_nil t).
Proof.
rewrite /all_nil; apply (iffP allP); elim: t => //= t0 t IHt.
  move=> Hin; rewrite IHt ?cats0.
    have {}/Hin : t0 \in t0 :: t by rewrite inE eqxx.
    by case: t0.
  move=> s sint.
  by have {}/Hin : s \in t0 :: t by rewrite inE sint orbT.
case: t0 => //; rewrite cat0s => {}/IHt Hin s.
by rewrite inE => /orP[/eqP-> // | /Hin].
Qed.

Lemma flatten_is_longerE t1 t2 :
  flatten_is_longer t1 t2 = (size (flatten t1) >= size (flatten t2)).
Proof.
rewrite /flatten_is_longer -subn_eq0 -size_drop -drop_size_flattenE.
by apply/all_nil_flattenP/eqP => [-> //| H]; apply/nilP/eqP.
Qed.

End Seq.
