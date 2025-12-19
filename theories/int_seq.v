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
From Stdlib Require Import Znat BinIntDef Uint63 Ring Ring63.
From mathcomp Require Import all_boot all_order nmodule ssralg zmodp.


Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

Require Import well_founded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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


Local Open Scope uint63_scope.

Section IntRing.

Implicit Type (x y : int) (m n : nat).

Lemma le0Z x : BinInt.Z.le 0 φ(x).
Proof. by have [] := to_Z_bounded x. Qed.
Lemma ltZwB x : BinInt.Z.lt φ(x) wB.
Proof. by have [] := to_Z_bounded x. Qed.
Hint Resolve le0Z ltZwB : core.

Fact natint_eq_axiom : Equality.axiom PrimInt63.eqb.
Proof. by move=> i j; apply (iffP idP); rewrite -eqb_spec. Qed.
HB.instance Definition _ := hasDecEq.Build int natint_eq_axiom.

Fact to_natK : cancel (fun i => to_nat i) (fun n => of_nat n).
Proof. by move=> i; rewrite Z2Nat.id ?of_to_Z // -to_Z_0. Qed.
HB.instance Definition _ := CanIsCountable to_natK.

Lemma to_nat_inj : injective (fun i => to_nat i).
Proof. exact: can_inj to_natK. Qed.

Lemma add0i : left_id (0 : int) add.
Proof. move=> x; ring. Qed.
Lemma addNi : left_inverse 0%uint63 opp add.
Proof. move=> x; ring. Qed.
HB.instance Definition _ :=
  GRing.isZmodule.Build int add_assoc add_comm add0i addNi.

Lemma muliA : associative PrimInt63.mul.
Proof. move=> x y z; ring. Qed.
Lemma  mul1i : left_id (1 : int) PrimInt63.mul.
Proof. move=> x; ring. Qed.
Lemma  muli1 : right_id (1 : int) PrimInt63.mul.
Proof. move=> x; ring. Qed.
Lemma  muliDl : left_distributive PrimInt63.mul add.
Proof. move=> x y z; ring. Qed.
Lemma  muliDr : right_distributive PrimInt63.mul add.
Proof. move=> x y z; ring. Qed.
Lemma  onei_neq0 : (1 : int) != (0 : int).
Proof. by []. Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isNzRing.Build int muliA mul1i muli1 muliDl muliDr onei_neq0.

Lemma to_nat0 : to_nat 0 = 0%N.
Proof. by []. Qed.
Lemma to_nat1 : to_nat 1 = 1%N.
Proof. by []. Qed.

Lemma int0E : 0 = 0%R.
Proof. by []. Qed.
Lemma int1E : 1 = 1%R.
Proof. by []. Qed.
Lemma intDE : add =2 +%R.
Proof. by []. Qed.
Lemma intME : PrimInt63.mul =2 GRing.mul.
Proof. by []. Qed.
Lemma intNE x : - x  = (- x)%R.
Proof. by rewrite -[RHS]of_to_Z -[LHS]of_to_Z sub_spec. Qed.
Lemma intBE x y : x - y = (x - y)%R.
Proof.
rewrite -intDE -[RHS]of_to_Z -[LHS]of_to_Z sub_spec add_spec opp_spec.
by rewrite -BinInt.Z.add_opp_r Zdiv.Zplus_mod_idemp_r.
Qed.

Definition int_to_ring := (int0E, int1E, intDE, intME, intNE, intBE).

End IntRing.
Hint Resolve le0Z ltZwB : core.

Lemma succDl u v : succ u + v = succ (u + v).
Proof. by rewrite /succ; ring. Qed.
Lemma succDr u v : u + succ v = succ (u + v).
Proof. by rewrite /succ; ring. Qed.


Definition wBnat := locked (BinInt.Z.to_nat wB).
Lemma wBnatE : wBnat = BinInt.Z.to_nat wB.
Proof. by rewrite /wBnat; unlock. Qed.

Lemma of_nat_modK n : to_nat (of_nat n) = n %% wBnat.
Proof.
rewrite of_Z_spec Z2Nat.inj_mod //; last exact: Nat2Z.is_nonneg.
by rewrite mod_natE -wBnatE Nat2Z.id.
Qed.
Lemma of_wBnat : of_nat wBnat = 0.
Proof. by apply: to_nat_inj; rewrite to_nat0 of_nat_modK modnn. Qed.

Lemma of_natK n : n < wBnat -> to_nat (of_nat n) = n.
Proof. by rewrite of_nat_modK => /modn_small. Qed.

Lemma ltwBnat i : to_nat i < wBnat.
Proof. by rewrite wBnatE; apply/ltP; have := ltZwB i; rewrite Z2Nat.inj_lt. Qed.


Lemma to_natDE x y : to_nat (x + y) = (to_nat x + to_nat y) %% wBnat.
Proof.
rewrite add_spec Z2Nat.inj_mod //; last exact: BinInt.Z.add_nonneg_nonneg.
by rewrite Z2Nat.inj_add // mod_natE wBnatE.
Qed.
Lemma to_natME x y : to_nat (x * y) = (to_nat x * to_nat y) %% wBnat.
Proof.
rewrite mul_spec Z2Nat.inj_mod //; last exact: BinInt.Z.mul_nonneg_nonneg.
by rewrite Z2Nat.inj_mul // mod_natE wBnatE.
Qed.

Lemma natrEint n : n%:R%R = of_nat n.
Proof.
elim: n => // n IHn.
rewrite -addn1 GRing.natrD -intDE {}IHn -[X in _ + X = _]/(of_nat 1).
by apply: to_nat_inj; rewrite to_natDE !of_nat_modK modnDmr modnDml.
Qed.


Section IntOrder.

Implicit Type (x y : int) (m n : nat).

Fact int_disp : Order.disp_t. by []. Qed.

Lemma leEintb x y : (x ≤? y) = (to_nat x <= to_nat y).
Proof. by apply/lebP/leP; rewrite Z2Nat.inj_le. Qed.
Lemma ltEintb x y : (x <? y) = (to_nat x < to_nat y).
Proof. by apply/ltbP/ltP; rewrite Z2Nat.inj_lt. Qed.

Fact ltint_def x y : (x <? y) = (y != x) && (x ≤? y).
Proof.
by rewrite ltEintb leEintb -(inj_eq to_nat_inj) ltn_neqAle eq_sym.
Qed.
Fact leint_refl x : (x <=? x).
Proof. by rewrite leEintb leqnn. Qed.
Fact leint_anti : antisymmetric leb.
Proof. by move=> x y; rewrite !leEintb -eqn_leq => /eqP/to_nat_inj. Qed.
Fact leint_trans : transitive leb.
Proof. by move=> y x z; rewrite !leEintb => /leq_trans/[apply]. Qed.
HB.instance Definition _ := Order.isPOrder.Build int_disp int
                              ltint_def leint_refl leint_anti leint_trans.

Lemma leEint x y : (x <= y)%O = (to_nat x <= to_nat y).
Proof. exact: leEintb. Qed.
Lemma ltEint x y : (x < y)%O = (to_nat x < to_nat y).
Proof. exact: ltEintb. Qed.

Fact leint_total : total (<=%O : rel int).
Proof. by move=> x y; rewrite !leEint -!leEnat Order.le_total. Qed.
HB.instance Definition _ := Order.POrder_isTotal.Build int_disp int leint_total.

Fact le0int x : (0 <= x)%O.
Proof. by rewrite leEint. Qed.
HB.instance Definition _ := Order.hasBottom.Build int_disp int le0int.
Hint Resolve le0int : core.

Lemma maxEint x y : to_nat (max x y) = maxn (to_nat x) (to_nat y).
Proof.
rewrite max_spec Z2Nat.inj_max; apply anti_leq; apply/andP; split.
  by apply/leP; apply: Nat.max_lub; apply/leP; [apply: leq_maxl | apply: leq_maxr].
rewrite geq_max; apply/andP.
by split; apply/leP; [apply: Nat.le_max_l | apply: Nat.le_max_r].
Qed.

Lemma minEint x y : to_nat (min x y) = minn (to_nat x) (to_nat y).
Proof.
rewrite min_spec Z2Nat.inj_min; apply anti_leq; apply/andP; split.
  rewrite leq_min; apply/andP.
  by split; apply/leP; [apply: Nat.le_min_l | apply: Nat.le_min_r].
by apply/leP; apply: Nat.min_glb; apply/leP; [apply: geq_minl | apply: geq_minr].
Qed.

Lemma wf_ltint : well_founded (<%O : rel int).
Proof. by apply: (wf_f _ wf_ltnat) => x y; rewrite ltEint; apply. Qed.

End IntOrder.


Section ZmodP.

Local Notation ZwB := 'Z_wBnat.

Implicit Type (x y : int) (m n : nat) (z : ZwB).

Definition to_ZwB x : ZwB := (to_nat x)%:R%R.
Definition of_ZwB z : int := of_nat z.

Local Lemma Zp_trunc_wBnat : (Zp_trunc wBnat).+2 = wBnat.
Proof. by rewrite wBnatE /= Zp_cast. Qed.

Lemma to_ZwBK : cancel to_ZwB of_ZwB.
Proof.
move=> x; rewrite /to_ZwB /of_ZwB Zp_nat /= Zp_trunc_wBnat -mod_natE.
by rewrite wBnatE -Z2Nat.inj_mod // BinInt.Z.mod_small // to_natK.
Qed.
Lemma of_ZwBK : cancel of_ZwB to_ZwB.
Proof.
move=> z; rewrite /to_ZwB /of_ZwB /= Zp_nat.
by rewrite -(valZpK z) of_natK ?valZpK // -{2}Zp_trunc_wBnat.
Qed.

Lemma to_ZwBK_is_nmod_morphism : GRing.nmod_morphism to_ZwB.
Proof.
rewrite /to_ZwB; split; first by rewrite to_nat0.
move=> /= x y; rewrite -GRing.natrD to_natDE; move: (_ + _)%N => i.
by rewrite Zp_nat_mod // wBnatE.
Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build int ZwB to_ZwB to_ZwBK_is_nmod_morphism.

Lemma to_ZwBK_is_monoid_morphism : GRing.monoid_morphism to_ZwB.
Proof.
rewrite /to_ZwB; split; first by rewrite to_nat1.
move=> /= x y; rewrite -GRing.natrM to_natME; move: (_ * _)%N => i.
by rewrite Zp_nat_mod // wBnatE.
Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build int ZwB to_ZwB to_ZwBK_is_monoid_morphism.

End ZmodP.


Section Int.

Implicit Type (x y : int) (m n : nat).

Lemma to_natD x y :
  to_nat x + to_nat y < wBnat -> to_nat (x + y) = (to_nat x + to_nat y)%N.
Proof. by move=> lt; rewrite to_natDE modn_small. Qed.

Lemma succ_of_nat n : succ (of_nat n) = of_nat n.+1.
Proof.
apply: to_Z_inj; rewrite of_Z_spec succ_spec of_Z_spec.
by rewrite Zdiv.Zplus_mod_idemp_l -addn1 Nat2Z.inj_add.
Qed.
Lemma to_nat_succ x :
  (to_nat x).+1 < wBnat -> to_nat (succ x) = (to_nat x).+1.
Proof.
move=> Hx.
have := succ_of_nat (to_nat x); rewrite to_natK => ->.
by rewrite of_natK //.
Qed.
Lemma succK : cancel succ Uint63.pred.
Proof. move=> x; rewrite /succ /Uint63.pred; ring. Qed.
Lemma predK : cancel Uint63.pred succ.
Proof. move=> x; rewrite /succ /Uint63.pred; ring. Qed.

Lemma ltleSint x y : (x < y)%O -> (x + 1 <= y)%O.
Proof.
move=> /[dup] ltxy; rewrite ltEint -addn1 -to_nat1 -to_natD ?leEint //.
move: ltxy; rewrite to_nat1 addn1 ltEint => /leq_ltn_trans; apply.
exact: ltwBnat.
Qed.

Lemma ltSleint x y : (x < y + 1)%O -> (x <= y)%O.
Proof.
move=> /[dup] H; rewrite ltEint -addn1 -to_nat1 to_natD.
  by rewrite leq_add2r -leEint.
rewrite to_nat1 addn1 ltnNge; apply/negP => Habs.
suff {H} Heq : y + 1 = 0 by move: H; rewrite Heq ltEint to_nat0.
apply: to_nat_inj; rewrite to_nat0 to_natDE to_nat1.
suff -> : (to_nat y + 1)%N = wBnat by rewrite modnn.
rewrite addn1; apply anti_leq.
by rewrite ltwBnat Habs.
Qed.

Lemma int_neq0 x : x != 0 -> (1 <= x)%O.
Proof.
rewrite eq_sym => /negbTE neq0; have := le0int x.
rewrite Order.POrderTheory.le_eqVlt neq0 /= => /ltleSint.
by rewrite leEint to_natD // wBnatE.
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
by move: lt1x; rewrite leEint to_nat1.
Qed.

Lemma to_natM x y :
  to_nat x * to_nat y < wBnat -> to_nat (x * y) = (to_nat x * to_nat y)%N.
Proof. by move=> lt; rewrite to_natME modn_small. Qed.

Lemma to_nat_mod x y : to_nat (x mod y) = (to_nat x %% to_nat y)%N.
Proof. by rewrite mod_spec Z2Nat.inj_mod // mod_natE. Qed.
Lemma to_nat_div x y : to_nat (x / y) = (to_nat x %/ to_nat y)%N.
Proof. by rewrite div_spec Z2Nat.inj_div // div_natE. Qed.

End Int.


Section Overflow.

Implicit Type c : carry int.

Coercion overflow_to_int c := match c with | C0 i | C1 i => i end.
Definition overflow c := match c with | C0 _ => false | C1 _ => true end.
Definition succov c :=
  match c with | C0 i => succc i | C1 i => C1 (succ i) end.
Definition addov c1 c2 := match c1, c2 with
                          | C0 i, C0 j => i +c j
                          | C0 i, C1 j | C1 i, C0 j | C1 i, C1 j => C1 (i + j)
                          end.

Lemma succov_impl c :
  ~~ overflow (succov c) -> ~~ overflow c.
Proof. by case: c => [i |]. Qed.
Lemma succovE c : succov c = succ c :> int.
Proof.
case: c => [] i //=.
have:= succc_spec i; rewrite /interp_carry.
case: (succc i) => [i1 /= | i1] /(congr1 BinInt.Z.to_nat).
- rewrite Z2Nat.inj_add // add_natE addn1 => H.
  by apply: to_nat_inj; rewrite to_nat_succ // -H ltwBnat.
- rewrite !BinInt.Z.mul_1_l !Z2Nat.inj_add -?wBnatE // !add_natE.
  move/(congr1 (fun n : nat => n%:R%R : int)).
  rewrite !GRing.natrD GRing.natr1 -addn1 !GRing.natrD.
  rewrite /succ -!intDE !natrEint -to_nat1 !to_natK => <-.
  rewrite of_wBnat /=; ring.
Qed.

Lemma to_nat_succovE c :
  ~~ overflow (succov c) -> to_nat (succov c) = (to_nat c).+1.
Proof.
case: c => [i | //] /=.
have /= := succc_spec i; rewrite /interp_carry /overflow /overflow_to_int.
case: (succc i) => [i1|//] /(congr1 BinInt.Z.to_nat) -> _.
by rewrite Z2Nat.inj_add // to_nat1 add_natE addn1.
Qed.
Lemma addov_impl c1 c2 :
  ~~ overflow (addov c1 c2) -> ~~ overflow c1 /\ ~~ overflow c2.
Proof. by case: c1 c2 => []i1 []i2. Qed.

Lemma addovE c1 c2 : addov c1 c2 = c1 + c2 :> int.
Proof.
case: c1 c2 => [] i [] j //=.
have /= := addc_spec i j; rewrite /interp_carry /overflow /overflow_to_int.
case: (i +c j) => [r|r] /(congr1 BinInt.Z.to_nat).
  rewrite Z2Nat.inj_add // add_natE => H.
  by apply: to_nat_inj; rewrite to_natD // -H ltwBnat.
rewrite !BinInt.Z.mul_1_l !Z2Nat.inj_add -?wBnatE // !add_natE.
move=> /(congr1 (fun n => of_nat n)).
rewrite -!natrEint !GRing.natrD -!intDE.
by rewrite !natrEint of_wBnat !to_natK => <-; ring.
Qed.
Lemma to_nat_addovE c1 c2 :
  ~~ overflow (addov c1 c2) ->
  to_nat (addov c1 c2) = (to_nat c1 + to_nat c2)%N.
Proof.
case: c1 c2 => [] i [] j //=.
have /= := addc_spec i j; rewrite /interp_carry /overflow /overflow_to_int.
case: (i +c j) => [r|//] /(congr1 BinInt.Z.to_nat) -> _.
by rewrite Z2Nat.inj_add.
Qed.

End Overflow.


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
by rewrite {}IHs /= -(succ_subint1E ineq0) //= rev_cons -cats1 -catA cat1s.
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
