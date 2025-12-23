From Corelib Require Import Setoid.
From HB Require Import structures.
From Stdlib Require Import Znat BinIntDef Uint63 Ring Ring63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot all_order.

Import Order.TTheory.

Require Import int_seq array monoids.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.
Local Open Scope order_scope.


Section FinType.

Variables (T : finType) (x0 : T) (crd : int).
Implicit Types (i j : int) (x y : T) (f g : {transf T}).

Hypothesis crdE : to_nat crd = #|T|.
Hypothesis crd_le : crd <= max_length.

Local Lemma crdWb : #|T| < wBnat.
Proof.
rewrite -crdE.
apply: (leq_ltn_trans _ lt_max_lenght_wB).
by rewrite -leEint.
Qed.
Hint Resolve crdWb : core.

Definition int_of_finT x := of_nat (enum_rank x).
Definition finT_of_int i := nth x0 (enum T) (to_nat i).

Lemma int_of_finTK : cancel int_of_finT finT_of_int.
Proof.
rewrite /int_of_finT /finT_of_int => x.
by rewrite of_natK ?(ltn_trans (ltn_ord _) crdWb) // nth_enum_rank.
Qed.
Lemma finT_of_intK : {in < crd, cancel finT_of_int int_of_finT}.
Proof.
rewrite /int_of_finT /finT_of_int => /= i.
rewrite inE ltEint crdE => lti.
by rewrite -[to_nat i]/(\val (Ordinal lti)) -enum_val_nth enum_valK /= to_natK.
Qed.
Lemma le_int_of_finT x : int_of_finT x < crd.
Proof. by rewrite /int_of_finT ltEint crdE of_natK // (ltn_trans _ crdWb). Qed.

Definition transfun_int f := int_of_finT \o f \o finT_of_int.
Definition atransf f := locked (make_array 0 crd (transfun_int f)).
Definition one_atransf := make_array 0 crd id.
Definition eq_atransf arf arg :=
  allint (fun i => PrimInt63.eqb arf.[i] arg.[i]) 0 crd.
Definition mul_atransf arf arg := make_array 0 crd (fun i => arf.[arg.[i]]).

Lemma atransfE f : atransf f = make_array 0 crd (transfun_int f).
Proof. by rewrite /atransf; unlock. Qed.
Lemma length_atransf f : length (atransf f) = crd.
Proof. by rewrite atransfE length_make_array. Qed.
Lemma default_atransf f : default (atransf f) = 0.
Proof. by rewrite atransfE default_make_array. Qed.
Lemma get_atransf_finTE f x : finT_of_int (atransf f).[int_of_finT x] = f x.
Proof.
rewrite atransfE get_make_array; last by rewrite le_int_of_finT crd_le.
by rewrite /transfun_int /= !int_of_finTK.
Qed.
Lemma get_atransfE f i :
  i < crd -> (atransf f).[i] = int_of_finT (f (finT_of_int i)).
Proof. by move=> lti; rewrite atransfE get_make_array ?lti ?crd_le. Qed.

Lemma eq_atransfE f g :
  eq_atransf (atransf f) (atransf g) = (atransf f == atransf g).
Proof.
rewrite /eq_op /= /eq_array !length_atransf !default_atransf !eqxx /= andbT.
by unlock.
Qed.
Lemma atransf_inj : injective atransf.
Proof. by move=> f g Heq; apply/ffunP => x; rewrite -!get_atransf_finTE Heq. Qed.
Lemma eq_atransfP f g : reflect (f = g) (eq_atransf (atransf f) (atransf g)).
Proof. by rewrite eq_atransfE; apply (iffP idP) => [/eqP/atransf_inj| ->]. Qed.

Lemma atransf1 : atransf 1%g = one_atransf.
Proof.
apply: array_ext.
- by rewrite length_atransf length_make_array.
- rewrite length_atransf => i lti.
  rewrite get_atransfE // ffunE finT_of_intK //.
  by rewrite get_make_array // crd_le andbT.
- by rewrite default_atransf default_make_array.
Qed.

Lemma atransfM f g : atransf (f * g)%g = mul_atransf (atransf f) (atransf g).
Proof.
apply: array_ext.
- by rewrite length_atransf !length_make_array.
- rewrite length_atransf // => i lti.
  rewrite get_atransfE // get_make_array; last by rewrite crd_le andbT.
  rewrite !get_atransfE //; last exact: le_int_of_finT.
  by rewrite int_of_finTK /= ffunE.
- by rewrite default_atransf default_make_array.
Qed.

End FinType.


Module Test.
Section Test.

Definition N := 4.

Local Lemma crdE : to_nat N = #|'I_4|.
Proof. by rewrite /N card_ord. Qed.
Local Lemma crd_le : N <= max_length.
Proof. by []. Qed.

Goal (1 * 1 = 1 :> {transf 'I_4})%g.
Proof.
apply/(eq_atransfP ord0 crdE crd_le).
rewrite !(atransf1 ord0 crdE crd_le, atransfM ord0 crdE crd_le).
by vm_compute.
Qed.

Definition rev4 : {transf 'I_4} := [ffun x => rev_ord x].
Definition rev4ar := atransf ord0 N rev4.

Lemma rev4arE : rev4ar = make_array 0 N (fun i => 3 - i).
Proof.
apply: array_ext.
- by rewrite length_atransf.
- rewrite length_atransf // => i lti.
  rewrite get_atransfE // get_make_array; first last.
    by move: lti; rewrite -[i <? N]/(i < N) => -> /=.
  rewrite ffunE /= /int_of_finT /= enum_rank_ord /= subSS; apply: to_nat_inj.
  rewrite of_natK; first last.
    apply: (leq_trans (n := 4)); first by rewrite ltnS (leq_subr).
    by rewrite wBnatE.
  rewrite /finT_of_int /= nth_enum_ord; first last.
    by rewrite -[4%N]/(to_nat 4) -ltEint -/N.
  by rewrite to_natB //; apply: ltSleint.
- by rewrite default_atransf.
Qed.

Goal (rev4 * rev4 = 1 :> {transf 'I_4})%g.
Proof.
apply/(eq_atransfP ord0 crdE crd_le).
rewrite !(atransf1, atransfM) ?crdE // -/rev4ar rev4arE.
by vm_compute.
Qed.

End Test.
End Test.
