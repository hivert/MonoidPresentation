From Corelib Require Import Setoid.
From HB Require Import structures.
From Stdlib Require Import Znat BinIntDef Uint63 Ring Ring63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot all_order fingroup perm.

Import Order.TTheory.

Require Import int_seq array monoids present monpres enumnf inttrie.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.
Local Open Scope order_scope.

Section UniqMap.

Variables (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1).

Lemma uniq_map_indexE :
  uniq (map f s) -> forall x, x \in s -> index (f x) (map f s) = index x s.
Proof.
move=> f_uniq x /[dup] xins /(map_f f) fxinfs; apply/eqP.
rewrite -(nth_uniq (f x) _ _ f_uniq) ?index_mem ?size_map ?index_mem //.
by rewrite nth_index // (nth_map x) ?index_mem // nth_index.
Qed.
Lemma uniq_map_in_inj : uniq (map f s) -> {in s &, injective f}.
Proof.
move=> Huniq x y xin yin eqfxy; apply: (index_inj x xin yin).
by rewrite -!(uniq_map_indexE Huniq) ?eqfxy.
Qed.

End UniqMap.


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
Definition eq_intarray arf arg :=
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

Lemma eq_intarrayP (a1 a2 : array int) :
  length a1 = crd -> length a2 = crd -> default a1 = default a2 ->
  (a1 == a2) = (eq_intarray a1 a2).
Proof.
move=> /[dup] lena1; rewrite /eq_op /= /eq_array => -> -> ->.
by rewrite !eqxx /= andbT /eq_intarray; unlock.
Qed.
Lemma eq_atransfE f g :
  eq_intarray (atransf f) (atransf g) = (atransf f == atransf g).
Proof. by rewrite -eq_intarrayP // ?length_atransf ?default_atransf. Qed.
Lemma atransf_inj : injective atransf.
Proof. by move=> f g Heq; apply/ffunP => x; rewrite -!get_atransf_finTE Heq. Qed.
Lemma eq_atransfP f g : reflect (f = g) (eq_intarray (atransf f) (atransf g)).
Proof. by rewrite eq_atransfE; apply (iffP idP) => [/eqP/atransf_inj| ->]. Qed.

Lemma atransf1 : atransf 1%g = one_atransf.
Proof.
apply: array_ext; first 2 last.
- by rewrite default_atransf default_make_array.
- by rewrite length_atransf length_make_array.
rewrite length_atransf => i lti.
rewrite get_atransfE // ffunE finT_of_intK //.
by rewrite get_make_array // crd_le andbT.
Qed.

Lemma atransfM f g : atransf (g * f)%g = mul_atransf (atransf f) (atransf g).
Proof.
apply: array_ext; first 2 last.
- by rewrite default_atransf default_make_array.
- by rewrite length_atransf !length_make_array.
rewrite length_atransf // => i lti.
rewrite get_atransfE // get_make_array; last by rewrite crd_le andbT.
rewrite !get_atransfE //; last exact: le_int_of_finT.
by rewrite int_of_finTK /= !ffunE.
Qed.

Lemma atransf_prod (I : Type) (s : seq I) (f : I -> {transf T}) :
  atransf (\prod_(i <- s) f i)%g =
    foldl (fun r u => mul_atransf (atransf (f u)) r) one_atransf s.
Proof.
elim/last_ind: s => [| s sn IHs] /=.
  by rewrite big_nil atransf1.
by rewrite big_rcons /= foldl_rcons -{}IHs -atransfM.
Qed.

End FinType.


Module Test.
Section Test.

Definition N := 20.
Let Nnat := to_nat N.

Local Lemma crdE : to_nat N = #|'I_Nnat|.
Proof. by rewrite card_ord. Qed.
Local Lemma crd_le : N <= max_length.
Proof. by []. Qed.

Goal (1 * 1 = 1 :> {transf 'I_Nnat})%g.
Proof.
apply/(eq_atransfP ord0 crdE crd_le).
rewrite !(atransf1 ord0 crdE crd_le, atransfM ord0 crdE crd_le).
by vm_compute.
Qed.

Definition revN : {transf 'I_Nnat} := [ffun x => rev_ord x].
Definition revNar := atransf ord0 N revN.

Lemma revNarE : revNar = make_array 0 N (fun i => N - 1 - i).
Proof.
rewrite /revNar; apply: array_ext; first 2 last.
- by rewrite default_atransf.
- by rewrite [LHS](length_atransf _ crd_le) [RHS]length_make_array.
  (* Faster than   by rewrite length_atransf.
     or            rewrite (length_atransf ord0 crd_le revN).
   *)
rewrite length_atransf // => i lti.
rewrite get_atransfE // get_make_array; first last.
  by move: lti; rewrite -[i <? N]/(i < N) => -> /=.
rewrite ffunE /= /int_of_finT /= enum_rank_ord /= subSS; apply: to_nat_inj.
rewrite of_natK; first last.
  apply: (leq_trans (n := Nnat)); first by rewrite ltnS (leq_subr).
  by rewrite wBnatE.
rewrite /finT_of_int /= nth_enum_ord; first last.
  by rewrite /Nnat -ltEint -/N.
by rewrite to_natB //; apply: ltSleint.
Qed.

Goal (revN * revN = 1 :> {transf 'I_Nnat})%g.
Proof.
apply/(eq_atransfP ord0 crdE crd_le).
rewrite !(atransf1, atransfM) ?crdE // -/revNar revNarE.
by vm_compute.
Qed.

End Test.
End Test.

Require Import symmetricgroup4.

Module TestPerm.
Section TestPerm.

Definition N := 4.
Let Nnat := to_nat N.

Implicit Type (i j : int) (n m : nat) (r u v w : seq int) (p q : 'S_Nnat).

Local Lemma crdE : to_nat N = #|'I_Nnat|.
Proof. by rewrite card_ord. Qed.
Local Lemma crd_le : N <= max_length.
Proof. by []. Qed.

Local Notation atransf1 := (atransf1 _ crdE crd_le).
Local Notation atransfM := (atransfM _ crdE crd_le).
Local Notation atransf_inj := (atransf_inj crdE crd_le (x0 := ord0)).

Definition perm_to_array : {perm 'I_Nnat} -> array int :=
  (atransf ord0 N) \o perm_to_transf.
Lemma perm_to_array_inj : injective perm_to_array.
Proof. exact: (inj_comp atransf_inj (can_inj perm_to_transfK)). Qed.
Lemma perm_to_array1 : perm_to_array 1%g = one_atransf N.
Proof. by rewrite /perm_to_array /= gmulf1 atransf1. Qed.
Lemma perm_to_arrayM f g :
  perm_to_array (f * g)%g = mul_atransf N (perm_to_array g) (perm_to_array f).
Proof.
Proof. by rewrite /perm_to_array /= gmulfM atransfM /=. Qed.

Definition ord_array : array 'I_Nnat :=
  make_array ord0 N (fun i => inord (to_nat i)).
Lemma val_get_ord_array i : i < N -> \val ord_array.[i] = to_nat i.
Proof.
move=> ltiN; rewrite get_make_array ?ltiN //=.
by rewrite inordK //= -[X in (_ < X)%N]/Nnat -ltEint.
Qed.
Local Lemma get_ord_array (i : int) : ord_array.[i] = finT_of_int ord0 i.
Proof.
apply: val_inj => /=; case: (ltP i N) => [ltiN | leNi]; first last.
  rewrite get_out_of_bounds; first last.
    by rewrite length_make_array // ltbE ltNge leNi.
  rewrite default_make_array /finT_of_int nth_default //.
  by rewrite size_enum_ord -[X in (X <= _)%N]/Nnat -leEint.
by rewrite val_get_ord_array // /finT_of_int nth_enum_ord // -ltEint.
Qed.

Definition elemtr i : {perm 'I_Nnat} := tperm ord_array.[i] ord_array.[succ i].
Definition elemtra i : array int :=
  make_array 0 N (fun j => if j == i then i + 1
                           else if j == i + 1 then i else j).

Lemma elemtraE i : i < N - 1 -> perm_to_array (elemtr i) = elemtra i.
Proof.
move=> lti.
have lti1N: i + 1 < N.
  by move: lti => /ltleSint/le_lt_trans; apply.
apply: array_ext; first 2 last.
- by rewrite default_atransf default_make_array.
- by rewrite !length_make_array ?length_atransf.
rewrite length_atransf // => j /[!ltbE] ltjN.
rewrite get_atransfE // get_make_array ?ltjN //.
rewrite perm_to_transfE /elemtr !get_ord_array.
case: (altP (j =P i)) => [{ltjN j}->| neqji].
  by rewrite tpermL (finT_of_intK _ crdE).
case: (altP (j =P i + 1)) => [{ltjN j neqji}->| neqj1i].
  rewrite tpermR (finT_of_intK _ crdE) // inE.
  exact: (lt_trans lti).
rewrite tpermD ?(finT_of_intK _ crdE) //.
  move: neqji; apply contra => /eqP/(can_in_inj (finT_of_intK _ crdE)) -> //.
  by rewrite inE; exact: (lt_trans lti).
by move: neqj1i; apply contra => /eqP /(can_in_inj (finT_of_intK _ crdE)) <-.
Qed.

Lemma elemtr1_2 : ((elemtr 0) ^+ 2 = 1)%g.
Proof.
rewrite expg2.
apply: perm_to_array_inj; rewrite !(perm_to_arrayM, perm_to_array1) /=.
by rewrite !elemtraE.
Qed.
Lemma elemtr121_121 :
  (elemtr 0 * elemtr 1 * elemtr 0 = elemtr 1 * elemtr 0 * elemtr 1)%g.
Proof.
apply: perm_to_array_inj; rewrite !(perm_to_arrayM, perm_to_array1) /=.
by rewrite !elemtraE.
Qed.
Lemma elemtr13_31 :
  (elemtr 0 * elemtr 2 = elemtr 2 * elemtr 0)%g.
Proof.
apply: perm_to_array_inj; rewrite !(perm_to_arrayM, perm_to_array1) /=.
by rewrite !elemtraE.
Qed.

Definition aeval (r : seq int) : array int :=
  foldl (fun a i => mul_atransf N (elemtra i) a) (one_atransf N) r.
Definition is_rel (rr : seq int * seq int) :=
  eq_intarray N (aeval rr.1) (aeval rr.2).

Lemma default_aeval r : default (aeval r) = 0.
Proof.
rewrite /aeval; case/lastP: r => //= r rn.
by rewrite foldl_rcons default_make_array.
Qed.
Lemma length_aeval r : length (aeval r) = N.
Proof.
rewrite /aeval; case/lastP: r => //= r rn.
by rewrite foldl_rcons length_make_array.
Qed.

Lemma univmor_elemtr (r : seq int) :
  all (<%O^~ (N - 1)) r -> perm_to_array (univmor elemtr r) = aeval r.
Proof.
elim/last_ind: r => [|r rn IHr] /=.
  by rewrite univmor_nil perm_to_array1.
rewrite univmor_rcons perm_to_arrayM all_rcons => /andP[/elemtraE -> {}/IHr ->].
by rewrite /aeval foldl_rcons.
Qed.

Lemma satisfy_eltr (rels : relat int) :
  all_relwords rels (<%O^~ (N - 1)) -> satisfy rels elemtr = all is_rel rels.
Proof.
rewrite /is_rel => /allP /= Hr.
apply/satisfyP/allP => /= Hrel [r1 r2] /[dup]/Hr /= /andP[Hr1 Hr2] {}/Hrel /=.
  move/(congr1 perm_to_array) => /=.
  rewrite !univmor_elemtr //= => ->.
  by apply/allintP => i _; rewrite eqb_refl.
rewrite -eq_intarrayP ?default_aeval ?length_aeval // => /eqP Heq.
by apply: perm_to_array_inj; rewrite !univmor_elemtr.
Qed.

Lemma elemtr_S4_Moore : satisfy (prelat S4_Moore) elemtr.
Proof. by rewrite satisfy_eltr; vm_compute. Qed.

Lemma elemtr_S4_rws : satisfy (prelat S4_rws) elemtr.
Proof. by rewrite satisfy_eltr; vm_compute. Qed.

Let bound := 10%N.
Let all_perm_from_nf : seq {perm 'I_Nnat} :=
      [seq univmor elemtr w | w <- (enum_normal_trie S4_rws bound).1].
Let all_permarray_from_nf : seq (array int : eqType) :=
      [seq aeval w | w <- (enum_normal_trie S4_rws bound).1].

Lemma is_enum_normal_S4_rws :
  is_enum_normal S4_rws (enum_normal_trie S4_rws bound).1.
Proof.
have S4_rws_ok : all (<%O^~ max_length) (pgen S4_rws) by [].
exact: (enum_normal_trieP S4_rws_convergent S4_rws_ok).
Qed.

Lemma all_permarray_from_nf_uniq : uniq all_permarray_from_nf.
Proof. by vm_compute; unlock. Qed.
Lemma all_perm_from_nf_uniq : uniq all_perm_from_nf.
Proof.
rewrite -(map_inj_uniq perm_to_array_inj).
rewrite /all_perm_from_nf -map_comp.
set f := (X in map X _); set l := (X in map _ X).
suff /eq_in_map -> : {in l, f =1 aeval} by apply: all_permarray_from_nf_uniq.
rewrite {}/l {}/f => w win /=; apply: univmor_elemtr.
have:= is_enum_normal_S4_rws; rewrite /is_enum_normal => -[_ /(_ w)].
rewrite {}win /normalword_of => /andP[+ _]; apply: sub_all => x /=.
by move: x; apply/allP.
Qed.

Lemma size_nf_S4_rws : size (enum_normal_trie S4_rws bound).1 = 24%N.
Proof. by vm_compute. Qed.
Lemma all_perm_from_nfE : perm_eq all_perm_from_nf (enum 'S_Nnat).
Proof.
apply: uniq_perm.
- exact: all_perm_from_nf_uniq.
- exact: enum_uniq.
have /(_ (enum 'S_Nnat))[] // := (uniq_min_size all_perm_from_nf_uniq).
- by move=> x _; rewrite mem_enum inE.
- by rewrite -cardT card_Sn !size_map size_nf_S4_rws /=.
Qed.
Lemma in_enum_univmor_inj :
  {in (enum_normal_trie S4_rws bound).1 &, injective (univmor elemtr)}.
Proof. exact: (uniq_map_in_inj all_perm_from_nf_uniq). Qed.

Lemma mem_all_perm_from_nf p : p \in all_perm_from_nf.
Proof. by have /perm_mem -> := all_perm_from_nfE; rewrite mem_enum inE. Qed.

Theorem S4_rwsP : S4_rws \present 'S_4.
Proof.
apply: (Presentation (mgen := elemtr)) => [p /=| u v uin vin].
  have /mapP [w win eqw] := mem_all_perm_from_nf p.
  exists w; last by rewrite eqw.
  have:= is_enum_normal_S4_rws; rewrite /is_enum_normal => -[_ /(_ w)].
  by rewrite {}win /normalword_of => /andP[+ _].
split; first by move/(satisfy_univmor elemtr_S4_rws).
rewrite (equiv_normal_ofE S4_rws_convergent).
have univ_normal w :
     univmor elemtr w = univmor elemtr (normal_of S4_rws_convergent.2 w).
  apply: (satisfy_univmor elemtr_S4_rws).
  exact: equiv_normal_of.
rewrite (univ_normal u) (univ_normal v) {univ_normal}.
have normalofS4 (w : seq int) : w \in words_of S4_rws ->
                   normalword_of S4_rws (normal_of S4_rws_convergent.2 w).
  rewrite /normalword_of normal_ofP andbT.
  by rewrite (equiv_words_ofE (equiv_normal_of S4_rws_convergent.2 w)).
move/normalofS4: vin; move/normalofS4: uin => {normalofS4}.
move: (normal_of _ _) (normal_of _ _) => {}v {}u + + equnivmor.
have [_ mem_enumS4] := is_enum_normal_S4_rws.
rewrite !{}mem_enumS4 => uin vin.
rewrite -(nth_index_map [::] in_enum_univmor_inj uin).
rewrite -(nth_index_map [::] in_enum_univmor_inj vin).
by rewrite equnivmor.
Qed.

Corollary S4_MooreP : S4_Moore \present 'S_4.
Proof. exact: (isopresent S4_rwsP isopres_S4). Qed.

End TestPerm.
End TestPerm.
