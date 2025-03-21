(** Native int is a well founded choice and type **)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Znat BinIntDef Uint63.

Require Import present cert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

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

Lemma wf_ltint : well_founded (<%O : rel int).
Proof.
apply: (wf_f int_to_natK _ wf_ltnat) => x y.
by rewrite int_ltE ltEnat.
Qed.
Definition sizelexi_int_wf := sizelexi_wf wf_ltint.
Definition check_convergence_intP fuel R :
  is_Ok (check_convergence <%O fuel R) -> convergent R :=
  check_convergenceP (@lt_sizelexi_stable _ int) sizelexi_int_wf
    (fuel := fuel) (R := R).

Theorem isopres_final : isopres present_entry present_final.
Proof.
have wfc : wfpres_cert present_entry cert by vm_cast_no_check (eq_refl true).
apply: (isopres_trans (@iso_final_pres _ present_entry cert wfc)).
apply: pres_irrelevance.
  by rewrite (pgen_final_pres wfc).
by rewrite (prelat_final_pres wfc).
Time Qed.

Fixpoint eqseq_int (s1 s2 : seq int) {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => if eqb x1 x2 then eqseq_int s1' s2' else false
  | _, _ => false
  end.
Lemma eqseq_intE : @eq_op (seq int) = eqseq_int.
Proof. by []. Qed.


Fixpoint prefix_int s1 s2 {struct s2} :=
  if s1 isn't x :: s1' then true else
  if s2 isn't y :: s2' then false else
    if eqb x y then prefix_int s1' s2' else false.
Lemma prefixE : @prefix int = prefix_int.
Proof. by []. Qed.

Definition drop_int := Eval compute in @drop int.     (* 7%   speedup ?? *)
Definition cat_int := Eval compute in @cat int.       (* 3.5% speedup ?? *)
Definition size_int := Eval compute in @seq.size int. (* 4%   speedup ?? *)

Fixpoint rewrites1_front_int (R : relat int) (u : seq int) :=
  if R is (r1, r2) :: R' then
    if prefix_int r1 u then Some (cat_int r2 (drop_int (size_int r1) u))
    else rewrites1_front_int R' u
  else None.
Lemma rewrites1_front_intE : @rewrites1_front int = rewrites1_front_int.
Proof. by []. Qed.
Definition rewrites1_front_int_fast := Eval compute in rewrites1_front_int.

Definition rewrites1_int  := (* Eval compute in 25% speedup ?? 25% slowdown ?? *)
  fun R : relat int => (fix rec (u : seq int) :=
                         if u is a :: u' then
                           if rewrites1_front_int_fast R u is Some u as res then res
                           else option_map (cons a) (rec u')
                         else rewrites1_front_int_fast R [::]).
Lemma rewrites1_intE : @rewrites1 int = rewrites1_int.
Proof. by []. Qed.

Fixpoint norfuel2_int R fuel u :=
  if fuel is fuel'.+1 then
    if rewrites1_int R u is Some u1 then
      let rec := norfuel2_int R fuel' u1 in
      if rec is (u2, false) then norfuel2_int R fuel' u2 else rec
    else (u, true)
  else (u, false).

Lemma norfuel2_intE : @norfuel2 int = norfuel2_int.
Proof. by []. Qed.

Definition all_spairs_rule_int (r1 r2 s1 s2 : seq int) :=
  [seq (r2 ++ drop (seq.size r1 - shift) s1, take shift r1 ++ s2) |
    shift <- iota 0 (seq.size r1) & prefix_int (drop shift r1) s1].
Definition all_spairs_int R :=
  flatten [seq all_spairs_rule_int r.1 r.2 s.1 s.2 | r <- R, s <- R].
Definition all_npairs_rule_int (r1 r2 s1 s2 : seq int) :=
  [seq (r2, take shift r1 ++ s2 ++ drop (shift + seq.size s1) r1) |
    shift <- iota 0 (seq.size r1 - seq.size s1).+1 &
      eqseq_int s1 (take (seq.size s1) (drop shift r1))].
Definition all_npairs_int R :=
  flatten [seq all_npairs_rule_int r.1 r.2 s.1 s.2 | r <- R, s <- R].
Lemma all_spairs_intE : @all_spairs int = all_spairs_int.
Proof. by []. Qed.
Lemma all_npairs_intE : @all_npairs int = all_npairs_int.
Proof. by []. Qed.

Definition eqbool b1 b2 := Eval compute in addb (~~ b1) b2.
Definition eqnor R fuel (p : word int * word int) :=
  let x1 := norfuel2_int R fuel p.1 in
  let x2 := norfuel2_int R fuel p.2 in
  if eqseq_int x1.1 x2.1 then eqbool x1.2 x2.2 else false.

Definition spair_confluence_dec_int fuel R :=
  if all (fun p => eqseq_int p.1 p.2) (all_npairs_int R) then
    let spairs := filter (fun p => ~~ eqseq_int p.1 p.2) (all_spairs_int R) in
    (* all (fun p => norfuel_int R fuel p.1 == norfuel_int R fuel p.2) spairs *)
    all (eqnor R fuel) spairs
  else false.
Lemma spair_confluence_dec_intE :
  @spair_confluence_dec int = spair_confluence_dec_int.
Proof. by []. Qed.

Definition all_pred_npairs_rule_int (p : seq int * seq int -> bool) (r1 r2 s1 s2 : seq int) :=
  let ss1 := seq.size s1 in
  all (fun shift =>
      if eqseq_int s1 (take ss1 (drop shift r1)) then
        p (r2, take shift r1 ++ s2 ++ drop (shift + ss1) r1)
      else true)
    (iota 0 (seq.size r1 - ss1).+1).

Lemma all_pred_npairs_rule_intE :
  @all_pred_npairs_rule int = all_pred_npairs_rule_int.
Proof. by rewrite /all_pred_npairs_rule eqseq_intE. Qed.

Definition all_pred_npairs_int (p : seq int * seq int -> bool) R :=
  all (fun r =>
    let r1 := r.1 in let r2 := r.2 in
    all (fun s => all_pred_npairs_rule_int p r1 r2 s.1 s.2) R) R.

Lemma all_pred_npairs_intE :
  @all_pred_npairs int = all_pred_npairs_int.
Proof. by rewrite /all_pred_npairs all_pred_npairs_rule_intE. Qed.

Definition all_pred_spairs_rule_int (p : seq int * seq int -> bool) (r1 r2 s1 s2 : seq int) :=
  let sr1 := seq.size r1 in
  all (fun shift =>
      if prefix_int (drop shift r1) s1 then
        p (r2 ++ drop (sr1 - shift) s1, take shift r1 ++ s2)
      else true)
    (iota 0 sr1).

Lemma all_pred_spairs_rule_intE :
  @all_pred_spairs_rule int = all_pred_spairs_rule_int.
Proof. by rewrite /all_pred_spairs_rule prefixE. Qed.

Definition all_pred_spairs_int (p : seq int * seq int -> bool) R :=
  all (fun r =>
    let r1 := r.1 in let r2 := r.2 in
    all (fun s => all_pred_spairs_rule_int p r1 r2 s.1 s.2) R) R.

Lemma all_pred_spairs_intE :
  @all_pred_spairs int = all_pred_spairs_int.
Proof. by rewrite /all_pred_spairs all_pred_spairs_rule_intE. Qed.

Definition spair_confluence_loop_int fuel R :=
  (all_pred_npairs_int (fun p => eqseq_int p.1 p.2) R) &&
  (all_pred_spairs_int (fun p =>
     if eqseq_int p.1 p.2 then true else eqnor R fuel p) R).

Lemma spair_confluence_loop_intE :
  @spair_confluence_loop int = spair_confluence_loop_int.
Proof.
rewrite /spair_confluence_loop all_pred_npairs_intE eqseq_intE.
by rewrite /eq_op /= eqseq_intE norfuel2_intE.
Qed.
