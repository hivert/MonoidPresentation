From Coq Require Import Znat BinIntDef Uint63.
From mathcomp Require Import all_ssreflect.

Require Import int_seq wfsizelexi present rewcert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(** Native int is a well founded choice and ordered type **)
Lemma wf_ltint : well_founded (<%O : rel int).
Proof.
apply: (wf_f _ wf_ltnat) => x y.
by rewrite ltintE ltEnat; apply.
Qed.
Definition sizelexi_int_wf := sizelexi_wf wf_ltint.
Definition check_convergence_intP fuel R :
  is_Ok (check_convergence R (rewrites1 _) <%O fuel) -> convergent R :=
  check_convergenceP (rewrites1P _) lt_sizelexi_stable sizelexi_int_wf
    (T := int) (fuel := fuel) (R := R).

Fixpoint eqseq_int (s1 s2 : seq int) {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => if x1 =? x2 then eqseq_int s1' s2' else false
  | _, _ => false
  end.
Lemma eqseq_intE : @eq_op (seq int) = eqseq_int.
Proof. by []. Qed.


Fixpoint prefix_int s1 s2 {struct s2} :=
  if s1 isn't x :: s1' then true else
  if s2 isn't y :: s2' then false else
    if x =? y then prefix_int s1' s2' else false.
Lemma prefix_intE : @prefix int = prefix_int.
Proof. by []. Qed.

Definition drop_seq_int := Eval compute in @drop int.     (* 7%   speedup ?? *)
Definition cat_seq_int := Eval compute in @cat int.       (* 3.5% speedup ?? *)
Definition size_seq_int := Eval compute in @size int.     (* 4%   speedup ?? *)

Fixpoint rewrites1_front_int (R : relat int) (u : seq int) :=
  if R is (r1, r2) :: R' then
    if prefix_int r1 u then Some (cat_seq_int r2 (drop_seq_int (size_seq_int r1) u))
    else rewrites1_front_int R' u
  else None.
Lemma rewrites1_front_intE : @rewrites1_front int = rewrites1_front_int.
Proof. by []. Qed.
Definition rewrites1_front_int_fast := Eval compute in rewrites1_front_int.

Definition rewrites1_int (R : relat int) :=
  fix aux (u : seq int) :=
    if rewrites1_front_int_fast R u is Some u as res then res
    else if u is a :: u' then
      match aux u' with Some v => Some (cons a v) | None => None end
    else None.
Lemma rewrites1_intE R : @rewrites1 int R = rewrites1_int R.
Proof. by []. Qed.

Definition norfuel2_int R :=
  fix nor fuel u :=
    if fuel is fuel'.+1 then
      if rewrites1_int R u is Some u1 then
        let rec := nor fuel' u1 in
        if rec is (u2, false) then nor fuel' u2 else rec
      else (u, true)
    else (u, false).

Lemma norfuel2_intE R : norfuel2 (rewrites1_int R) = norfuel2_int R.
Proof. by []. Qed.

Definition all_spairs_rule_int (r1 r2 s1 s2 : seq int) :=
  [seq (r2 ++ drop (size r1 - shift) s1, take shift r1 ++ s2) |
    shift <- iota 0 (size r1) & prefix_int (drop shift r1) s1].
Definition all_spairs_int R :=
  flatten [seq all_spairs_rule_int r.1 r.2 s.1 s.2 | r <- R, s <- R].
Definition all_npairs_rule_int (r1 r2 s1 s2 : seq int) :=
  [seq (r2, take shift r1 ++ s2 ++ drop (shift + size s1) r1) |
    shift <- iota 0 (size r1 - size s1).+1 &
      eqseq_int s1 (take (size s1) (drop shift r1))].
Definition all_npairs_int R :=
  flatten [seq all_npairs_rule_int r.1 r.2 s.1 s.2 | r <- R, s <- R].
Lemma all_spairs_intE : @all_spairs int = all_spairs_int.
Proof. by []. Qed.
Lemma all_npairs_intE : @all_npairs int = all_npairs_int.
Proof. by []. Qed.

Definition eqbool b1 b2 := Eval compute in addb (~~ b1) b2.
Definition eqnor R fuel (p1 p2 : word int) :=
  let x1 := norfuel2_int R fuel p1 in
  let x2 := norfuel2_int R fuel p2 in
  eqseq_int x1.1 x2.1.

Definition all_tr {T} (p : T -> bool) :=
  fix aux (s : seq T) :=
    match s with
    | nil => true
    | cons x s' => if p x then aux s' else false
    end.

Lemma all_trE : @all = @all_tr.
Proof. by []. Qed.

Definition spair_confluence_dec_int R fuel :=
  if all_tr (fun p => eqseq_int p.1 p.2) (all_npairs_int R) then
    let spairs := filter_rev_tr
                    (fun p => ~~ eqseq_int p.1 p.2) (all_spairs_int R) in
    (* all (fun p => norfuel_int R fuel p.1 == norfuel_int R fuel p.2) spairs *)
    all_tr (fun p => eqnor R fuel p.1 p.2) spairs
  else false.
Lemma spair_confluence_dec_intE R :
  spair_confluence_dec R (rewrites1_int R) = spair_confluence_dec_int R.
Proof. by []. Qed.

Section WordRel.

Implicit Types r s : seq int.
Variable wrel : seq int -> seq int -> bool.

Definition all_pred_npairs_rule_int r1 r2 s1 s2 :=
  let ss1 := size s1 in
  all_tr (fun shift =>
      if prefix_int s1 (drop shift r1) then
        wrel r2 (take shift r1 ++ s2 ++ drop (shift + ss1) r1)
      else true)
    (iota 0 (size r1 - ss1).+1).

Definition all_pred_npairs_int R :=
  all_tr (fun pa => let r1 := pa.1 in let r2 := pa.2 in
    all_tr (fun pb => all_pred_npairs_rule_int r1 r2 pb.1 pb.2) R) R.

Definition all_pred_spairs_rule_int r1 r2 s1 s2 :=
  let sr1 := size r1 in
  all_tr (fun shift =>
      if prefix_int (drop shift r1) s1 then
        wrel (r2 ++ drop (sr1 - shift) s1) (take shift r1 ++ s2)
      else true)
    (iota 0 sr1).

Definition all_pred_spairs_int R :=
  all_tr (fun pa => let r1 := pa.1 in let r2 := pa.2 in
    all_tr (fun pb => all_pred_spairs_rule_int r1 r2 pb.1 pb.2) R) R.

End WordRel.

Definition spair_confluence_loop_int R fuel :=
  (all_pred_npairs_int eqseq_int R) &&
  (all_pred_spairs_int (fun p1 p2 =>
     if eqseq_int p1 p2 then true else eqnor R fuel p1 p2) R).

Lemma spair_confluence_loop_intE R :
  spair_confluence_loop R (rewrites1_int R) = spair_confluence_loop_int R.
Proof. by []. Qed.
