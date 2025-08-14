From HB Require Import structures.
From Coq Require Import Znat BinIntDef Uint63 PString.
From mathcomp Require Import all_ssreflect.


Require Import int_seq monoids present.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Lemma isSome_omap (T U : Type) (f : T -> U) (x : option T) :
  isSome (omap f x) = isSome x.
Proof. by case: x. Qed.


Implicit Types (a b c : char63) (x y : int) (s t u v : string).

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

Fact strcat_assoc : associative PrimString.cat.
Proof. by move=> s t u; rewrite cat_assoc. Qed.
HB.instance Definition _ := isMonoid.Build string
                              strcat_assoc cat_empty_l cat_empty_r.

Lemma lengthE s : to_nat (length s) = size (to_list s).
Proof. by rewrite length_spec. Qed.

Lemma length_max s : (length s <= max_length)%O.
Proof. by rewrite leEint -leintbE; apply/lebP; exact: valid_length. Qed.

Definition takes s i := sub s 0 i.
Definition drops s i := sub s i (length s).

Lemma takesE s i : to_list (takes s i) = take (to_nat i) (to_list s).
Proof. by rewrite sub_spec List.skipn_O firstnE. Qed.
Lemma dropsE s i :
  to_list (drops s i) = drop (to_nat i) (to_list s).
Proof.
by rewrite sub_spec skipnE firstnE take_oversize // size_drop lengthE leq_subr.
Qed.

Lemma drops0E s : drops s 0 = s.
Proof. by apply: (can_inj of_to_list); rewrite dropsE drop0. Qed.
Lemma takes0E s : takes s 0 = ""%pstring.
Proof. by apply: (can_inj of_to_list); rewrite takesE take0. Qed.

Definition str_prefix u v := sub v 0 (length u) == u.
Lemma str_prefixE u v : str_prefix u v = prefix (to_list u) (to_list v).
Proof.
by rewrite /str_prefix -(eqtype.inj_eq to_list_inj) takesE lengthE prefixE.
Qed.

Section Rewrite.

Variable R : seq (string * string).
Hypothesis Hdecr : all (fun r => (length r.2 <= length r.1)%O) R.

Fixpoint str_rewrites1_front R u :=
  if R is (r1, r2) :: R' then
    if str_prefix r1 u then
      Some (PrimString.cat r2 (sub u (length r1) (length u)))
    else
      str_rewrites1_front R' u
  else None.
Lemma str_rewrites1_frontE u :
  omap to_list (str_rewrites1_front R u) =
    rewrites1_front [seq (to_list r.1, to_list r.2) | r <- R] (to_list u).
Proof.
elim: R Hdecr => [| [r1 r2] S IHS] //= /andP[lenr] {}/IHS <-.
rewrite str_prefixE; case Hpref: prefix => //=.
rewrite cat_spec; congr Some.
rewrite sub_spec !firstnE !skipnE (lengthE r1).
have lesz : size (drop (size (to_list r1)) (to_list u)) <= to_nat (length u).
  by rewrite size_drop lengthE leq_subr.
rewrite !take_oversize // {lesz} size_cat size_drop.
have:= length_max u; rewrite leEint => /(leq_trans _); apply.
move: lenr; rewrite leEint !lengthE.
move/size_prefix/subnKC : Hpref => {2}<-.
by rewrite leq_add2r.
Qed.
Lemma length_rewrites1_frontE u :
  omap (fun s => to_nat (length s)) (str_rewrites1_front R u) =
    omap size (rewrites1_front [seq (to_list r.1, to_list r.2) | r <- R] (to_list u)).
Proof.
rewrite -str_rewrites1_frontE -[RHS]omap_comp; apply eq_omap => s /=.
by rewrite lengthE.
Qed.
Lemma length_rewrites1_front_leq u v :
  str_rewrites1_front R u = Some v -> (length v <= length u)%O.
Proof.
move=> H.
rewrite leEint !lengthE.
have:= length_rewrites1_frontE u.
rewrite -str_rewrites1_frontE H /= => -[] eq.
have := str_rewrites1_frontE u.
rewrite H => /esym/rewrites1_frontP/rewrites_frontP[/= suf [s1 s2] /= -> ->].
case/mapP => /= -[r1 r2] /[swap] /= -[{s1}-> {s2}->]/=.
move/(allP Hdecr) => /=.
by rewrite leEint !size_cat leq_add2r !lengthE.
Qed.

Definition str_rewrites1_at R u i :=
  omap (PrimString.cat (takes u i)) (str_rewrites1_front R (drops u i)).

Lemma str_rewrites1_at0E u :
  str_rewrites1_at R u 0 = str_rewrites1_front R u.
Proof.
rewrite /str_rewrites1_at; apply: (inj_omap (can_inj of_to_list)).
rewrite -[LHS]omap_comp drops0E takes0E.
by apply: eq_omap => s /=; rewrite cat_empty_l.
Qed.
Lemma str_rewrites1_at_drop u n i :
  to_nat n + to_nat i <= to_nat (length u) ->
  str_rewrites1_at R (drops u n) i =
    omap (drops^~ n) (str_rewrites1_at R u (n + i)).
Proof.
move=> lesum.
have ltsum : to_nat n + to_nat i < BinInt.Z.to_nat wB.
  apply (leq_ltn_trans lesum).
  rewrite length_spec.
  have /leP/leq_ltn_trans := (to_list_length u); apply.
  rewrite /max_length; apply/ltP.
  by rewrite -Z2Nat.inj_lt.
rewrite /str_rewrites1_at.
have -> : drops (drops u n) i = drops u (n + i).
  apply: (can_inj of_to_list); rewrite !dropsE drop_drop.
  by rewrite (to_natD _ _ ltsum) addnC.
case H: str_rewrites1_front => [s|//]; congr Some.
move/length_rewrites1_front_leq : H.
rewrite leEint !lengthE !dropsE size_drop (to_natD _ _ ltsum) => ltl.
apply: (can_inj of_to_list); rewrite !dropsE !cat_spec !firstnE.
rewrite !(takesE, dropsE).
rewrite !take_drop (to_natD _ _ ltsum).
rewrite take_oversize; first last.
  rewrite size_cat size_drop size_take_min (addnC (to_nat i)).
  have:= lesum; rewrite lengthE => /minn_idPl ->.
  rewrite addKn.
  have:= ltl; rewrite subnDA -(leq_add2l (to_nat i)) => /leq_trans; apply.
  rewrite addnC subnK.
    apply (leq_trans (leq_subr _ _)).
    by rewrite -lengthE -leEint length_max.
  rewrite -(leq_add2l (to_nat n)) -lengthE subnKC; first exact: lesum.
  exact: (leq_trans (leq_addr _ _) lesum).
rewrite (take_oversize (n := to_nat max_length)).
  rewrite [X in take X]addnC.
  rewrite drop_cat.


  
Lemma str_rewrites1_atE u i :
  (i <= length u)%O ->
  omap to_list (str_rewrites1_at R u i) =
    omap (cat (take (to_nat i) (to_list u)))
      (rewrites1_front [seq (to_list r.1, to_list r.2) | r <- R]
         (drop (to_nat i) (to_list u))).
Proof.
rewrite /str_rewrites1_at -dropsE => leiu.
rewrite -str_rewrites1_frontE.
case Hrew : (str_rewrites1_front _ _) => [s|] //=; congr Some.
move/length_rewrites1_front_leq: Hrew => lens.
rewrite cat_spec takesE firstnE take_oversize //.
rewrite size_cat size_take_min -!lengthE.
have:= leiu; rewrite leEint => /minn_idPl ->.
apply: (leq_trans (n := to_nat (length u))); first last.
  rewrite -(leEint (length u) max_length) /Order.le /=.
  by have := valid_length u; rewrite -leb_spec.
move: lens; rewrite leEint lengthE.
rewrite (lengthE (sub _ _ _)) dropsE // size_drop.
rewrite -(leq_add2l (to_nat i)) => /leq_trans; apply.
by rewrite subnKC -(lengthE u) // -leEint.
Qed.

Fixpoint str_rewrites1_loop u n i :=
    if n is n'.+1 then
      let rec := str_rewrites1_at R u i in
      if rec then rec else str_rewrites1_loop u n' (i + 1)
    else None.
Definition str_rewrites1 u := str_rewrites1_loop u (to_nat (length u)).+1 0.

Lemma str_rewrites1E u :
  omap to_list (str_rewrites1 u) =
    rewrites1 [seq (to_list r.1, to_list r.2) | r <- R] (to_list u).
Proof.
rewrite /str_rewrites1 lengthE; move Hl : (to_list u) => l /=.
rewrite -(isSome_omap to_list) fun_if.
rewrite str_rewrites1_at0E /= str_rewrites1_frontE Hl.
elim: l u Hl => [|l0 l IHl] u eql0l /=.
  by case: rewrites1_front.
case: rewrites1_front => [res|]//=.
have {}/IHl <- : to_list (drops u 1) = l by rewrite dropsE eql0l /= drop0.
rewrite -(isSome_omap to_list) fun_if.
rewrite str_rewrites1_atE /=; last by rewrite leEint lengthE eql0l.
rewrite eql0l /= drop0 isSome_omap.
case: rewrites1_front => [res|] /=; first by rewrite take0.
have -> : option_map (cons l0) =1 omap (cons l0) by case.
rewrite -[RHS](omap_comp (to_list) (cons l0)).
rewrite -[2]/(1 + 1); move: {2 4}1 => i.
elim: l u eql0l => [// | l1 l IHl]//= u equ.
rewrite isSome_omap.

case: (size l) => // n.
rewrite /option_map. 
/  rewrite /=.
  have /str_rewrites1_atE : (0 <= length u)%O by rewrite leEint.
  rewrite eql0l take0 drop0 /=.
  by case: (str_rewrites1_at R u 0) => [res|] ->; case: rewrites1_front.






  
move Hl : (to_nat (length u))
Fixpoint str_norfuel2 fuel u :=
  if fuel is fuel'.+1 then
    if str_rewrites1 u is Some u1 then
      let rec := str_norfuel2 fuel' u1 in
      if rec is (u2, false) then str_norfuel2 fuel' u2 else rec
    else (u, true)
  else (u, false).

End Rewrite.

Local Open Scope pstring_scope.

Definition Sys := [::
                   ("abababab", "c");
                   ("abc", "cab");
                   ("babaaa", "ca");
                   ("babaac", "cc");
                   ("ababaca", "caaa");
                   ("ababacc", "caac")].

Eval compute in str_rewrites1 Sys "bcaabacbabbacaaabcccbba".
Eval compute in str_rewrites1 Sys "bcaabacbabbacaacabccbba".
Eval compute in str_rewrites1 Sys "bcaabacbabbacaaccabcbba".
Eval compute in str_rewrites1 Sys "bcaabacbabbacaacccabbba".
Eval compute in str_rewrites1 Sys "bcaabacbabbacaacccabbba".
Eval compute in str_norfuel2 Sys 10 "aabcaabacbabbacaaabcccbba".

Eval compute in str_rewrites1
                  [::
                    ("aabaaaba", "c");
                    ("aabac", "caaba");
                    ("bababba", "ca");
                    ("bababbc", "cc");
                    ("bababca", "cababba");
                    ("bababcc", "cababbc");
                    ("aabaaabc", "cabaaaba");
                    ("aabaaaca", "cbabba");
                    ("aabaaacc", "cbabbc")]
                  "bcaabacbabbacaaabcccbba".



(* Check string : monoidType.

Eval compute in ("aaaa"%pstring * 1 * "bbb"%pstring)%M.


Time Definition lnat := Eval native_compute in
    [seq ncons i i [:: 1 : nat] | i <- iota 0 250].
Time Definition lint := Eval native_compute in
    [seq [seq nat_to_int i | i <- l] | l <- lnat].
Time Definition lstr := Eval native_compute in
    [seq of_list [seq 64 + i | i <- l] | l <- lint].

Time Eval native_compute in count (fun l => size l == (4 : nat))
                              [seq p ++ q | p <- lnat, q <- lnat].
Time Eval native_compute in count (fun l => size l == (4 : nat))
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
