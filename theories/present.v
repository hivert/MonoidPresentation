(** * Monoid Presentations *)
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
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq eqtype
  choice path bigop.


Require Import monoids factor well_founded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation "'{' 'rewmorph' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'rewmorph'  U  ->  V }").
Reserved Notation "'{' 'presmorph' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'presmorph'  U  ->  V }").
Reserved Notation "x '~>' y" (at level 0, format "x '~>' y").
Reserved Notation "x '~>*' y" (at level 0, format "x '~>*' y").

#[warning="-postfix-notation-not-level-1"]
Reserved Notation "x = y %[mod e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %[mod  e ] ']'").


Lemma expn_non2 n : 2 ^ n > 0.
Proof. by case: n => // n; apply: (leq_trans _ (ltn_expl _ _)). Qed.


(* A tail recursive reverse filter for large lists *)
Section FilterRevTr.

Context {T : Type}.
Implicit Types (s : seq T) (a : pred T).

Definition filter_rev_tr a := (* filter_rev is a MC lemma *)
  let aux := fix aux (acc s : seq T) : seq T :=
    match s with
    | [::] => acc
    | x :: s' => if a x then aux (x :: acc) s' else aux acc s'
    end in
  aux nil.

Lemma filter_rev_trE a s : filter_rev_tr a s = rev (filter a s).
Proof.
rewrite /filter_rev_tr -[RHS](cats0); elim: s [::] => [|s0 s IHs] acc //=.
rewrite !{}IHs; case: (a s0) => //.
by rewrite rev_cons -cats1 -catA cat1s.
Qed.

End FilterRevTr.


(* Relation words of a presentation *)
Section Defs.

Variable (Alph : choiceType).  (* monoidType inherits from choice *)

Definition word := seq Alph.
Definition relat := seq (word * word).

Implicit Types (R : relat) (u v w x y : word) (p : word * word).

Definition relwords R :=
  let fix aux accu R :=
  if R is (r1, r2) :: R' then aux (r1 :: r2 :: accu) R' else accu
  in aux [::] R.

Lemma relwordsP R w :
  reflect (exists2 r : word * word, r \in R & (w == r.1) || ((w == r.2)))
    (w \in relwords R).
Proof.
rewrite /relwords /=; set aux := (X in w \in X [::] R).
suff auxP (accu : seq word) : reflect
    (w \in accu \/ exists2 r, r \in R & (w == r.1) || ((w == r.2)))
    (w \in aux accu R) by apply (iffP (auxP _)); [case | right].
apply (iffP idP) => /=.
- elim: R accu => [|[r1 r2] R IHR] //= accu; first by left.
  move=> {}/IHR [| [[s1 s2] sinR /= ws]].
  + rewrite !inE => /or3P[/eqP {w}->|/eqP {w}->|].
    * by right; exists (r1, r2); rewrite ?inE ?eqxx.
    * by right; exists (r1, r2); rewrite ?inE ?eqxx ?orbT.
    * by left.
  + by right; exists (s1, s2); rewrite //= inE sinR orbT.
- elim: R accu => [|[r1 r2] R IHR] //= accu; first by case=> // -[].
  case=> [winaccu|].
    by apply: IHR; left; rewrite !inE winaccu !orbT.
  case=> -[s1 s2] /= sin ws; apply: IHR.
  move: sin ws; rewrite inE => /orP[/eqP[-> ->] eqw| sinR eqw].
    by left; rewrite !inE orbA eqw.
  by right; exists (s1, s2).
Qed.
Lemma mem_relwords R u v :
  (u, v) \in R -> (u \in relwords R) && (v \in relwords R).
Proof.
move=> inR; apply/andP.
by split; apply/relwordsP; exists (u, v); rewrite //= eqxx ?orbT.
Qed.

(* All relations words verify a predicate *)
Definition all_relwords R (P : pred Alph) :=
  all (fun p => all P p.1 && all P p.2) R.
Lemma all_relwordsE R (P : pred Alph) :
  all_relwords R P = all (all P) (relwords R).
Proof.
rewrite /all_relwords; apply/allP/allP => /= [inR w | inR [r1 r2] /=].
  by case/relwordsP => -[r1 r2] /inR /= /andP[allr1 allr2] /orP[] /eqP->.
by case/mem_relwords/andP => /inR-> /inR->.
Qed.


Section RelationsTerminology.

(* Relations on words, in Prop for the purpose of this development *)
Variable RP : word -> word -> Prop.

(* The relations we consider are congruences *)
Definition reflexivep := forall u, RP u u.
Definition symmetricp := forall u v, RP u v -> RP v u.
Definition transitivep := forall u v w, RP u v -> RP v w -> RP u w.
Definition stablep :=
  forall a b1 b2 c, RP b1 b2 -> RP (a ++ b1 ++ c) (a ++ b2 ++ c).
Definition rewcongrp := [/\ reflexivep, transitivep & stablep].
Definition congruencep := [/\ reflexivep, transitivep, stablep & symmetricp].

Lemma stable_cat :
  transitivep -> stablep ->
  forall a1 a2 b1 b2 , RP a1 a2 -> RP b1 b2 -> RP (a1 ++ b1) (a2 ++ b2).
Proof.
move=> trans stable a1 a2 b1 b2 R1 R2.
have:= stable [::] _ _ b1 R1; rewrite !cat0s => /trans; apply.
by have:= stable a2 _ _ [::] R2; rewrite !cats0.
Qed.

End RelationsTerminology.


(* A rewrite rule is a pair of words, the first being the lhs of the rw rule,
   a rewrite system is a list of rewrite rules. *)

(* rewrites_front_spec R u v holds when u rewrites into v by applying a rw rule
   in R to a prefix of u. *)
Variant rewrites_front_spec R u v : Prop :=
  RewritesFront : forall (suf : word) (rule : word * word),
      u = rule.1 ++ suf -> v = rule.2 ++ suf -> rule \in R
               -> rewrites_front_spec R u v.

(* rewrites_spec R u v holds when a rw rule in R applies rewrite u into v by
   applying a rule in R to an arbitrary subword of u *)
Variant rewrites_spec R u v : Prop :=
  Rewrites : forall (pre suf : word) (rule : word * word),
      u = pre ++ rule.1 ++ suf -> v = pre ++ rule.2 ++ suf -> rule \in R
               -> rewrites_spec R u v.

(* Produces the list of all words v than can be obtained by rewriting a prefix
   of u with a (single) rule in R *)
Fixpoint rewrites_front R u : seq word :=
  if R is (r1, r2) :: R' then
    if prefix r1 u then (r2 ++ drop (size r1) u) :: rewrites_front R' u
    else rewrites_front R' u
  else [::].

(* Produces the list of all words v than can be obtained by rewriting
   u with a (single) rule in R *)
Fixpoint rewrites R u :=
  if u is a :: u'
  then (rewrites_front R u) ++ [seq a :: v | v <- rewrites R u']
  else rewrites_front R [::].

Lemma rewrites_front_spec_cons R u v r1 r2:
  rewrites_front_spec R u v -> rewrites_front_spec ((r1, r2) :: R) u v.
Proof.
case=> suf [s1 s2] /= {u}->{v}-> sinR.
by exists suf (s1, s2) => //=; rewrite inE sinR orbT.
Qed.
Lemma rewrites_front_specP R u v pre :
  rewrites_front_spec R u v -> rewrites_spec R (pre ++ u) (pre ++ v).
Proof. by case=> suf r {u}->{v}-> rinR; exists pre suf r. Qed.
Lemma rewrites_frontP_impl R u v :
  rewrites_front_spec R u v -> rewrites_spec R u v.
Proof. by move/rewrites_front_specP => /(_ [::]) /=. Qed.
Lemma cons_rewrites_spec R a u v :
  rewrites_spec R u v -> rewrites_spec R (a :: u) (a :: v).
Proof. by case=> pre suf r /= {u}->{v}-> rinR; exists (a :: pre) suf r. Qed.

Lemma rewrites_frontP R u v :
  reflect (rewrites_front_spec R u v) (v \in rewrites_front R u).
Proof.
apply (iffP idP); elim: R => [|[r1 r2] R IHR] //=.
- case: prefixP => [| _ {}/IHR[suf [s1 s2]/= {u}->{v}-> sinR]]; first last.
    by exists suf (s1, s2) => //=; rewrite inE sinR orbT.
  case=> suf equ; subst u => /=.
  rewrite inE => /orP[/eqP{v IHR}-> | {}/IHR].
    by exists suf (r1, r2); rewrite ?drop_size_cat // inE eqxx.
  exact: rewrites_front_spec_cons.
- by case.
case=> suf [s1 s2]/= equ eqv; subst u v.
rewrite inE => /orP[/eqP[{r1}<-{r2}<-] | sinR].
  by rewrite prefix_prefix inE drop_size_cat // eqxx.
have {}/IHR : rewrites_front_spec R (s1 ++ suf) (s2 ++ suf) by exists suf (s1, s2).
by case: prefixP => _ //; rewrite inE orbC => ->.
Qed.

Lemma rewritesP R u v : reflect (rewrites_spec R u v) (v \in rewrites R u).
Proof.
apply (iffP idP); elim: u v => [| a u IHu] v /=.
- by move=> /rewrites_frontP/(rewrites_front_specP [::]).
- rewrite mem_cat => /orP[/rewrites_frontP/(rewrites_front_specP [::]) //|].
  move=> /mapP[/= w {}/IHu /[swap]{v}->].
  exact: cons_rewrites_spec.
- case=> -[|//] /[swap] [[/= [|//] b]] /= [|//] _ -> rinR /[!cats0].
  by apply/rewrites_frontP; exists [::] ([::], b); rewrite // cats0.
- rewrite mem_cat => -[pre suf [r1 r2] /= /[dup] equ-> {v}-> rinR].
  case: pre equ => [/=| b pre /= [{b}<-]] equ; apply/orP.
    by left; apply/rewrites_frontP; exists suf (r1, r2).
  right; rewrite mem_map; last by move=> ? ? [].
  by apply: IHu; rewrite {}equ; exists pre suf (r1, r2).
Qed.
Lemma rewrites_front_impl R u v :
  v \in rewrites_front R u-> v \in rewrites R u.
Proof. by move=> /rewrites_frontP/rewrites_frontP_impl/rewritesP. Qed.

Lemma rewrites_rel R u v : (u, v) \in R -> v \in rewrites R u.
Proof.
move=> rin; apply/rewritesP.
by exists [::] [::] (u, v); rewrite //= cats0.
Qed.


(* Finds the first matching rule in R that matches a prefix of u and produces
   the rewriten v, or None. *)
Fixpoint rewrites1_front R u : option word :=
  if R is (r1, r2) :: R' then
    if prefix r1 u then Some (r2 ++ drop (size r1) u)
    else rewrites1_front R' u
  else None.

Section Rewrites1.

Variable R : relat.

(* rewrites_front_spec R u x holds when either
   - s = Some v and one can obtain v from u by rewriting a prefix
   - x = None and no rewrites rule or R apply to a prefix of u *)
Variant rewrites1_front_spec u : option word -> Prop :=
  | Rewrites1FrontRes v :
    v \in rewrites_front R u -> rewrites1_front_spec u (Some v)
  | Rewrites1FrontNone :
    rewrites_front R u = [::] -> rewrites1_front_spec u None.
Definition rewrites1_front_Ok rew :=
  forall u, rewrites1_front_spec u (rew u).

(* rewrites_spec R u x holds when either
   - x = None and no rewrites rule or R apply to u
   - s = Some v and u rewrites in one step to v *)
Variant rewrites1_spec u : option word -> Prop :=
  | Rewrite1Res : forall v, v \in rewrites R u -> rewrites1_spec u (Some v)
  | Rewrite1None : rewrites R u == [::]        -> rewrites1_spec u None.
(* Equivalent definition *)
Variant rewrites1_spec_def u : option word -> Prop :=
  | Rewrite1ResDef :
    forall v, rewrites_spec R u v -> rewrites1_spec_def u (Some v)
  | Rewrite1NoneDef :
    (forall v, ~ rewrites_spec R u v) -> rewrites1_spec_def u None.
Definition rewrites1_Ok rew := forall u, rewrites1_spec u (rew u).

Lemma rewrite1_specE u res :
  rewrites1_spec u res <-> rewrites1_spec_def u res.
Proof.
split => [][v|].
- by move=> uRv; constructor; apply/rewritesP.
- by move=> /eqP uRv; constructor => v /rewritesP; rewrite uRv.
- by move=> /rewritesP uRv; constructor.
- move=> nrew; constructor; apply/negP => /negP.
  case H : (rewrites R u) => [//| a l] //= _.
  by apply: (nrew a); apply/rewritesP; rewrite H inE eqxx.
Qed.

Lemma rewrites1_frontE u :
  rewrites1_front R u = head None [seq Some v | v <- rewrites_front R u].
Proof. by elim: R => [// | [r1 r2] R' IHR'] /=; case: prefix. Qed.
Lemma rewrites_front0P u :
  (rewrites_front R u == [::]) = (rewrites1_front R u == None).
Proof. by rewrite rewrites1_frontE; case: rewrites_front. Qed.
Lemma rewrites1_front_SomeP u v :
  rewrites1_front R u = Some v -> v \in rewrites_front R u.
Proof.
rewrite rewrites1_frontE.
by case: rewrites_front => [//| w s] /= [<-{v}]; rewrite inE eqxx.
Qed.
Lemma rewrites1_frontP : rewrites1_front_Ok (rewrites1_front R).
Proof.
move=> u; case H: rewrites1_front => [v|]; constructor.
  by move/rewrites1_front_SomeP: H.
by apply/eqP; rewrite rewrites_front0P H.
Qed.


(* Finds the first matching rule in R that matches a factor of u and produces
   the rewritten v, or None.  rewfront is supposed to match the
   rewrites1_front specification.

   We use it right away with rewrites1_front and will use it later with more
   efficient rewrites search algorihtms, for example using tries.
*)
Definition rewrites1_from_front (rewfront : word -> option word) :=
  fix loop u := if rewfront u is Some u as res then res
                else if u is a :: u' then option_map (cons a) (loop u')
                else None.
Definition rewrites1 := rewrites1_from_front (rewrites1_front R).

Lemma rewrite1E u :
  rewrites1 u = head None [seq Some v | v <- rewrites R u].
Proof.
rewrite /rewrites1; elim: u => [|a u H /=]; rewrite /= rewrites1_frontE.
  by case: head.
case: rewrites_front => //=; rewrite {}H /=.
by case: rewrites.
Qed.
Lemma rewrites0P u : (rewrites R u == [::]) = (rewrites1 u == None).
Proof. by rewrite rewrite1E; case: rewrites. Qed.
Lemma rewrites1SomeP u v : rewrites1 u = Some v -> v \in rewrites R u.
Proof.
by rewrite rewrite1E; case: rewrites => [//| w s] /= [{v}<-]; rewrite inE eqxx.
Qed.

Lemma rewrite1_from_frontP rewfront :
  (rewrites1_front_Ok rewfront) -> rewrites1_Ok (rewrites1_from_front rewfront).
Proof.
move=> front_spec; elim => [|u0 u IHu] /=.
  case: (front_spec [::]) => [v /rewrites_frontP R0v|].
    by rewrite rewrite1_specE; constructor; apply: rewrites_frontP_impl.
  by move=> /eqP H; constructor.
case: (front_spec (u0 :: u)) => [v|].
  by move/rewrites_front_impl => H; constructor.
case: IHu => [v /rewritesP uRv _ | /eqP norew norewfront] /=.
  by rewrite rewrite1_specE; constructor; apply: cons_rewrites_spec.
by constructor; rewrite /= norew norewfront /=.
Qed.
Definition rewrites1P := rewrite1_from_frontP rewrites1_frontP.

Lemma rewrites1_defP rew1 :
  rewrites1_Ok rew1 -> forall u, rewrites1_spec_def u (rew1 u).
Proof. by move=> H u; rewrite -rewrite1_specE. Qed.


(* rewrites_to u v holds when a sequence of rewriting with rules from R turns
  u into v. The sequence can be empty, i.e., the relation is reflexive *)
Variant rewrites_to u v : Prop :=
  RewritesTo : forall pth, path (fun u v => v \in rewrites R u) u pth ->
                  v = last u pth -> rewrites_to u v.
Arguments RewritesTo {u v} (pth).

Lemma rewrites_to1 u v : v \in rewrites R u -> rewrites_to u v.
Proof. by move=> rew; exists [:: v]; rewrite //= andbT. Qed.

Lemma rewrites_to_refl : reflexivep rewrites_to.
Proof. by move=> x; exists [::]. Qed.
Hint Resolve rewrites_to_refl : core.

Lemma rewrites_to_trans : transitivep rewrites_to.
Proof.
move=> x y z [pathxy Hxy Hy] [pathyz Hyz Hz].
exists (pathxy ++ pathyz).
- by rewrite cat_path Hxy -Hy Hyz.
- by rewrite last_cat -Hy.
Qed.
Lemma rewrites_toP u v :
  rewrites_to u v
  <-> ((u = v) \/ (exists2 w, w \in rewrites R u & rewrites_to w v)).
Proof.
split.
  case=> -[/= _ -> | w pth /= /andP[u_w Hpth] /= {v}->]; first by left.
  by right; exists w; [exact: u_w | exists pth].
case=> [-> | [w /rewrites_to1]]; first exact: rewrites_to_refl.
exact: rewrites_to_trans.
Qed.
Lemma rewrites_stable u v1 v2 w :
  v2 \in rewrites R v1 -> u ++ v2 ++ w \in rewrites R (u ++ v1 ++ w).
Proof.
move=> /rewritesP[pre suf [r1 r2] {v1}->{v2}-> rinR /=].
by apply/rewritesP; exists (u ++ pre) (suf ++ w) (r1, r2); rewrite //= !catA.
Qed.
Lemma rewrites_to_stable : stablep rewrites_to.
Proof.
move=> u v1 v2 w [p path_p {v2}->].
pose F b := u ++ b ++ w; rewrite -/(F v1).
exists [seq F b | b <- p]; last by rewrite last_map.
by move: path_p; apply: homo_path => x y; apply: rewrites_stable.
Qed.

Definition rewrites_to_cat := stable_cat rewrites_to_trans rewrites_to_stable.

(* rewrites_to u v is the minimal reflexive, transitive and stable relation
   which contains R. This could be taken as a definition. *)
Theorem rewrites_to_min CR :
  (forall p, p \in R -> CR p.1 p.2) -> rewcongrp CR ->
  forall u v, rewrites_to u v -> CR u v.
Proof.
move=> incl [CR_refl CR_trans CR_stable] u v [p path_p {v}->].
elim: p u path_p => [//=| p0 p IHp] u /= /andP[p0_u] {}/IHp; apply CR_trans.
move/rewritesP : p0_u => [pre suf [r1 pr] {u}->{p0}-> rinR] /=.
by apply: CR_stable; apply: (incl _ rinR).
Qed.


Section Symmetry.

Hypothesis Rsym : forall u v, (u, v) \in R -> (v, u) \in R.

Lemma rewrites_sym_impl x y : x \in rewrites R y -> y \in rewrites R x.
Proof.
move=> /rewritesP[pre suf [r1 r2] {y}->{x}-> rinR  /=].
apply/rewritesP; exists pre suf (r2, r1) => //.
exact: Rsym.
Qed.

Lemma rewrites_sym x y : (x \in rewrites R y) = (y \in rewrites R x).
Proof. by apply/idP/idP; exact: rewrites_sym_impl. Qed.

Lemma rewrites_to_sym : symmetricp rewrites_to.
Proof.
move=> x y [pathxy]; rewrite -rev_path => Hxy Hy.
move: Hxy; rewrite -Hy.
case/lastP: pathxy Hy => [/= -> _ | pathxz z]; first by exists [::].
rewrite last_rcons belast_rcons rev_cons => {y}-> Hpath.
exists (rcons (rev pathxz) x); last by rewrite last_rcons.
set rel := (X in path X _ _) in Hpath.
rewrite (eq_path (e' := rel)) /=; first exact: Hpath.
by rewrite /rel => u v; exact: rewrites_sym.
Qed.
Lemma rewrites_to_symE x y : rewrites_to x y <-> rewrites_to y x.
Proof. split; exact: rewrites_to_sym. Qed.

Lemma rewrites_to_congr : congruencep rewrites_to.
Proof.
split.
- exact: rewrites_to_refl.
- exact: rewrites_to_trans.
- exact: rewrites_to_stable.
- exact: rewrites_to_sym.
Qed.

End Symmetry.

End Rewrites1.

Lemma rewrites_front_cat R1 R2 u :
  rewrites_front (R1 ++ R2) u = rewrites_front R1 u ++ rewrites_front R2 u.
Proof. by elim: R1 => [// | [r1 r2] R1 /= ->]; case (prefix _ _). Qed.

Lemma rewrites_cat_perm R1 R2 u :
  perm_eq (rewrites (R1 ++ R2) u) ((rewrites R1 u) ++ (rewrites R2 u)).
Proof.
apply/permP.
elim: u => [|u0 u IHu] /= p; first by rewrite rewrites_front_cat.
rewrite !count_cat addnA [X in _ = X + _]addnC addnA [X in _ = X + _ + _]addnC.
rewrite -[X in _ = X + _ + _]count_cat -rewrites_front_cat -addnA; congr (_ + _).
by rewrite !count_map IHu -count_cat.
Qed.

Lemma rewrites_cat R1 R2 u :
  rewrites (R1 ++ R2) u =i (rewrites R1 u) ++ (rewrites R2 u).
Proof. exact/perm_mem/rewrites_cat_perm. Qed.
Lemma rewrites_cons p R u :
  rewrites (p :: R) u =i (rewrites [:: p] u) ++ (rewrites R u).
Proof. by move=> v; rewrite -cat1s rewrites_cat. Qed.
Lemma rewrites_rcons R p u :
  rewrites (rcons R p) u =i (rewrites [:: p] u) ++ (rewrites R u).
Proof. by move=> v; rewrite -cats1 rewrites_cat !mem_cat orbC. Qed.


Section DefPresentationRels.

Definition undirected R := R ++ [seq swap p | p <- R].

Lemma rewrites_map_swap R u v :
  (u \in rewrites [seq swap p | p <- R] v) = (v \in rewrites R u).
Proof.
have impl S x y :
  (y \in rewrites S x) -> (x \in rewrites [seq swap p | p <- S] y).
  move=> /rewritesP[pre suf [r1 r2] {u}->{v}-> rinR /=].
  apply/rewritesP; exists pre suf (swap (r1, r2)) => //=.
  by rewrite (mem_map swap_inj).
apply/idP/idP; last exact: impl.
rewrite -{2}(map_id R) -(eq_map swapK) (map_comp swap swap).
exact: impl.
Qed.
Lemma rewrites_undirected R u v :
  u \in (rewrites (undirected R)) v =
          (u \in rewrites R v) || (v \in rewrites R u).
Proof. by rewrite rewrites_cat mem_cat rewrites_map_swap. Qed.

Variable R : relat.

Lemma mem_undirected u v :
  (u, v) \in undirected R = ((u, v) \in R) || ((v, u) \in R).
Proof.
rewrite mem_cat; congr orb.
by rewrite -/(swap (v, u)) (mem_map swap_inj).
Qed.

Lemma undirected_sym u v : (u, v) \in undirected R -> (v, u) \in undirected R.
Proof. by rewrite !mem_undirected orbC. Qed.

Let equiv_to := rewrites_to (undirected R).
Lemma equiv_congr : congruencep equiv_to.
Proof. exact: (rewrites_to_congr undirected_sym). Qed.
Lemma equiv_sym : symmetricp equiv_to. Proof. by have [] := equiv_congr. Qed.
Lemma equiv_refl : reflexivep equiv_to. Proof. by have [] := equiv_congr. Qed.
Lemma equiv_trans : transitivep equiv_to. Proof. by have [] := equiv_congr. Qed.
Lemma equiv_stable : stablep equiv_to. Proof. by have [] := equiv_congr. Qed.
(* equiv is the minimal congruence which contains R. *)
Theorem equiv_min CR :
  (forall p, p \in R -> CR p.1 p.2) -> congruencep CR ->
  forall u v, equiv_to u v -> CR u v.
Proof.
move=> Hin [refl trans stab sym]; apply: rewrites_to_min => // [[u v]].
by rewrite mem_undirected => /orP[] /Hin //= /sym.
Qed.

End DefPresentationRels.
Notation "x = y %[mod R ]" := (rewrites_to (undirected R) x y).


Section SubRule.

Variable R1 R2 : relat.
Hypothesis sub_rule : {subset R1 <= R2}.

Lemma sub_rewrites u v : v \in rewrites R1 u -> v \in rewrites R2 u.
Proof.
move=> /rewritesP[pre suf [r1 r2] /= {v}->{u}-> rinR].
apply/rewritesP; exists pre suf (r1, r2) => //=.
exact: sub_rule.
Qed.
Lemma sub_rewrites_to u v : rewrites_to R1 u v -> rewrites_to R2 u v.
Proof.
case=> p p_path {v}->; exists p => //.
by move: p_path; apply (sub_path sub_rewrites).
Qed.
Lemma sub_undirected : {subset undirected R1 <= undirected R2}.
Proof.
case=> u v; rewrite !mem_cat => /orP[/sub_rule -> // |].
move=> /mapP/=[[a b] /sub_rule /[swap]/=[][<-{b}<-{a}]] uvR.
by apply/orP; right; apply/mapP; exists (v, u).
Qed.

End SubRule.

Lemma sub_equiv (R1 R2 : relat) :
  {subset R1 <= R2} -> forall u v, u = v %[mod R1] -> u = v %[mod R2].
Proof.
by move=> sub u v; apply: sub_rewrites_to => [[r1 r2]]; apply: sub_undirected.
Qed.

Lemma subset_undirected (R : relat) : {subset R <= undirected R}.
Proof. by move => [a b] /[!mem_undirected] ->. Qed.
Lemma rewrites_to_equiv (R : relat) u v : rewrites_to R u v -> u = v %[mod R].
Proof. exact: (sub_rewrites_to (@subset_undirected R)). Qed.


Section EqRule.

Variable R1 R2 : relat.
Hypothesis eq_rule : R1 =i R2.

Lemma eq_rewrites u : rewrites R1 u =i rewrites R2 u.
Proof. by move=> v; apply/idP/idP; apply: sub_rewrites => p /[!eq_rule]. Qed.
Lemma eq_rewrites_to u v : rewrites_to R1 u v <-> rewrites_to R2 u v.
Proof. by split; apply: sub_rewrites_to => p /[!eq_rule]. Qed.
Lemma eq_equiv u v :  u = v %[mod R1] <-> u = v %[mod R2].
Proof. by split; apply: sub_equiv => p /[!eq_rule]. Qed.

End EqRule.

Lemma eq_equiv_undirected R1 R2 (eq_rule : undirected R1 =i undirected R2) u v :
  u = v %[mod R1] <-> u = v %[mod R2].
Proof. by split; apply: sub_rewrites_to => /= p /[!eq_rule]. Qed.

End Defs.
Notation "x = y %[mod R ]" := (rewrites_to (undirected R) x y).


Section FreeMonoidInterface.

Variable A : choiceType.
Implicit Types (u v w x y : word A).

Lemma mul_catE u v : u ++ v = ((u : {freemon A}) * (v : {freemon A}))%M.
Proof. by []. Qed.
Lemma flatten_map_prodE I (s : seq I) (g : I -> word A) :
  flatten [seq g i | i <- s] = (\prod_(i <- s) (g i : {freemon A}))%M.
Proof. by elim: s => /=[| s0 s ->]; rewrite ?big_nil ?big_cons. Qed.
Lemma flatten_prodE (s : seq (word A)) :
  flatten s = (\prod_(l <- s) (l : {freemon A}))%M.
Proof. by rewrite -{1}(map_id s) flatten_map_prodE. Qed.

End FreeMonoidInterface.


Section Morphism.

Variable (A B : choiceType).
Implicit Types (u v w x y : word A).

Variable f : {mmorphism {freemon A} -> {freemon B}}.

Lemma mmorph_cat : {morph f: x y  / x ++ y}.
Proof. exact: mmorphM. Qed.
Lemma mmorph_flatten (s : seq (word A)) :
  f (flatten s) = flatten [seq f l | l <- s].
Proof. by rewrite flatten_prodE mmorph_prod [RHS]flatten_map_prodE. Qed.

End Morphism.


(* Structure for presentation *)
Structure pres (A : choiceType) := Pres {
  pgen : seq A;
  prelat :> relat A;
  uniq_pgen : uniq pgen;
  wf_relat : all_relwords prelat (mem pgen)
}.


Section Presentation.

Variable (A : choiceType).
Implicit Types (u v w x y : word A) (R : @pres A).

Definition eq_pres R1 R2 := (pgen R1 == pgen R2) && (prelat R1 == prelat R2).
Lemma eq_presP : Equality.axiom eq_pres.
Proof.
rewrite /eq_pres => -[p1 r1 g1 l1][p2 r2 g2 l2] /=.
apply (iffP idP) => [/andP[/eqP eqp /eqP eqr] | [-> ->]]; last by rewrite !eqxx.
by subst r2 p2; rewrite (bool_irrelevance g2 g1) (bool_irrelevance l2 l1).
Qed.
HB.instance Definition _ := hasDecEq.Build (@pres A) eq_presP.
Lemma eqpresE R1 R2 :
  (pgen R1 == pgen R2) && (prelat R1 == prelat R2) = (R1 == R2).
Proof. by []. Qed.

(* TODO: improve this name *)
Definition words_of R := [pred w | all (mem (pgen R)) w].
Definition WPdecidable R :=
  forall u v, u \in words_of R -> v \in words_of R ->
                                        decidable (u = v %[mod R]).

Lemma words_of_prelat R r :
  r \in prelat R -> (r.1 \in words_of R) && (r.2 \in words_of R).
Proof. by move=> Rr; move/allP: (wf_relat R) => /(_ r Rr). Qed.

Lemma relwords_of R w : w \in relwords R -> w \in words_of R.
Proof.
case/relwordsP=> -[r1 r2] /words_of_prelat /= /andP[r1in r2in].
by move=> /orP[]/eqP ->.
Qed.

Lemma words_of_cat R u v :
  u ++ v \in words_of R = (u \in words_of R) && (v \in words_of R).
Proof. by rewrite /words_of /= !inE all_cat. Qed.

Lemma rewrites_words_ofE R u v :
  v \in rewrites R u -> (u \in words_of R) = (v \in words_of R).
Proof.
case/rewritesP => [pre suf [r1 r2]] /= {u}->{v}->.
rewrite !words_of_cat.
by move/words_of_prelat/andP => /=[-> ->].
Qed.
Lemma rewrites_to_words_ofE R u v :
  rewrites_to R u v -> (u \in words_of R) = (v \in words_of R).
Proof.
case=> pathuv Huv {v}->.
elim: pathuv u Huv => [| p0 pth IHpth] //= u.
case/andP => /rewrites_words_ofE ->.
exact: IHpth.
Qed.

Fact wf_undirected_pres R : all_relwords (undirected R) (mem (pgen R)).
Proof.
apply/allP=> /= [[x1 x2]] /=.
have /allP := wf_relat R => /= hwf.
rewrite mem_undirected => /orP [] hx //=; last rewrite andbC.
all: by rewrite (hwf _ hx).
Qed.
Definition undirected_pres R := Pres (uniq_pgen R) (wf_undirected_pres R).

Lemma words_of_undirected_pres R :
  words_of (undirected_pres R) =i words_of R.
Proof. by []. Qed.
Lemma rewrites_to_undirected_pres R u v :
  rewrites_to (undirected_pres R) u v <-> u = v %[mod R].
Proof. by []. Qed.
Lemma equiv_words_ofE R u v :
  u = v %[mod R] -> (u \in words_of R) = (v \in words_of R).
Proof.
rewrite -rewrites_to_undirected_pres.
by move/rewrites_to_words_ofE; rewrite !words_of_undirected_pres.
Qed.

End Presentation.


Definition rewmorphism A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) :=
  forall u v : word A, u \in words_of R -> v \in words_of R ->
  v \in rewrites R u -> rewrites_to S (f u) (f v).

(* assia : or may be axiom on generators and this as a theory lemma *)
Definition rewmorphism_in A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) :=
  forall u : word A, u \in words_of R -> (f u \in words_of S).

(* assia: where is this needed? *)
Definition rewmorphism_to A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) :=
  forall u v : word A, u \in words_of R -> v \in words_of R ->
     rewrites_to R u v -> rewrites_to S (f u) (f v).

Lemma rewmorphism_toP A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) : rewmorphism R S f <-> rewmorphism_to R S f.
Proof.
split; last first.
- by move=> h u v wu wv hrw; apply: h=> //; apply: rewrites_to1.
- move=> h u v wu wv [p hp ->].
  elim: p u hp wu => [u _ _ |p0 pth IHpth u] /=; first exact: rewrites_to_refl.
  move=> /andP[p0_u {}/IHpth] ihp hu.
  have /ihp : p0 \in words_of R by rewrite -(rewrites_words_ofE p0_u).
  apply: rewrites_to_trans; apply: h => //.
  by rewrite -(rewrites_words_ofE p0_u).
Qed.

HB.mixin Record isRewMorphism
  A B (R : pres A) (S : pres B) (f : {freemon A} -> {freemon B}) := {
    rewmorphism_subproof : rewmorphism R S f;
    rewmorphism_in_subproof : rewmorphism_in R S f
  }.

HB.structure Definition RewMorphism A B (R : pres A) (S : pres B) :=
  {f of MonMorphism {freemon A} f & isRewMorphism A B R S f}.
Notation "{ 'rewmorph' R -> S }" := (RewMorphism.type R S) : type_scope.
Notation "{ 'presmorph' R -> S }" :=
  (RewMorphism.type (undirected_pres R) (undirected_pres S)) : type_scope.


Section RewMorphismTheory.

Variables (A B : choiceType) (R : pres A) (S : pres B) (f : {rewmorph R -> S}).

Lemma rewmorph_toP u v :
  u \in words_of R -> v \in words_of R ->
  v \in rewrites R u -> rewrites_to S (f u) (f v).
Proof. exact: rewmorphism_subproof. Qed.

Lemma rewmorph_inP u :
  u \in words_of R -> f u \in words_of S.
Proof. exact: rewmorphism_in_subproof. Qed.

Lemma rewmorphP u v :
  u \in words_of R -> v \in words_of R ->
  rewrites_to R u v -> rewrites_to S (f u) (f v).
Proof.
move=> hu hv [p Hp ->].
elim: p u Hp hu => [u _ _ |p0 pth IHpth u] /=; first exact: rewrites_to_refl.
move=> /andP[p0_u {}/IHpth] ihp hu.
have hp0 : p0 \in words_of R by rewrite -(rewrites_words_ofE p0_u).
apply: rewrites_to_trans (ihp hp0); exact: rewmorph_toP.
Qed.

End RewMorphismTheory.

HB.factory Record isRewMorphismTo
  A B (R : pres A) (S : pres B) (f : {freemon A} -> {freemon B}) := {
    rewmorphism_to_subproof : rewmorphism_to R S f;
    rewmorphism_to_in_subproof : rewmorphism_in R S f
  }.
HB.builders Context A B (R : pres A) (S : pres B) f of
  isRewMorphismTo A B R S f.

Lemma rewmorphism_toP : rewmorphism R S f.
Proof. move=> u v wu wv /rewrites_to1/rewmorphism_to_subproof; exact. Qed.

Lemma rewmorphism_to_inP : rewmorphism_in R S f.
Proof. exact: rewmorphism_to_in_subproof. Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _  :=
  isRewMorphism.Build A B R S f rewmorphism_toP rewmorphism_to_inP.
HB.end.

(* assia: builds the instance of morphism on symmetrized relations,
from a morphism on the undirected relations. *)
HB.factory Record isPresMorphism
  A B (R : pres A) (S : pres B) (f : {freemon A} -> {freemon B}) := {
    presmorphism_subproof : rewmorphism R S f;
    rewmorphism_in_subproof : rewmorphism_in R S f
  }.
HB.builders Context A B (R : pres A) (S : pres B) f of
  isPresMorphism A B R S f.

(* what is "fresh_name_22"? *)
Lemma rewmorphism_undirected :
  rewmorphism (undirected_pres R) (undirected_pres S) f.
Proof.
move=> u v; rewrite rewrites_undirected => /= hu hv /orP [].
all: move=> /presmorphism_subproof/rewrites_to_equiv // h.
2: apply: equiv_sym.
all: exact: h.
Qed.

Lemma rewmorphism_in_undirected :
  rewmorphism_in (undirected_pres R) (undirected_pres S) f.
Proof. move=> u hu; exact: rewmorphism_in_subproof. Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _  :=
  isRewMorphism.Build A B
  (undirected_pres R) (undirected_pres S) f
  rewmorphism_undirected rewmorphism_in_undirected.
HB.end.

HB.factory Record isPresMorphismTo
  A B (R : pres A) (S : pres B) (f : {freemon A} -> {freemon B}) := {
    presmorphism_to_subproof : rewmorphism_to R S f;
    presmorphism_in_subproof : rewmorphism_in R S f
  }.

HB.builders Context A B (R : pres A) (S : pres B) f of
  isPresMorphismTo A B R S f.

Lemma rewmorphism_to_undirected : rewmorphism R S f.
Proof.
move=> u v hu hv /rewrites_to1/presmorphism_to_subproof; exact.
Qed.

(* assia: is this name ok ?*)
Lemma rewmorphism_in_undirected :
  rewmorphism_in (undirected_pres R) (undirected_pres S) f.
Proof. move=> u hu; exact: presmorphism_in_subproof. Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _  :=
  isPresMorphism.Build A B R S f
  rewmorphism_to_undirected rewmorphism_in_undirected.
HB.end.


Section IdMor.
Variables (A : choiceType) (R R' : pres A).
Hypothesis eqR : forall u v, u \in words_of R -> v \in words_of R ->
  rewrites_to R u v -> rewrites_to R' u v.
Hypothesis inR : forall u, u \in words_of R ->  u \in words_of R'.

Definition idRR' : {freemon A} -> {freemon A} := idfun.
HB.instance Definition _  := MonMorphism.on idRR'.
HB.instance Definition _  := isRewMorphismTo.Build A A R R' idRR' eqR inR.
Definition idmorRR' : {rewmorph R -> R'} := idRR'.

Lemma morRR'E : idmorRR' =1 id :> (word A -> word A).
Proof. by []. Qed.

End IdMor.

Definition idmor A (R : pres A) : {rewmorph R -> R} :=
  idmorRR' (fun _ _ _ _ => idfun) (fun _ => idfun).


Section RewMorphismTheory.

Variables (A B C : choiceType) (R : pres A) (S : pres B) (T : pres C)
  (f : {rewmorph R -> S}) (g : {rewmorph S -> T}).

Fact comp_is_rewmorphism : rewmorphism_to R T (g \o f).
Proof.
move=> u v hu hv hR.
by apply: rewmorphP; last apply: rewmorphP=> //; apply: rewmorph_inP.
Qed.

Fact comp_rewmorphism_in : rewmorphism_in R T (g \o f).
Proof. by move=> u hu; do 2! apply: rewmorph_inP. Qed.

HB.instance Definition _ :=
  isRewMorphismTo.Build A C R T (g \o f)
  comp_is_rewmorphism comp_rewmorphism_in.

End RewMorphismTheory.

Record isopres (A B : choiceType) (R : pres A) (S : pres B) := IsoPres {
    mor :> {presmorph R -> S};
    inv : {presmorph S -> R};
    canmor : forall a : word A,
      a \in words_of R -> inv (mor a) = a %[mod R];
    caninv : forall b : word B,
      b \in words_of S -> mor (inv b) = b %[mod S]
  }.

Definition isopres_sym A B (R : pres A) (S : pres B)
  (eq : isopres R S) := IsoPres (caninv eq) (canmor eq).
Lemma isopres_symK A B (R : pres A) (S : pres B) eq :
  ((@isopres_sym B A S R) \o (@isopres_sym A B R S)) eq = eq.
Proof. by rewrite /isopres_sym; move: eq => [m i cm ci]/=. Qed.
Lemma isopres_symE A B (R : pres A) (S : pres B) (eq : isopres R S) :
  isopres_sym eq =1 inv eq.
Proof. by []. Qed.

Lemma isopres_words_of A B (R : pres A) (S : pres B) (eq : isopres R S) u :
  u \in words_of R -> eq u \in words_of S.
Proof. by move=> H; apply: rewmorph_inP; rewrite words_of_undirected_pres. Qed.

Lemma isopresP A B (R : pres A) (S : pres B) (eq : isopres R S) u v :
  u \in words_of R -> v \in words_of R ->
  eq u = eq v %[mod S] <-> u = v %[mod R].
Proof.
move=> wu wv; split => [/(rewmorphP (inv eq)) /= H |]; first last.
  exact: (rewmorphP eq).
have hu : eq u \in words_of (undirected_pres S) by exact: rewmorph_inP.
have hv : eq v \in words_of (undirected_pres S) by exact: rewmorph_inP.
have {H} h := H hu hv.
apply: (equiv_trans (equiv_sym (canmor eq wu))).
apply: (equiv_trans h); exact: canmor.
Qed.


Lemma isopres_invP A B (R : pres A) (S : pres B) (eq : isopres R S) u v :
  u \in words_of S -> v \in words_of S ->
  inv eq u = inv eq v %[mod R] <-> u = v %[mod S].
Proof. move=> hu hv; exact: (isopresP (isopres_sym eq)). Qed.

Lemma isopres_dec A B (R : pres A) (S : pres B) :
  isopres R S -> WPdecidable S -> WPdecidable R.
Proof.
move=> iso decS u v uR vR.
have uS : iso u \in words_of S.
  by apply: rewmorph_inP; rewrite words_of_undirected_pres.
have vS : iso v \in words_of S.
  by apply: rewmorph_inP; rewrite words_of_undirected_pres.
have [RS RSinv] := isopresP iso uR vR.
case: (decS _ _ uS vS) => [/RS uv| uv]; first by left.
by right => H; apply uv; apply: RSinv.
Qed.
Lemma isopres_decK A B (R : pres A) (S : pres B) :
  isopres R S -> WPdecidable R -> WPdecidable S.
Proof. by move/isopres_sym/isopres_dec. Qed.

Section IsopresTheory.

Variables (A B C : choiceType) (R : pres A) (S : pres B) (T : pres C).

Definition isopres_refl :=
  let uR := undirected_pres R in IsoPres (mor := idmor uR) (inv := idmor uR)
      (fun a _ => rewrites_to_refl uR a)
      (fun a _ => rewrites_to_refl uR a).

Lemma isopres_reflE : isopres_refl = (@idmor _ _) :> {presmorph _ -> _}.
Proof. by []. Qed.

Variable (eqRS : isopres R S) (eqST : isopres S T).
Fact canmor_trans a :
  a \in words_of R ->
        (inv eqRS \o inv eqST) ((eqST \o eqRS) a) = a %[mod R].
Proof.
move=> wa.
have wRSa : eqRS a \in words_of S by apply: rewmorph_inP.
have := canmor eqST wRSa; rewrite -(isopres_invP eqRS) /=.
- by move/equiv_trans; apply; apply canmor.
- by do 3! apply: rewmorph_inP.
- exact: rewmorph_inP.
Qed.

Fact invmor_trans c :
  c \in words_of T ->
        (eqST \o eqRS) ((inv eqRS \o inv eqST) c) = c %[mod T].
Proof.
move=> wc.
have wiSTc : inv eqST c \in words_of S by apply: rewmorph_inP.
have := caninv eqRS wiSTc; rewrite -(isopres_invP eqST) //=.
- by move/(equiv_trans _); apply; apply canmor; do 3! apply: rewmorph_inP.
- by do 4! apply: rewmorph_inP.
Qed.
Definition isopres_trans := IsoPres canmor_trans invmor_trans.

Lemma isopres_transE : isopres_trans = eqST \o eqRS :> {presmorph _ -> _}.
Proof. by []. Qed.
Lemma isopres_trans_invE : inv isopres_trans = inv eqRS \o inv eqST.
Proof. by []. Qed.

End IsopresTheory.


Section PresEqEquivTheory.

Variables (A : choiceType) (R R' : pres A).
Hypothesis eqR : forall u v,
    [/\ u \in words_of R, v \in words_of R & u = v %[mod R]] <->
    [/\ u \in words_of R', v \in words_of R' & u = v %[mod R']].

Let mor_subproof u v : u \in words_of R -> v \in words_of R ->
  u = v %[mod R] -> u = v %[mod R'].
Proof.
move=> wu wv Ruv.
have : [/\ u \in words_of R, v \in words_of R & u = v %[mod R]] by split.
by case/eqR.
Qed.

Lemma mor_in_subproof u :
  u \in words_of (undirected_pres R) -> u \in words_of (undirected_pres R').
Proof.
move=> wu.
suff : [/\ u \in words_of R, u \in words_of R & u = u %[mod R]].
  by move/eqR; case.
split=> //; exact: rewrites_to_refl.
Qed.

Let inv_subproof u v :  u \in words_of R' -> v \in words_of R' ->
 u = v %[mod R'] -> u = v %[mod R].
Proof.
move=> wu wv R'uv.
have : [/\ u \in words_of R', v \in words_of R' & u = v %[mod R']] by split.
by case/eqR.
Qed.

Lemma inv_in_subproof u :
  u \in words_of (undirected_pres R') -> u \in words_of (undirected_pres R).
Proof.
move=> wu.
suff : [/\ u \in words_of R', u \in words_of R' & u = u %[mod R']].
  by move/eqR; case.
split=> //; exact: rewrites_to_refl.
Qed.

Let morRR' : {presmorph R -> R'} :=
      idmorRR' (R := undirected_pres R) (R' := undirected_pres R')
        mor_subproof mor_in_subproof.

Let morR'R : {presmorph R' -> R} :=
      idmorRR' (R := undirected_pres R') (R' := undirected_pres R)
        inv_subproof inv_in_subproof.

Fact canmor_eq a : morR'R (morRR' a) = a %[mod R].
Proof. exact: equiv_refl. Qed.
Fact caninv_eq a : morRR' (morR'R a) = a %[mod R'].
Proof. exact: equiv_refl. Qed.
Definition isopres_eq : isopres R R' :=
  IsoPres (fun _ _ => canmor_eq _) (fun _ _ => caninv_eq _).

Lemma isopres_eqE : isopres_eq = id :> (_ -> _).
Proof. by []. Qed.

End PresEqEquivTheory.


Section PermIrrelevance.

Variable (A : choiceType) (R1 R2 : pres A).
Hypotheses (eqgen : perm_eq (pgen R1) (pgen R2))
           (eqrel : perm_eq (prelat R1) (prelat R2)).

Definition pres_irrelevance_perm_eq : isopres R1 R2.
Proof.
apply: isopres_eq => u v.
move/perm_mem: eqgen => geneq.
move/perm_mem: eqrel => releq.
have eq_word_of : words_of R1 =i words_of R2.
  by move=> w; apply: eq_all.
rewrite !eq_word_of.
case: (u \in _); rewrite ?orbT //; last by split => [][].
case: (v \in _); rewrite ?orbT //; last by split => [][].
suff /eq_equiv_undirected /(_ u v) Heq :
    undirected R1 =i undirected R2.
  by split => [][_ _ /Heq].
by case=> x y; rewrite !mem_undirected !releq.
Defined.
Lemma pres_irrelevance_perm_eqE : pres_irrelevance_perm_eq = id :> (_ -> _).
Proof. by []. Qed.

End PermIrrelevance.


Section Tietze1.

Variable A : choiceType.
Implicit Types (R : relat A) (u v w x y : word A).


(** First Tietze transformation, rewrites_to version *)
Lemma rewrites_to_cons_rule R u v :
  rewrites_to R u v ->
  forall x y, rewrites_to R x y <-> rewrites_to ((u, v) :: R) x y.
Proof.
move=> cuv x y.
split; first by apply: sub_rewrites_to => p p_inR; rewrite inE p_inR orbT.
case=> p /[swap] {y}->; elim: p x => [|p0 p IHp] x /=.
  by move=> _; exists [::].
move=> /andP[p0_rew {}/IHp p0_p].
suff {p0_p} x_p0 : rewrites_to R x p0 by apply: (rewrites_to_trans x_p0 p0_p).
move: p0_rew; rewrite rewrites_cons mem_cat => /orP[]; last exact: rewrites_to1.
move=> /rewritesP[pre suf [r1 r2] {x}->{p0}-> /[!inE]/eqP[{r1}->{r2}->]]/=.
exact: (rewrites_to_stable pre suf cuv).
Qed.


(** First Tietze transformation, equivalence version *)
Variables (R : pres A) (u v : word A).
Hypotheses (pgen_u : u \in words_of R) (pgen_v : v \in words_of R).

Let pgu : all (mem (pgen R)) u.
Proof. exact: pgen_u. Qed.
Let pgv : all (mem (pgen R)) v.
Proof. exact: pgen_v. Qed.

Lemma wf_ext_pres : all_relwords ((u, v) :: prelat R) (mem (pgen R)).
Proof.
apply/allP=> /= [[x1 x2]] /=.
have /allP := wf_relat R => /= hwf.
rewrite inE; case/orP; last exact: hwf.
by case/eqP=> -> ->; rewrite pgu.
Qed.

Definition ext_pres : pres A :=  Pres (uniq_pgen R) wf_ext_pres.

Lemma wf_rcons_ext_pres :
  all_relwords (rcons (prelat R) (u, v)) (mem (pgen R)).
Proof.
apply/allP=> /= [[x1 x2]] /=.
have /allP := wf_relat R => /= hwf.
rewrite mem_rcons; case/orP; last exact: hwf.
by case/eqP=> -> ->; rewrite pgu.
Qed.

Definition rcons_ext_pres : pres A :=  Pres (uniq_pgen R) wf_rcons_ext_pres.

Hypothesis (Ruv : u = v %[mod R]).

Lemma equiv_cons_rule_mod x y :
  x = y %[mod R] <-> x = y %[mod (u, v) :: prelat R].
Proof.
rewrite (rewrites_to_cons_rule Ruv).
have rvu : rewrites_to ((u, v) :: undirected R) v u.
  by rewrite -(rewrites_to_cons_rule Ruv); apply: equiv_sym.
rewrite (rewrites_to_cons_rule rvu) {rvu}.
apply: eq_rewrites_to => {x y}[[/= x y]].
rewrite !(mem_undirected, inE) -[(y, x) == _](inj_eq swap_inj) /swap /=.
by case: eqP; rewrite !(orbT, orbA).
Qed.

Fact equiv_cons_rule x y :
  [/\ x \in words_of R, y \in words_of R & x = y %[mod R]] <->
  [/\ x \in words_of R, y \in words_of R & x = y %[mod (u, v) :: prelat R]].
Proof.
by split; case=> wx wy Rxy; split=> //; apply/equiv_cons_rule_mod.
Qed.
Definition isopres_cons_rule := @isopres_eq _ _ ext_pres equiv_cons_rule.

Lemma isopres_cons_ruleE : isopres_cons_rule = id :> (_ -> _).
Proof. by []. Qed.

Lemma equiv_rcons_rule_mod x y :
  x = y %[mod R] <-> x = y %[mod rcons (prelat R) (u, v)].
Proof.
rewrite (equiv_cons_rule_mod x y); apply eq_equiv => /= p.
by rewrite mem_rcons.
Qed.

Fact equiv_rcons_rule x y :
  [/\ x \in words_of R, y \in words_of R & x = y %[mod R]] <->
  [/\ x \in words_of R, y \in words_of R & x = y %[mod rcons (prelat R) (u, v)]].
Proof.
by split; case=> wx wy Rxy; split=> //; apply/equiv_rcons_rule_mod.
Qed.
Definition isopres_rcons_rule := @isopres_eq _ _ rcons_ext_pres equiv_rcons_rule.

Lemma isopres_rcons_ruleE : isopres_cons_rule = id :> (_ -> _).
Proof. by []. Qed.

End Tietze1.

Lemma Tietze_add_rel  A (R1 R2 : pres A) (u v : word A) :
  u \in words_of R1 -> v \in words_of R1 ->
  pgen R1 = pgen R2 -> prelat R2 = rcons (prelat R1) (u, v) ->
  u = v %[mod R1] -> isopres R1 R2.
Proof.
move=> allu allv eqgen eqrelat newrelat.
suff -> : R2 = rcons_ext_pres allu allv by apply isopres_rcons_rule.
by apply/eqP; rewrite -eqpresE /= eqrelat eqgen !eqxx.
Defined.


Section Tietze2.

Context (A : choiceType) (R : pres A) (gen : A) (w : word A).

Hypothesis wcorr : w \in words_of R.
Hypothesis gen_nP : gen \notin (pgen R).

Let wall : all (mem (pgen R)) w.
Proof. exact: wcorr. Qed.

Implicit Types (u v x y : word A).

Definition Tietze2_gen := rcons (pgen R) gen.
Definition Tietze2_relat := rcons (prelat R) (w, [:: gen]).

Lemma subset_Tietze2 : {subset prelat R <= Tietze2_relat}.
Proof. by move=> /= p; rewrite mem_rcons inE orbC => ->. Qed.

Fact Tietze2_gen_uniq : uniq Tietze2_gen.
Proof.
rewrite rcons_uniq gen_nP; exact: uniq_pgen.
Qed.
Fact Tietze2_wf_relat : all_relwords Tietze2_relat (mem Tietze2_gen).
Proof.
have sub_relat : subpred (mem (prelat R)) (mem Tietze2_relat).
  by move=> x Rx; rewrite /= mem_rcons mem_behead.
have sub_gen : subpred (mem (pgen R)) (mem Tietze2_gen).
  by move=> x Rx; rewrite /= mem_rcons mem_behead.
apply/allP=> /= [] r.
rewrite mem_rcons inE; case/orP=> [/eqP | Rr].
- case:r  => r1 r2 [] -> ->; rewrite /= mem_rcons mem_head /= andbT.
  exact: (sub_all sub_gen).
- have /allP/(_ _ Rr) /andP[rr1 Rr2] := wf_relat R.
  by rewrite !(sub_all sub_gen).
Qed.
Definition T2_pres : pres A := Pres Tietze2_gen_uniq Tietze2_wf_relat.


Lemma sub_2 u v : u = v %[mod R] -> u = v %[mod Tietze2_relat].
Proof. exact: (sub_equiv subset_Tietze2). Qed.

Lemma sub_words_of_T2 u : u \in words_of (undirected_pres R) ->
   u \in words_of (undirected_pres T2_pres).
Proof.
move=> wu.
have sub_gen : subpred (mem (pgen R)) (mem Tietze2_gen). (* should be a fact*)
  by move=> x Rx; rewrite /= mem_rcons mem_behead.
by apply/allP=> /= [] r ur; apply: sub_gen; apply: (allP wu).
Qed.

Definition T2mor : {presmorph R -> T2_pres}.
apply: idmorRR'.
- by move=> u v wu wv; exact: sub_2.
- exact: sub_words_of_T2.
Defined.

Definition T2inv : {freemon A} -> {freemon A} :=
  fun u => (\prod_(i <- u) if i != gen then [fmon i] else w)%M.
Fact T2inv_monmorphism : monmorphism T2inv.
Proof. by rewrite /T2inv; split => [|u v]; rewrite ?big_nil ?big_cat. Qed.
HB.instance Definition _ :=
  isMonMorphism.Build {freemon A} {freemon A} T2inv T2inv_monmorphism.

Lemma T2inv_gen : T2inv [:: gen] = w.
Proof. by rewrite /T2inv big_seq1 eqxx. Qed.
Lemma allP_T2inv u : all (mem (pgen R)) u -> T2inv u = u.
Proof.
rewrite /T2inv; elim: u => [| u0 u IHu] /=; first by rewrite big_nil.
rewrite big_cons => /andP[Pgen {}/IHu ->].
case: eqP gen_nP => [<- /[!Pgen] // | _ _] /=.
by rewrite -mul_catE cat1s.
Qed.
Lemma T2inv_w : T2inv w = w.
Proof. exact: allP_T2inv. Qed.

Lemma T2inv_rewrites_to u : rewrites_to Tietze2_relat (T2inv u) u.
Proof.
rewrite /T2inv; elim: u => [| u0 u /(rewrites_to_cat _) IHu] /=.
  by rewrite big_nil; exists [::].
rewrite big_cons -mul_catE -[u0 :: u]cat1s; apply: IHu.
case: eqP => [-> |_] /= ; last exact: rewrites_to_refl.
apply: rewrites_to1; rewrite /Tietze2_relat rewrites_rcons mem_cat.
apply/orP; left; apply/rewritesP.
by exists [::] [::] (w, [:: gen]); rewrite //= ?cats0 // inE.
Qed.
Lemma T2invE u : u = T2inv u %[mod T2_pres].
Proof.
apply: equiv_sym.
exact: (rewrites_to_equiv (T2inv_rewrites_to u)).
Qed.
Fact rewmorphism_T2inv : rewmorphism T2_pres R T2inv.
Proof.
rewrite /T2_pres => u v /= wu wv /rewritesP [pre suf [r1 r2]] /= eu ev.
rewrite eu ev  mem_rcons inE => /orP [/eqP [er1 er2] | rinR] /=.
  rewrite er1 er2 -cat1s !mul_catE !mmorphM /= -!mul_catE; apply: rewrites_to_stable.
  by rewrite T2inv_gen T2inv_w /T2inv big_nil cats0; apply: rewrites_to_refl.
rewrite !mul_catE !mmorphM /= -!mul_catE.
move/allP: (wf_relat R) => /=/(_ _ rinR) /= /andP[/allP_T2inv-> /allP_T2inv->].
by apply: rewrites_to1; apply/rewritesP; exists (T2inv pre) (T2inv suf) (r1, r2).
Qed.
Fact rewmorphism_inT2inv : rewmorphism_in T2_pres R T2inv.
Proof.
elim=> [_ |a u ihu]; first by rewrite /T2inv big_nil.
rewrite inE /= mem_rcons inE; case/andP=> ha hu.
rewrite /T2inv big_cons; case/orP: ha => ha.
- by rewrite ha /= inE all_cat wall; apply: ihu.
- case: ifP; last first.
    by move/negbT; rewrite negbK => /eqP ea; move: gen_nP; rewrite -ea ha.
  by move=> aNg; rewrite inE all_cat /= ha; apply: ihu.
Qed.
HB.instance Definition _ :=
  isPresMorphism.Build A A T2_pres R T2inv rewmorphism_T2inv rewmorphism_inT2inv.

Lemma T2morK u : all (mem (pgen R)) u -> T2inv (T2mor u) = u %[mod R].
Proof. by move/allP_T2inv => ->; apply: equiv_refl. Qed.
Lemma T2invK v : T2mor (T2inv v) = v %[mod T2_pres].
Proof. exact: (equiv_trans (equiv_refl _ _) (equiv_sym (T2invE v))). Qed.

Fact T2invK_in v :
  v \in words_of T2_pres -> T2mor (T2inv v) = v %[mod T2_pres].
Proof. by move => _; exact: T2invK. Qed.
Definition isopres_Tietze2 : isopres R T2_pres :=
  IsoPres T2morK T2invK_in.

Lemma isopres_Tietze2E : isopres_Tietze2 = id :> (_ -> _).
Proof. by []. Qed.

End Tietze2.

Lemma Tietze_add_gen A (R1 R2 : pres A) (g : A) (w : word A) :
  pgen R2 = rcons (pgen R1) g -> prelat R2 = rcons (prelat R1) (w, [:: g]) ->
  w \in words_of R1 -> g \notin (pgen R1) -> isopres R1 R2.
Proof.
move=> eqgen eqrelat allw gok.
suff -> : R2 = T2_pres allw gok by apply: isopres_Tietze2.
by apply/eqP; rewrite -eqpresE /= eqgen eqrelat !eqxx.
Defined.

Lemma Tietze_add_gen_swap A (R1 R2 : pres A) (g : A) (w : word A) :
  pgen R2 = rcons (pgen R1) g -> prelat R2 = rcons (prelat R1) ([:: g], w) ->
  w \in words_of R1 -> g \notin (pgen R1) -> isopres R1 R2.
Proof.
move=> eqgen eqrelat allw cok.
apply: (isopres_trans (isopres_Tietze2 allw cok)).
apply: isopres_eq => u v.
rewrite /words_of /= /Tietze2_gen {}eqgen.
suff /eq_equiv_undirected /(_ u v) Heq :
    undirected (Tietze2_relat R1 g w) =i undirected R2.
  by split => [][-> -> /Heq].
case=> x y; rewrite !mem_undirected {}eqrelat /Tietze2_relat.
rewrite !mem_rcons !inE.
case: (_ \in prelat R1); rewrite ?orbT //.
case: (_ \in prelat R1); rewrite ?orbT //= !orbF orbC.
by rewrite !xpair_eqE ![_ && (y == _)]andbC.
Defined.


Section RewritingTheory.

Variable T : choiceType.
Implicit Types (R : relat T) (u v w x y : word T).

Definition decreasing (C : rel (word T)) R := all (fun r => C r.2 r.1) R.
Definition terminating R := well_founded (fun v u => v \in rewrites R u).
Definition joinable R u v :=
  exists2 w, rewrites_to R u w & rewrites_to R v w.
Definition locconfluent R := forall u v1 v2,
  v1 \in rewrites R u -> v2 \in rewrites R u -> joinable R v1 v2.
Definition confluent R := forall u v1 v2,
  rewrites_to R u v1 -> rewrites_to R u v2 -> joinable R v1 v2.
Definition convergent R := confluent R /\ terminating R.

Definition normal R u := rewrites R u == [::].
Definition normalf R u v := normal R v /\ rewrites_to R u v.

Lemma joinable_refl R u : joinable R u u.
Proof. by exists u; apply: rewrites_to_refl. Qed.
Lemma joinableC R u v : joinable R u v -> joinable R v u.
Proof. by case=> w uw vw; exists w. Qed.
Lemma joinable_stable R u v1 v2 w :
  joinable R v1 v2 -> joinable R (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof. by case=> r r1 r2; exists (u ++ r ++ w); apply: rewrites_to_stable. Qed.


Section Confluence.

Variable (R : relat T).
Hypothesis Rconfl : confluent R.

Lemma normalE u v : normal R u -> rewrites_to R u v -> u = v.
Proof.
move/eqP => noru [[_ {v}-> // | w pth /= /andP[/[swap] _ ]]].
by rewrite noru.
Qed.
Lemma infix_normal u v : infix v u -> normal R u -> normal R v.
Proof.
rewrite /normal => /infixP[pre][suf] {u}-> /eqP noru.
apply/negP => /negP.
case H : (rewrites R v) => [| u r] // _.
have {H} : u \in rewrites R v by rewrite H inE eqxx.
by move/(rewrites_stable pre suf); rewrite noru.
Qed.

Lemma confluentE u v1 v2 : normalf R u v1 -> normalf R u v2 -> v1 = v2.
Proof.
case=> /normalE norv1 /Rconfl HC; case=> /normalE norv2 {}/HC.
by case=> w /norv1-> /norv2->.
Qed.
Lemma normalf_rewrite0 u : rewrites R u == [::] -> normalf R u u.
Proof. by move=> H; split; last exact: rewrites_to_refl. Qed.
Lemma normalf_rewrites u v w :
  normalf R u w -> v \in rewrites (undirected R) u -> normalf R v w.
Proof.
case=> norw u_w; rewrite rewrites_undirected orbC.
move=> /orP[/rewrites_to1 v_u | /rewrites_to1 u_v]; split; try exact: norw.
  exact: (rewrites_to_trans _ u_w).
by have [w0 /(normalE norw) <-{w0}] := Rconfl u_w u_v.
Qed.
Lemma normalf_equivE u w :
  normalf R u w -> forall v, normalf R v w <-> u = v %[mod R].
Proof.
move=> noruw v; split.
  case=> _ /rewrites_to_equiv/equiv_sym/(equiv_trans _); apply.
  by move: noruw => [_ /rewrites_to_equiv].
case=> pth Hpth {v}->.
elim: pth u noruw Hpth => // [p0 pth IHpth] u noruw /=.
by move=> /andP[/(normalf_rewrites noruw)/IHpth].
Qed.
Lemma normalf_equivP u1 v1 u2 v2 :
  normalf R u1 v1 -> normalf R u2 v2 -> reflect (u1 = u2 %[mod R]) (v1 == v2).
Proof.
move=> nor1 nor2; apply (iffP eqP) => [eq|]; rewrite -(normalf_equivE nor1).
  by rewrite eq.
by move/confluentE; apply.
Qed.

End Confluence.


Lemma terminatingP R : terminating R ->
                       well_founded (fun v u => exists2 w : word T,
                                         w \in rewrites R u & rewrites_to R w v).
Proof.
move=> wf; elim/(well_founded_ind wf) => u IHu.
apply: Acc_intro => v [/= w {}/IHu Accw /rewrites_toP[<- // |]].
case=> /= w1 w_w1 w1_v.
by apply: (Acc_inv Accw); exists w1.
Qed.

Lemma diamond R : terminating R -> locconfluent R -> convergent R.
Proof.
move=> term loc; split; last exact: term.
move: term => /terminatingP wf; elim/(well_founded_ind wf) => u IHu v1 v2.
have {}IHu w y : w \in rewrites R u -> rewrites_to R w y ->
          forall v1 v2, rewrites_to R y v1 -> rewrites_to R y v2 ->
        exists2 w : word T, rewrites_to R v1 w & rewrites_to R v2 w.
  by move=> w_u w_y; apply: IHu; exists w.
move/rewrites_toP => [-> v1_v2| [/= w1 u_w1 w1_v1]].
  by exists v2; last exact: rewrites_to_refl.
move/rewrites_toP => [<- | [/= w2 u_w2 w2_v2]].
  exists v1; first exact: rewrites_to_refl.
  exact: (rewrites_to_trans (rewrites_to1 u_w1) w1_v1).
have [l w1_l w2_l] := loc _ _ _ u_w1 u_w2.
have [l1 v1_l1 l_l1] := IHu w1 w1 u_w1 (rewrites_to_refl R w1) v1 l w1_v1 w1_l.
have [l2 v2_l2 l_l2] := IHu w2 w2 u_w2 (rewrites_to_refl R w2) v2 l w2_v2 w2_l.
have [z l1_z l2_z] := IHu w1 l u_w1 w1_l l1 l2 l_l1 l_l2.
exists z.
- exact: rewrites_to_trans v1_l1 l1_z.
- exact: rewrites_to_trans v2_l2 l2_z.
Qed.

(** * Note : I include trivial spairs and npairs where u = v *)
Variant spair R u v : Prop :=
  SPair: forall (pre mid suf: word T) (rpre rsuf : word T * word T),
      rpre \in R -> rsuf \in R
      -> mid != [::] -> rpre.1 = pre ++ mid -> rsuf.1 = mid ++ suf
      -> u = rpre.2 ++ suf -> v = pre ++ rsuf.2 -> spair R u v.
Variant npair R u v : Prop :=
  NPair: forall (pre mid suf: word T) (rw rmid : word T * word T),
      rw \in R -> rmid \in R
      -> rw.1 = pre ++ mid ++ suf -> rmid.1 = mid
      -> u = rw.2 -> v = pre ++ rmid.2 ++ suf -> npair R u v.

Definition all_spairs_rule (r1 r2 s1 s2 : word T) :=
  [seq (r2 ++ drop (size r1 - shift) s1, take shift r1 ++ s2) |
    shift <- iota 0 (size r1) & prefix (drop shift r1) s1].
Definition all_spairs R :=
  flatten [seq all_spairs_rule r.1 r.2 s.1 s.2 | r <- R, s <- R].
Definition all_npairs_rule (r1 r2 s1 s2 : seq T) :=
  [seq (r2, take shift r1 ++ s2 ++ drop (shift + size s1) r1) |
    shift <- iota 0 (size r1 - size s1).+1 & s1 == take (size s1) (drop shift r1)].
Definition all_npairs R :=
  flatten [seq all_npairs_rule r.1 r.2 s.1 s.2 | r <- R, s <- R].


Lemma all_spairsP R u v : reflect (spair R u v) ((u, v) \in all_spairs R).
Proof.
apply (iffP flattenP) => /=.
  case=> seqp /allpairsP/=[[[r1 r2] [s1 s2] /= [rinR sinR] {seqp}->]].
  rewrite /all_spairs_rule => /mapP[/= shift].
  rewrite mem_filter mem_iota leq0n add0n /= => /andP[].
  move=> /prefixP[suf eqs1] ltshift [{u}->{v}->].
  pose pre := take shift r1.
  pose mid := drop shift r1.
  exists pre mid suf (r1, r2) (s1, s2) => //=.
  - apply/negP=> /eqP eqmid.
    have := congr1 size (cat_take_drop shift r1).
    rewrite size_cat size_take ltshift => eq.
    by move: ltshift; rewrite -eq -/mid eqmid /= addn0 ltnn.
  - by rewrite /pre /mid cat_take_drop.
  - by congr cat; rewrite eqs1 drop_cat size_drop ltnn subnn drop0.
case=> pre mid suf [r1 r2] [s1 s2] rinR sinR /= midn0 eqr1 eqs1 {u}->{v}->.
have eqmid : mid = drop (size pre) r1 by rewrite eqr1 drop_size_cat.
exists (all_spairs_rule r1 r2 s1 s2).
  by apply/allpairsP => /=; exists (r1, r2, (s1, s2)).
apply/mapP; exists (size pre).
  rewrite mem_filter mem_iota add0n /= -eqmid eqs1 prefix_prefix /=.
  rewrite eqr1 -[size pre]addn0 size_cat ltn_add2l lt0n.
  by move: midn0; case mid.
by rewrite eqs1 eqr1 take_size_cat // size_cat addKn drop_size_cat.
Qed.

Lemma all_npairsP R u v : reflect (npair R u v) ((u, v) \in all_npairs R).
Proof.
apply (iffP flattenP) => /=.
  case=> seqp /allpairsP/=[[[r1 r2] [s1 s2] /= [rinR sinR] {seqp}->]].
  rewrite /all_npairs_rule => /mapP[shift].
  rewrite mem_filter mem_iota leq0n add0n /= => /andP[].
  rewrite ltnS => /eqP eqs1 ltshift [{u}->{v}->].
  set pre := take shift r1.
  set suf := drop (shift + size s1) r1.
  exists pre s1 suf (r1, r2) (s1, s2) => //=.
  rewrite /pre eqs1 /suf take_drop.
  have -> : take shift r1 = take shift (take (size s1 + shift) r1).
    by rewrite take_takel ?leq_addl.
  by rewrite catA addnC !cat_take_drop.
case=> pre mid suf [r1 r2] [s1 s2] rinR sinR /= eqr1 eqs1 {u}->{v}->.
exists (all_npairs_rule r1 r2 s1 s2).
  by apply/allpairsP => /=; exists (r1, r2, (s1, s2)).
apply/mapP; exists (size pre).
  rewrite mem_filter mem_iota add0n /= ltnS.
  rewrite eqr1 eqs1 drop_size_cat // take_size_cat // eqxx /=.
  by rewrite !size_cat [size mid + _]addnC addnA addnK leq_addr.
by rewrite eqr1 eqs1 take_size_cat // -size_cat !catA drop_size_cat.
Qed.


Section PredicateOnNSPairs.

Variable p : pred (word T * word T).

Definition all_pred_spairs_rule (r1 r2 s1 s2 : seq T) :=
  all (fun shift => (prefix (drop shift r1) s1)
                  ==> p (r2 ++ drop (size r1 - shift) s1, take shift r1 ++ s2))
      (iota 0 (size r1)).
Definition all_pred_spairs R :=
  all (fun r => all (fun s => all_pred_spairs_rule r.1 r.2 s.1 s.2) R) R.

Lemma all_pred_spairsE R : all_pred_spairs R = all p (all_spairs R).
Proof.
rewrite /all_pred_spairs /all_spairs.
elim: {2 4}R => [// | /= [r1 r2] R1 IHR1].
rewrite flatten_cat all_cat; congr andb => //= {R1 IHR1}.
elim: R => [// | [s1 s2] R IHR] /=.
rewrite !(flatten_cat, all_cat); congr andb => //= {R IHR}.
rewrite /all_pred_spairs_rule /all_spairs_rule.
by rewrite all_map all_filter; apply: eq_all.
Qed.

Definition all_pred_npairs_rule (r1 r2 s1 s2 : seq T) :=
  all (fun shift => (prefix s1 (drop shift r1))
                  ==> p (r2, take shift r1 ++ s2 ++ drop (shift + size s1) r1))
      (iota 0 (size r1 - size s1).+1).
Definition all_pred_npairs R :=
  all (fun r => all (fun s => all_pred_npairs_rule r.1 r.2 s.1 s.2) R) R.

Lemma all_pred_npairsE R : all_pred_npairs R = all p (all_npairs R).
Proof.
rewrite /all_pred_npairs /all_npairs.
elim: {2 4}R => [// | /= [r1 r2] R1 IHR1].
rewrite flatten_cat all_cat; congr andb => //= {R1 IHR1}.
elim: R => [// | [s1 s2] R IHR] /=.
rewrite !(flatten_cat, all_cat); congr andb => //= {R IHR}.
rewrite /all_pred_npairs_rule /all_npairs_rule.
rewrite all_map all_filter; apply: eq_all => i /=.
by rewrite prefixE eq_sym.
Qed.

End PredicateOnNSPairs.


Lemma nspair_confluence R :
  (forall u v, npair R u v -> joinable R u v) ->
  (forall u v, spair R u v -> joinable R u v) -> locconfluent R.
Proof.
move=> npairconfl  spairconfl u v1 v2.
move=> /rewritesP[pre1 suf1 r1 {u}->{v1}-> r1inR].
move=> /rewritesP[pre2 suf2 r2  equ {v2}-> r2inR].
wlog lt12 : pre1 suf1 pre2 suf2 r1 r1inR r2 r2inR equ / size pre1 <= size pre2.
  move=> Hwlog.
  case: (leqP (size pre1) (size pre2)) => [le12 | /ltnW le21]; first exact: Hwlog.
  exact/joinableC/Hwlog.
case: r1 r2 r1inR r2inR equ => [r1 r2] [s1 s2] r1inR r2inR /= equ.
move: equ => /(cat2E lt12) {lt12} [a equ {pre2}->].
case: (leqP (size r1) (size a)) => [ler1_a | lea_r1].
  (** Trivial pair *)
  move: equ => /(cat2E ler1_a) {ler1_a} [mid {suf1}->{a}->].
  rewrite -!catA.
  exists (pre1 ++ r2 ++ mid ++ s2 ++ suf2); apply/rewrites_to1/rewritesP.
  - by exists (pre1 ++ r2 ++ mid) suf2 (s1, s2); rewrite ?catA.
  - by exists pre1 (mid ++ s2 ++ suf2) (r1, r2); rewrite ?catA.
move: equ => /esym/(cat2E (ltnW lea_r1)) [b] equ eqr1.
case: (leqP (size s1) (size b)) => [les1_b | /ltnW leb_s1].
  (** Nested pair *)
  move: equ => /(cat2E les1_b) {les1_b} [c {suf2}-> eqb].
  rewrite -!catA [a ++ _]catA [(a ++ s2) ++ _]catA; apply joinable_stable.
  rewrite -catA; apply: npairconfl => {spairconfl}.
  exists a s1 c (r1, r2) (s1, s2) => //=.
  by rewrite eqr1 eqb.
(** True critical Spair *)
move: equ => /esym/(cat2E leb_s1) {leb_s1} [c {suf1}-> eqs1].
rewrite -!catA [r2 ++ _]catA [a ++ _]catA; apply joinable_stable.
apply: spairconfl => {npairconfl}.
exists a b c (r1, r2) (s1, s2) => //=.
by apply/negP => /eqP eqb; move: lea_r1; rewrite eqr1 eqb cats0 ltnn.
Qed.

Lemma spair_confluence R :
  (forall u v, npair R u v -> u = v) ->
  (forall u v, spair R u v -> joinable R u v) -> locconfluent R.
Proof.
move=> no_npair; apply: nspair_confluence => u v /no_npair ->.
exact: joinable_refl.
Qed.

(** Compute a normal form using a rewriter function [rew1] *)
(** The rewriter function must verify the specification *)
Section Normalization.

Variable (R : relat T).
Variable (rew1 : word T -> option (word T)).
Hypothesis (rew1P : rewrites1_Ok R rew1).

Fixpoint norfuel fuel u :=
  if fuel is fuel'.+1 then
    if rew1 u is Some v then norfuel fuel' v else (u, true)
  else (u, false).

(** The same with exponential fuel for efficiency *)
Fixpoint norfuel2 fuel u :=
  if fuel is fuel'.+1 then
    if rew1 u is Some u1 then
      let rec := norfuel2 fuel' u1 in
      if rec is (u2, false) then norfuel2 fuel' u2 else rec
    else (u, true)
  else (u, false).
Definition expfuel fuel := (2 ^ fuel).-1.

Lemma norfuelD f1 f2 u :
  norfuel (f1 + f2) u =
    let rec := norfuel f1 u in
    if rec is (u', false) then norfuel f2 u' else rec.
Proof.
elim: f1 u => [|f1 IHf1]//= u; rewrite -/(f1 + f2).
by case: rew1.
Qed.
Lemma norfuel2E fuel : norfuel2 fuel =1 norfuel (expfuel fuel).
Proof.
rewrite /expfuel.
elim: fuel => [| fuel IHfuel] u //=.
rewrite expnSr muln2 -addnn.
have -> : (2 ^ fuel + 2 ^ fuel).-1 = 1 + ((2 ^ fuel).-1 + (2 ^ fuel).-1).
  case: (2 ^ fuel) (expn_non2 fuel) => // n _ /=.
  by rewrite -/(addn _ _) !add1n addnS.
rewrite norfuelD /=; case: rew1 => // {}u.
rewrite IHfuel /= norfuelD /= -!IHfuel.
by case: norfuel2 => v b /=; rewrite IHfuel.
Qed.

Lemma rewrites_to_norfuel fuel u : rewrites_to R u (norfuel fuel u).1.
Proof.
elim: fuel u => [|fuel IHfuel] u /=; first exact: rewrites_to_refl.
case: rew1P => /= [w | _]; last exact: rewrites_to_refl.
by move/rewrites_to1/rewrites_to_trans; apply.
Qed.
Lemma norfuelT fuel u :
  (norfuel fuel u).2 -> normalf R u (norfuel fuel u).1.
Proof.
have:= rewrites_to_norfuel fuel u.
case Hnor : norfuel => [v b] /= rew Hb; rewrite {}Hb in Hnor.
split => // {rew}.
move: Hnor; elim: fuel u => //= fuel IHfuel u.
by case: rew1P => /= [w _ /IHfuel // | {IHfuel} norew [<-{v}]].
Qed.
Lemma norfuel2T fuel u :
  (norfuel2 fuel u).2 -> normalf R u (norfuel2 fuel u).1.
Proof. rewrite norfuel2E; exact: norfuelT. Qed.
Lemma norfuelF fuel u :
  ~~ (norfuel fuel u).2 ->
  exists pth, [/\ path (fun u v => v \in rewrites R u) u pth,
      (norfuel fuel u).1 = last u pth & size pth = fuel].
Proof.
elim: fuel u => [// | fuel IHfuel] /= u; first by move=> _; exists [::].
case: rew1P => [v Ruv /IHfuel | norew //].
move=> [pth [Hpth eqlast szpth]].
by exists (v :: pth); split; rewrite /= ?szpth //= Ruv Hpth.
Qed.

Lemma equivalence_fuelP fuel :
  confluent R -> forall u v,
      let (un, uok) := norfuel2 fuel u in
      let (vn, vok) := norfuel2 fuel v in
      uok && vok -> reflect (u = v %[mod R]) (un == vn).
Proof.
move=> confl u v.
case: norfuel2 (@norfuel2T fuel u) => /= un [/(_ is_true_true) uok /=| _];
  last by case: norfuel2.
case: norfuel2 (@norfuel2T fuel v) => /= vn [/(_ is_true_true) vok /= _|//].
exact: normalf_equivP.
Qed.

Variant check_convergence_result :=
  | Ok : check_convergence_result
  | NotDecreasing : check_convergence_result
  | HaveNpair : (word T * word T) -> check_convergence_result
  | HaveSpair : (word T * word T) -> check_convergence_result.
Definition is_Ok r := if r is Ok then true else false.

Definition spair_confluence_dec fuel :=
  if all (fun p => p.1 == p.2) (all_npairs R) then
    let spairs := filter_rev_tr (fun p => p.1 != p.2) (all_spairs R) in
    (* if normalisation fails by out of fuel but results agree *)
    (* we do have confluence                                   *)
    all (fun p => (norfuel2 fuel p.1).1 == (norfuel2 fuel p.2).1) spairs
  else false.

Definition check_convergence_and C fuel : bool :=
  (decreasing C R) && (spair_confluence_dec fuel).

Definition spair_confluence_loop fuel :=
  (all_pred_npairs (fun p => p.1 == p.2) R) &&
    (all_pred_spairs (fun p => (p.1 == p.2) ||
                         ((norfuel2 fuel p.1).1 == (norfuel2 fuel p.2).1)) R).

Definition check_convergence C fuel : check_convergence_result :=
  if ~~ (decreasing C R) then NotDecreasing
  else if has (fun p => p.1 != p.2) (all_npairs R)
       then HaveNpair (head ([::], [::]) (all_npairs R))
  else let spairs := filter (fun p => p.1 != p.2) (all_spairs R) in
      (* if normalisation fails by out of fuel but results agree *)
      (* we do have confluence                                   *)
  let pos := find (fun p => (norfuel2 fuel p.1).1 != (norfuel2 fuel p.2).1) spairs in
  if pos < size spairs then HaveSpair (nth ([::], [::]) spairs pos)
  else Ok.

Lemma check_convergenceE C fuel :
  is_Ok (check_convergence C fuel) = check_convergence_and C fuel.
Proof.
rewrite /check_convergence /check_convergence_and /spair_confluence_dec.
case: (decreasing C R) => [/=|//].
rewrite has_predC; case: (all _ _) => [/=|//].
rewrite filter_rev_trE all_rev.
move: (filter _ _) => S; rewrite -[all _ _]negbK -has_predC has_find.
by case: ltnP.
Qed.

Lemma spair_confluence_loopE fuel :
  spair_confluence_loop fuel = spair_confluence_dec fuel.
Proof.
rewrite /spair_confluence_loop /spair_confluence_dec /=.
rewrite all_pred_npairsE all_pred_spairsE.
case: all => //=.
rewrite filter_rev_trE all_rev all_filter; apply eq_all => [[p1 p2]] /=.
by rewrite implyNb.
Qed.

Lemma spair_confluenceP fuel :
  spair_confluence_dec fuel -> locconfluent R.
Proof.
rewrite /spair_confluence_dec /=.
case: allP => [/= nonpair | //].
rewrite (eq_all (a2 := fun p => (norfuel (expfuel fuel) p.1).1
                                == (norfuel (expfuel fuel) p.2).1)); first last.
  by move=> u; rewrite !norfuel2E.
rewrite filter_rev_trE all_rev.
have {nonpair}/spair_confluence loc_confl : forall u v, npair R u v -> u = v.
  by move=> u v /all_npairsP /nonpair /= /eqP ->.
move/allP => /= confl.
apply: loc_confl => u v Suv.
case: (altP (u =P v)) => [-> | nequv]; first by exists v; apply: rewrites_to_refl.
have /confl/eqP/= eqnor : (u, v) \in filter (fun p => p.1 != p.2) (all_spairs R).
  by rewrite mem_filter /= {}nequv /=; apply/all_spairsP.
by exists (norfuel (expfuel fuel) u).1 => [|/[!eqnor]]; exact: rewrites_to_norfuel.
Qed.

Lemma spair_confluence_loopP fuel :
  spair_confluence_loop fuel -> locconfluent R.
Proof. by rewrite spair_confluence_loopE => /spair_confluenceP. Qed.


Section WellFounded.

Variable C : rel (word T).
Hypothesis Cstable : forall u v1 v2 w,
    C v1 v2 -> C (u ++ v1 ++ w) (u ++ v2 ++ w).
Hypothesis C_wf : well_founded C.

Lemma decreasing_wf : decreasing C R -> terminating R.
Proof.
move=> /allP /= decr.
apply: (wf_impl _ C_wf) => x y /rewritesP[pre suf r {x}->{y}-> rinR].
by apply: Cstable; apply: decr.
Qed.

Lemma check_convergence_andP fuel :
  check_convergence_and C fuel -> convergent R.
Proof.
rewrite /check_convergence_and => /=.
case: (boolP (decreasing C R)) => [/= dec /spair_confluenceP | //].
exact: diamond (decreasing_wf dec).
Qed.

Lemma check_convergenceP fuel :
  is_Ok (check_convergence C fuel) -> convergent R.
Proof. by rewrite check_convergenceE; apply: check_convergence_andP. Qed.

End WellFounded.

End Normalization.


Section Terminating.

Variable R : relat T.
Hypothesis termR : terminating R.

Theorem terminating_normal u : {v | normalf R u v}.
Proof.
move/well_founded_induction_type: termR => ind; elim/ind: u => {ind} u IHu.
case Hrew : (rewrites1 R u) => [u' | {IHu}].
  move/rewrites1SomeP: Hrew => /[dup]/rewrites_to1 ruu {}/IHu.
  case => v [norv ruv]; exists v; split => //.
  exact: (rewrites_to_trans ruu).
exists u; split; first by move/eqP: Hrew; rewrite -rewrites0P.
exact: rewrites_to_refl.
Qed.
Corollary normal0 : normal R [::].
Proof.
case: (terminating_normal [::]) => u [+ _]; apply: infix_normal.
exact: infix0s.
Qed.

Definition normal_of u := let: exist res _ := terminating_normal u in res.
Lemma normalf_ofP u : normalf R u (normal_of u).
Proof. by rewrite /normal_of; case: terminating_normal. Qed.
Lemma normal_ofP u : normal R (normal_of u).
Proof. by case: (normalf_ofP u). Qed.
Lemma rewrites_to_normal_of u : rewrites_to R u (normal_of u).
Proof. by case: (normalf_ofP u). Qed.
Lemma equiv_normal_of u : u = normal_of u %[mod R].
Proof. exact/rewrites_to_equiv/rewrites_to_normal_of. Qed.
Lemma normal_of_normal u : normal R u -> normal_of u = u.
Proof.
move/eqP => noru; case: (normalf_ofP u) => _.
by case => [[|p0 p]] //= /andP[]; rewrite noru.
Qed.

End Terminating.

Section NormalOf.

Variables (R : relat T) (cvR : convergent R).

Lemma normal_of_id u : normal_of cvR.2 (normal_of cvR.2 u) = normal_of cvR.2 u.
Proof.
apply: (confluentE cvR.1 (normalf_ofP cvR.2 _)).
exact/normalf_rewrite0/normal_ofP.
Qed.

Lemma normal_of_cat u v :
  normal_of cvR.2 (normal_of cvR.2 u ++ normal_of cvR.2 v) =
    normal_of cvR.2 (u ++ v).
Proof.
apply: (confluentE cvR.1 (normalf_ofP cvR.2 _)).
rewrite (normalf_equivE cvR.1 (normalf_ofP cvR.2 _)).
exact/rewrites_to_cat/equiv_normal_of/equiv_normal_of.
Qed.
Lemma normal_of_catl u v :
  normal_of cvR.2 (u ++ normal_of cvR.2 v) = normal_of cvR.2 (u ++ v).
Proof. by rewrite -normal_of_cat normal_of_id normal_of_cat. Qed.
Lemma normal_of_catr u v :
  normal_of cvR.2 (normal_of cvR.2 u ++ v) = normal_of cvR.2 (u ++ v).
Proof. by rewrite -normal_of_cat normal_of_id normal_of_cat. Qed.

Lemma equiv_normal_ofE u v :
  u = v %[mod R] <-> normal_of cvR.2 u = normal_of cvR.2 v.
Proof.
split => [] Heq.
  by apply/eqP/(normalf_equivP cvR.1); try exact: normalf_ofP.
apply: (equiv_trans (equiv_normal_of cvR.2 u)); rewrite Heq.
exact/equiv_sym/equiv_normal_of.
Qed.

End NormalOf.


Theorem convergentrel_dec R :
  convergent R -> forall u v, decidable (u = v %[mod R]).
Proof.
case=> Hconfl Hterm u v.
case: (terminating_normal Hterm u) => un noru.
case: (terminating_normal Hterm v) => vn norv.
exact: decP (normalf_equivP Hconfl noru norv).
Qed.

Corollary convergent_dec (P : pres T) : convergent P -> WPdecidable P.
Proof. by move/convergentrel_dec => H u v. Qed.

End RewritingTheory.



(** Permuting the generators of a presentation *)
Section PermGen.

Context {A : choiceType} (P : pres A) (gens : seq A).
Hypothesis (perm_gen : perm_eq gens (pgen P)).

Fact pgen_uniq : uniq gens.
Proof. by rewrite (perm_uniq perm_gen) uniq_pgen. Qed.
Fact corr_perm_gen : all_relwords P (mem gens).
Proof.
have := wf_relat P; apply: sub_all => [[r1 r2]] /=.
by rewrite !(eq_all (perm_mem perm_gen)).
Qed.
Definition perm_gen_pres := Pres pgen_uniq corr_perm_gen.

Lemma perm_gen_pres_decK : WPdecidable P -> WPdecidable perm_gen_pres.
Proof. exact/isopres_dec/pres_irrelevance_perm_eq. Qed.
Lemma perm_gen_pres_dec : WPdecidable perm_gen_pres -> WPdecidable P.
Proof.
apply/isopres_dec/pres_irrelevance_perm_eq => //.
by rewrite perm_sym.
Qed.

End PermGen.


(** Dual of a presentation (i.e. reverting all relation words) *)
Section DualRelat.

Context {A : choiceType}.
Implicit Type (R : relat A) (u v : word A).

Definition dual_relat (r : word A * word A) := (rev r.1, rev r.2).
Definition dual_relats R := map dual_relat R.

Lemma dual_relatK : involutive dual_relat.
Proof. by rewrite /dual_relat => [][r1 r2] /=; rewrite !revK. Qed.
Lemma dual_relatsK : involutive dual_relats.
Proof.
rewrite /dual_relats => R; rewrite -map_comp map_id_in //= => r _.
exact: dual_relatK.
Qed.
Lemma swap_revC : swap \o dual_relat =1 dual_relat \o swap.
Proof. by case=> r1 r2; rewrite /swap /dual_relat /=. Qed.

Lemma rev_rewrites_impl R u v :
  v \in rewrites R u -> rev v \in rewrites (dual_relats R) (rev u).
Proof.
move/rewritesP => [pre suf /= r {u}-> {v}-> rin]; apply/rewritesP.
exists (rev suf) (rev pre) (dual_relat r) => /=.
- by rewrite -!rev_cat catA.
- by rewrite -!rev_cat catA.
exact: map_f.
Qed.
Lemma rev_rewritesE R u v :
  (rev v \in rewrites (dual_relats R) (rev u)) = (v \in rewrites R u).
Proof.
by apply/idP/idP => /rev_rewrites_impl //; rewrite !revK dual_relatsK.
Qed.

Lemma rev_rewrites_to_impl R u v :
  rewrites_to R u v -> rewrites_to (dual_relats R) (rev u) (rev v).
Proof.
case=> pth Hpth {v}->.
exists (map rev pth); last by rewrite last_map.
apply: (homo_path (f := rev) _ Hpth) => {Hpth}u v.
exact: rev_rewrites_impl.
Qed.
Lemma rev_rewrites_toE R u v :
  rewrites_to (dual_relats R) (rev u) (rev v) <-> rewrites_to R u v.
Proof.
split; last exact: rev_rewrites_to_impl.
by move/rev_rewrites_to_impl; rewrite !revK dual_relatsK.
Qed.
Lemma undirected_dual_relat R :
  undirected (dual_relats R) = dual_relats (undirected R).
Proof.
rewrite /undirected /dual_relats map_cat; congr cat.
by rewrite -!map_comp; apply eq_map; exact: swap_revC.
Qed.
Lemma rev_equivE R u v :
  rev u = rev v %[mod dual_relats R] <-> u = v %[mod R].
Proof.
split => /rev_rewrites_toE //; rewrite undirected_dual_relat //.
by rewrite dual_relatsK !revK.
Qed.

End DualRelat.

Section DualPres.

Context {A : choiceType}.
Implicit Type (R : pres A) (u v : word A).

Lemma dual_pres_subproof R : all_relwords (dual_relats R) (mem (pgen R)).
Proof.
have:= wf_relat R; rewrite /all_relwords /dual_relats => /allP /= H.
apply/allP => /= [[s1 s2]] /mapP[/=[r1 r2 /H /andP[/= all1 all2]] [{s1}-> {s2}->]].
by rewrite !all_rev all1 all2.
Qed.
Definition dual_pres R := Pres (uniq_pgen R) (dual_pres_subproof R).

Lemma dual_presK R : dual_pres (dual_pres R) = R.
Proof.
apply/eqP; rewrite -eqpresE /= eqxx /= /dual_relats -map_comp.
rewrite (eq_map (g := id)) ?map_id // => [[x1 x2]].
by rewrite /dual_relat /= !revK.
Qed.

Lemma dual_pres_rewritesE R u v :
  (rev v \in rewrites (dual_pres R) (rev u)) = (v \in rewrites R u).
Proof. exact: rev_rewritesE. Qed.
Lemma dual_pres_rewrites_toE R u v :
  rewrites_to (dual_pres R) (rev u) (rev v) <-> rewrites_to R u v.
Proof. exact: rev_rewrites_toE. Qed.
Lemma dual_pres_equivE R u v :
  rev u = rev v %[mod (dual_pres R)] <-> u = v %[mod R].
Proof. exact: rev_equivE. Qed.
Lemma dual_pres_equiv_impl R u v :
  rev u = rev v %[mod (dual_pres R)] -> u = v %[mod R].
Proof. by rewrite dual_pres_equivE. Qed.
Lemma dual_pres_equiv_implK R u v :
  u = v %[mod R] -> rev u = rev v %[mod (dual_pres R)].
Proof. by rewrite dual_pres_equivE. Qed.

Lemma dual_decK R : WPdecidable (dual_pres R) -> WPdecidable R.
Proof.
have revw w : w \in words_of R -> rev w \in words_of R.
  by rewrite /words_of !unfold_in /= => H /[!all_rev].
move=> dec u v /revw/dec+/revw => /[apply].
case => [|Hrev]; first by move/dual_pres_equiv_impl; left. (* Univ inconsistency *)
by right=> H; apply: Hrev; rewrite dual_pres_equivE.
Qed.
Lemma dual_dec R : WPdecidable R -> WPdecidable (dual_pres R).
Proof. rewrite -{1}(dual_presK R); exact: dual_decK. Qed.

End DualPres.


(** Reversing the sense of the relations *)
Section FlipDirection.

Context {A : choiceType}.
Implicit Types (R : relat A) (P : pres A) (u v : word A).

Lemma flipped_rewrites1_impl R u v :
  v \in rewrites R u -> u \in rewrites (map swap R) v.
Proof.
case/rewritesP => pre suf r /= {u}-> {v}-> rinR.
by apply/rewritesP; exists pre suf (swap r) => //; apply: map_f.
Qed.

Lemma flipped_rewrites_to_impl R u v :
  rewrites_to R u v -> rewrites_to (map swap R) v u.
Proof.
case=> pth /[swap] {v}->; elim: pth u => [|p0 pth IHpth] u /=.
  move=> _; exact: rewrites_to_refl.
case/andP => /flipped_rewrites1_impl Hp0 {}/IHpth /rewrites_to_trans; apply.
exact: rewrites_to1.
Qed.
Lemma flipped_rewrites_toE R u v :
  rewrites_to (map swap R) v u <-> rewrites_to R u v.
Proof.
split; last exact: flipped_rewrites_to_impl.
by move/flipped_rewrites_to_impl; rewrite (mapK swapK).
Qed.
Lemma flipped_equivE R u v : u = v %[mod map swap R] <-> u = v %[mod R].
Proof.
have swap_inj := @swap_inj (word A).
apply: eq_equiv_undirected => -[r1 r2].
by rewrite !mem_undirected -{1}/(swap (r2, r1)) -{2}/(swap (r1, r2)) !mem_map // orbC.
Qed.

Lemma flipped_pres_subproof (P : pres A) :
  all_relwords (map swap (prelat P)) (mem (pgen P)).
Proof.
have:= wf_relat P; rewrite /all_relwords all_map.
set p1 := (X in all X _ -> _); set p2 := (X in _ -> all X _).
suff /eq_all -> : p1 =1 p2 by [].
by rewrite {}/p1 {}/p2 => -[u v] /=; rewrite andbC.
Qed.
Definition flipped_pres P := Pres (uniq_pgen P) (flipped_pres_subproof P).

Lemma words_of_flipped P u :
  (u \in words_of (flipped_pres P)) = (u \in words_of P).
Proof. by rewrite !unfold_in. Qed.

Lemma flipped_presK : involutive flipped_pres.
Proof.
move=> P; apply/eqP; rewrite -eqpresE /= eqxx /= -map_comp.
by apply/eqP; rewrite -[RHS]map_id; apply eq_map => [[u v]]; rewrite /= swapK.
Qed.

Lemma flipped_pres_equivE P u v :
  u = v %[mod (flipped_pres P)] <-> u = v %[mod P].
Proof. exact: flipped_equivE. Qed.
Lemma flipped_pres_dec P : WPdecidable (flipped_pres P) -> WPdecidable P.
Proof.
move=> Hdec u v; rewrite -!(words_of_flipped P) => uP vP.
by have [] := Hdec _ _ uP vP => /(flipped_pres_equivE P u v) H; [left | right].
Qed.

End FlipDirection.


(** Renaming the generators *)
Section RenameGenImpl.

Context {A B : choiceType} {RA : relat A} {RB : relat B}.
Variable (newg : A -> B).

Definition rgen_rels := fun r => (map newg r.1, map newg r.2).

Hypothesis rrelatE : RB = [seq rgen_rels i | i <- RA].

Lemma rgen_rewrites_impl u v :
  v \in rewrites RA u -> map newg v \in rewrites RB (map newg u).
Proof.
move/rewritesP => [pre suf /=[r1 r2] {u}-> {v}-> rin]; apply/rewritesP.
exists (map newg pre) (map newg suf) (rgen_rels (r1, r2)) => /=.
- by rewrite -!map_cat.
- by rewrite -!map_cat.
by rewrite rrelatE map_f.
Qed.
Lemma rgen_rewrites_to_impl u v :
  rewrites_to RA u v -> rewrites_to RB (map newg u) (map newg v).
Proof.
case=> pth Hpth {v}->.
exists (map (map newg) pth); last by rewrite last_map.
exact: (homo_path (f := map newg) rgen_rewrites_impl Hpth).
Qed.

Variable (newg_inv : B -> A).
Hypothesis newgK : cancel newg newg_inv.
Let newg_inj := can_inj newgK.

Lemma rgen_rewritesE u (w : word B) :
  w \in rewrites RB (map newg u) -> exists v, w = map newg v.
Proof.
move=> /rewritesP[pre suf [r1 r2] /= eq1 eq2].
rewrite rrelatE => /mapP[/= [s1 s2] sin][eqr1 eqr2]; subst r1 r2.
move Hpre : (size pre) eq2 => szpre.
have eqpre : map newg ((take szpre) u) = pre.
  move: eq1 => /(congr1 (take szpre)).
  by rewrite -map_take take_size_cat.
move: eq1; rewrite -eqpre !catA -!map_cat => eq1.
have {Hpre eqpre} eqsuf : map newg (drop (szpre + size s1) u) = suf.
  move: eq1 => /(congr1 (drop (szpre + size s1))).
  rewrite -map_drop drop_size_cat // size_map size_cat.
  by rewrite -{2}Hpre -eqpre size_map.
move: eq1; rewrite -{}eqsuf -!map_cat.
move=> /(inj_map newg_inj) equ {w}->; rewrite equ -!catA.
by set v := (X in map newg X); exists v.
Qed.
Lemma rgen_rewrites_toE u (w : word B) :
  rewrites_to RB (map newg u) w -> exists v, w = map newg v.
Proof.
case=> pth Hpth {w}->.
elim: pth u Hpth => [/= u _ | p0 pth IHpth u /=]; first by exists u.
by case/andP => /rgen_rewritesE[v {p0}-> {}/IHpth].
Qed.

Lemma rgen_terminating : terminating RB -> terminating RA.
Proof. by apply: wf_f => x y; apply: rgen_rewrites_impl. Qed.

End RenameGenImpl.

Lemma rgen_equiv_impl
  {A B : choiceType} {RA : relat A} {RB : relat B} (newg : A -> B) :
  RB = [seq rgen_rels newg i | i <- RA] ->
  forall u v, u = v %[mod RA] -> (map newg u) = (map newg v) %[mod RB].
Proof.
move=> eqR u v /rgen_rewrites_to_impl; apply.
rewrite /undirected map_cat {}eqR; congr cat.
by rewrite -!map_comp; apply eq_map => {u v} [][r1 r2].
Qed.


Section RenameGenRelat.

Context {A B : choiceType} {RA : relat A} {RB : relat B}.

Variable (newg : A -> B) (newg_inv : B -> A).
Hypothesis newgK : cancel newg newg_inv.
Hypothesis rrelatE : RB = [seq rgen_rels newg i | i <- RA].

Implicit Type u v : word A.

Lemma rrelat_invE : RA = [seq rgen_rels newg_inv i | i <- RB].
Proof.
rewrite rrelatE -map_comp; apply/esym/map_id_in => [][/= r1 r2 _].
by rewrite /rgen_rels /= -!map_comp !(eq_map newgK) !map_id.
Qed.

Lemma rgen_rewrites u v :
  (v \in rewrites RA u) = (map newg v \in rewrites RB (map newg u)).
Proof.
apply/idP/idP => [/(rgen_rewrites_impl rrelatE) // |].
move/(rgen_rewrites_impl rrelat_invE).
by rewrite -!map_comp !(eq_map newgK) !map_id.
Qed.
Lemma rgen_rewrites_to u v :
  rewrites_to RA u v <-> rewrites_to RB (map newg u) (map newg v).
Proof.
split; first exact: rgen_rewrites_to_impl.
move/(rgen_rewrites_to_impl rrelat_invE).
by rewrite -!map_comp !(eq_map newgK) !map_id.
Qed.
Lemma rgen_equiv u v :
  u = v %[mod RA] <-> (map newg u) = (map newg v) %[mod RB].
Proof.
split; first exact: rgen_equiv_impl.
move/(rgen_equiv_impl rrelat_invE).
by rewrite -!map_comp !(eq_map newgK) !map_id.
Qed.

Lemma rgen_joinable u v :
  joinable RB (map newg u) (map newg v) -> joinable RA u v.
Proof.
case=> x /[dup] /(rgen_rewrites_toE rrelatE newgK)[w {x}->].
by rewrite -!rgen_rewrites_to => RAuw RAvW; exists w.
Qed.
Lemma rgen_confluent : confluent RB -> confluent RA.
Proof.
move=> conflRB u v1 v2.
by rewrite !rgen_rewrites_to => /conflRB/[apply]/rgen_joinable.
Qed.
Lemma rgen_convergent : convergent RB -> convergent RA.
Proof. by case=> /rgen_confluent cRA /(rgen_terminating rrelatE). Qed.

End RenameGenRelat.


Section RenameGenDefs.

Context {A B : choiceType} (R : pres A).

Variable (newg : A -> B) (newg_inv : B -> A).
Hypothesis newgK : cancel newg newg_inv.

Implicit Types (u v : word A).

Let gens := map newg (pgen R).
Let rels := map (rgen_rels newg) (prelat R).

Fact gens_uniq: uniq gens.
Proof. by rewrite (map_inj_uniq (can_inj newgK)) (uniq_pgen R). Qed.
Fact wf_rels: all_relwords rels (mem gens).
Proof.
have ingens : preim newg (mem gens) =i mem (pgen R).
  move=> u; rewrite /gens /preim unfold_in /= mem_map //.
  exact: can_inj.
apply/allP =>/=[[u0 v0]]/mapP/=[[u v] /(allP (wf_relat R))/= uvin][{u0}-> {v0}->].
by rewrite !all_map !(eq_all ingens).
Qed.
Definition rgen_pres := Pres gens_uniq wf_rels.

Lemma pgen_rgenE : pgen rgen_pres = gens. Proof. by []. Qed.
Lemma prelat_rgenE : prelat rgen_pres = rels. Proof. by []. Qed.

Definition rgen_pres_terminating := rgen_terminating prelat_rgenE.
Definition rgen_pres_confluent := rgen_confluent newgK prelat_rgenE.
Definition rgen_pres_convergent := rgen_convergent newgK prelat_rgenE.

Lemma word_of_rgen_pres u :
  (map newg u \in words_of rgen_pres) = (u \in words_of R).
Proof.
rewrite /words_of !unfold_in /= !all_map.
apply: eq_all => i; rewrite /= /gens mem_map //.
exact: can_inj.
Qed.

Lemma rgen_pres_decK : WPdecidable rgen_pres -> WPdecidable R.
Proof.
move=> Hdec u v uR vR.
have /(_ (prelat R)) [Hnew Hinv] := rgen_equiv newgK erefl u v.
case: (Hdec (map newg u) (map newg v)); rewrite ?word_of_rgen_pres // => eq_uv.
  by left; apply Hinv.
by right => H1; apply: eq_uv; apply: Hnew.
Qed.

End RenameGenDefs.


Arguments Pres {A}.

Notation make_pres g r := (@Pres _ g r erefl erefl).
