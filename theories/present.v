(** * Monoid Presentations *)
(******************************************************************************)
(*      Copyright (C) 2021      Florent Hivert <florent.hivert@lri.fr>        *)
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
From mathcomp Require Import all_ssreflect.

Require Import monoids.

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

Reserved Notation "x = y %[mod e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %[mod  e ] ']'").

(* Potential PRs to MathComp *)
Section Compl.
Context {T : Type}.
Definition swap (p : T * T) := (p.2, p.1).
Lemma swapK : involutive swap. Proof. by move => [i j]. Qed.
Lemma swap_inj : injective swap. Proof. exact: (can_inj swapK). Qed.
Implicit Type u v : seq T.
Lemma catl_inj u : injective (cat u).
Proof. by elim: u => [|a u IHu] //= v1 v2 []; exact: IHu. Qed.
Lemma catr_inj u : injective (cat^~ u).
Proof.
move=> v1 v2 /(congr1 rev) /[!rev_cat] /catl_inj.
exact: (can_inj revK).
Qed.
End Compl.


Definition word (Alph : Type):= seq Alph.
Definition relat Alph := seq (word Alph * word Alph).

Section Defs.

Variable (Alph : choiceType).

Local Notation relat := (relat Alph).
Local Notation word := (word Alph).

Implicit Types (R : relat) (u v w x y : word) (p : word * word).

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
   a rewrite system is a list of rewrite rules.
   rewrites_front_spec R u v holds when u rewrites into v by applying a rw rule
    in R to a prefix of u. *)
Inductive rewrites_front_spec R u v : Prop :=
  RewritesFront : forall (suf : word) (rule : word * word),
      u = rule.1 ++ suf -> v = rule.2 ++ suf -> rule \in R
               -> rewrites_front_spec R u v.

(* rewrites_spec R u v when a rw rule in R applies rewrite u into v by applying
   a rule in R to an arbitrary subword of u *)
Inductive rewrites_spec R u v : Prop :=
  Rewrites : forall (pre suf : word) (rule : word * word),
      u = pre ++ rule.1 ++ suf -> v = pre ++ rule.2 ++ suf -> rule \in R
               -> rewrites_spec R u v.

Lemma rewrite_front_spec_cons R u v r1 r2:
  rewrites_front_spec R u v -> rewrites_front_spec ((r1, r2) :: R) u v.
Proof.
move=> [suf [s1 s2] /= {u}->{v}-> sinR].
by exists suf (s1, s2) => //=; rewrite inE sinR orbT.
Qed.
Lemma rewrites_front_specP R u v pre :
  rewrites_front_spec R u v -> rewrites_spec R (pre ++ u) (pre ++ v).
Proof. by move=> [suf r {u}->{v}-> rinR]; exists pre suf r. Qed.
Lemma cons_rewrites_spec R a u v :
  rewrites_spec R u v -> rewrites_spec R (a :: u) (a :: v).
Proof. by move=> [pre suf r /= {u}->{v}-> rinR]; exists (a :: pre) suf r. Qed.

(* Finds the first matching rule in R that matches a prefix of u and produces
   the rewriten v, or None. *)
Fixpoint rewrites1_front R u :=
  if R is (r1, r2) :: R' then
    if prefix r1 u then Some (r2 ++ drop (size r1) u)
    else rewrites1_front R' u
  else None.

(* Produces the list of all words v than can be obtained by rewriting a prefix
   of u with a rule in R *)
Fixpoint rewrites_front R u :=
  if R is (r1, r2) :: R' then
    if prefix r1 u then (r2 ++ drop (size r1) u) :: rewrites_front R' u
    else rewrites_front R' u
  else [::].

Lemma rewrite1_frontE R u :
  rewrites1_front R u = head None [seq Some v | v <- rewrites_front R u].
Proof. by elim: R => [// | [r1 r2] R IHR] /=; case: prefix. Qed.
Lemma rewrites_frontP R u v :
  reflect (rewrites_front_spec R u v) (v \in rewrites_front R u).
Proof.
apply (iffP idP); elim: R => [|[r1 r2] R IHR] //=.
- case: prefixP => [| _ {}/IHR[suf [s1 s2]/= {u}->{v}-> sinR]]; first last.
    by exists suf (s1, s2) => //=; rewrite inE sinR orbT.
  move=> [suf equ]; subst u => /=.
  rewrite inE => /orP[/eqP{v IHR}-> | {}/IHR].
    by exists suf (r1, r2); rewrite ?drop_size_cat // inE eqxx.
  exact: rewrite_front_spec_cons.
- by move=> [].
move=> [suf [s1 s2]/= equ eqv]; subst u v.
rewrite inE => /orP[/eqP[{r1}<-{r2}<-] | sinR].
  by rewrite prefix_prefix inE drop_size_cat // eqxx.
have {}/IHR : rewrites_front_spec R (s1 ++ suf) (s2 ++ suf) by exists suf (s1, s2).
by case: prefixP => _ //; rewrite inE orbC => ->.
Qed.
Lemma rewrites_front0P R u :
  (rewrites_front R u == [::]) = (rewrites1_front R u == None).
Proof. by rewrite rewrite1_frontE; case: rewrites_front. Qed.
Lemma rewrites1_frontP R u v :
  rewrites1_front R u = Some v -> v \in rewrites_front R u.
Proof.
rewrite rewrite1_frontE.
by case: rewrites_front => [//| w s] /= [<-{v}]; rewrite inE eqxx.
Qed.

Section DefRewrites.

Variable (R : relat).

(* Finds the first matching rule in R that matches a subword of u and produces
   the rewritten v, or None. *)
Fixpoint rewrites1 u :=
  if u is a :: u' then
    if rewrites1_front R u is Some u as res then res
    else option_map (cons a) (rewrites1 u')
  else rewrites1_front R [::].

(* Produces the list of all words v than can be obtained by rewriting
   u with a (single) rule in R *)
Fixpoint rewrites u :=
  if u is a :: u'
  then (rewrites_front R u) ++ [seq a :: v | v <- rewrites u']
  else rewrites_front R [::].

Lemma rewrite1E u :
  rewrites1 u = head None [seq Some v | v <- rewrites u].
Proof.
elim: u => /= [| a u ->]; rewrite rewrite1_frontE //.
by case: rewrites_front => //=; case: rewrites.
Qed.
Lemma rewrite1_in u v : rewrites1 u = Some v -> v \in rewrites u.
Proof.
by rewrite rewrite1E; case: rewrites => [//| a l [->]/=]; rewrite inE eqxx.
Qed.
Lemma rewritesP u v : reflect (rewrites_spec R u v) (v \in rewrites u).
Proof.
apply (iffP idP); elim: u v => [| a u IHu] v /=.
- by move=> /rewrites_frontP/(rewrites_front_specP [::]).
- rewrite mem_cat => /orP[/rewrites_frontP/(rewrites_front_specP [::]) //|].
  move=> /mapP[/= w {}/IHu /[swap]{v}->].
  exact: cons_rewrites_spec.
- move=> [] [|//] /[swap] [[/= [|//] b]] /= [|//] _ -> rinR /[!cats0].
  by apply/rewrites_frontP; exists [::] ([::], b); rewrite // cats0.
- rewrite mem_cat => -[pre suf [r1 r2] /= /[dup] equ-> {v}-> rinR].
  case: pre equ => [/=| b pre /= [{b}<-]] equ; apply/orP.
    by left; apply/rewrites_frontP; exists suf (r1, r2).
  right; rewrite mem_map; last by move=> ? ? [].
  by apply: IHu; rewrite {}equ; exists pre suf (r1, r2).
Qed.
Lemma rewrites0P u : (rewrites u == [::]) = (rewrites1 u == None).
Proof. by rewrite rewrite1E; case: rewrites. Qed.
Lemma rewrites1P u v : rewrites1 u = Some v -> v \in rewrites u.
Proof.
by rewrite rewrite1E; case: rewrites => [//| w s] /= [{v}<-]; rewrite inE eqxx.
Qed.

Lemma rewrites_rel u v : (u, v) \in R -> v \in rewrites u.
Proof.
move=> rin; apply/rewritesP.
by exists [::] [::] (u, v); rewrite //= cats0.
Qed.

(* rewrites_to u v holds when a sequence of rewriting with rules from R turns
  u into v. The sequence can be empty, i.e., the relation is reflexive *)
Inductive rewrites_to u v : Prop :=
  RewritesTo : forall pth, path (fun u v => v \in rewrites u) u pth ->
                  v = last u pth -> rewrites_to u v.
Arguments RewritesTo {u v} (pth).

Lemma rewrites_to1 u v : v \in rewrites u -> rewrites_to u v.
Proof. by move=> rew; exists [:: v]; rewrite //= andbT. Qed.

Lemma rewrites_to_refl : reflexivep rewrites_to.
Proof. by move=> x; exists [::]. Qed.
Hint Resolve rewrites_to_refl.

Lemma rewrites_to_trans : transitivep rewrites_to.
Proof.
move=> x y z [pathxy Hxy Hy] [pathyz Hyz Hz].
exists (pathxy ++ pathyz).
- by rewrite cat_path Hxy -Hy Hyz.
- by rewrite last_cat -Hy.
Qed.
Lemma rewrites_toP u v :
  rewrites_to u v
  <-> ((u = v) \/ (exists2 w, w \in rewrites u & rewrites_to w v)).
Proof.
split.
  move=> [[/= _ -> | w pth /= /andP[u_w Hpth] /= {v}->]]; first by left.
  by right; exists w; [exact: u_w | exists pth].
move=> [-> | [w /rewrites_to1]]; first exact: rewrites_to_refl.
exact: rewrites_to_trans.
Qed.
Lemma rewrites_stable u v1 v2 w :
  v2 \in rewrites v1 -> u ++ v2 ++ w \in rewrites (u ++ v1 ++ w).
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

Lemma rewrites_to_min CR :
  (forall p, p \in R -> CR p.1 p.2) ->
  reflexivep CR -> transitivep CR -> stablep CR ->
  forall u v, rewrites_to u v -> CR u v.
Proof.
move=> incl CR_refl CR_trans CR_stable u v [p path_p {v}->].
elim: p u path_p => [//=| p0 p IHp] u /= /andP[p0_u] {}/IHp; apply CR_trans.
move/rewritesP : p0_u => [pre suf [r1 pr] {u}->{p0}-> rinR] /=.
by apply: CR_stable; apply: (incl _ rinR).
Qed.


Section Symmetry.

Hypothesis Rsym : forall u v, (u, v) \in R -> (v, u) \in R.

Lemma rewrites_sym_impl x y :
  x \in rewrites y -> y \in rewrites x.
Proof.
move=> /rewritesP[pre suf [r1 r2] {y}->{x}-> rinR  /=].
apply/rewritesP; exists pre suf (r2, r1) => //.
exact: Rsym.
Qed.

Lemma rewrites_sym x y :
  (x \in rewrites y) = (y \in rewrites x).
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
- exact rewrites_to_stable.
- exact: rewrites_to_sym.
Qed.

End Symmetry.

End DefRewrites.

Lemma rewrites_cat R1 R2 u :
  rewrites (R1 ++ R2) u =i (rewrites R1 u) ++ (rewrites R2 u).
Proof.
move=> /= v; rewrite mem_cat; apply/idP/orP.
  move=> /rewritesP[pre suf r {u}->{v}-> ].
  by rewrite mem_cat => /orP[]; [left|right]; apply/rewritesP; exists pre suf r.
by move=> []/rewritesP[pre suf r {u}->{v}-> rinR];
       apply/rewritesP; exists pre suf r => //=; rewrite mem_cat rinR ?orbT.
Qed.
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
Lemma equiv_min CR :
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
move=> [p p_path {v}->]; exists p => //.
by move: p_path; apply (sub_path sub_rewrites).
Qed.
Lemma sub_undirected : {subset undirected R1 <= undirected R2}.
Proof.
move=> [u v]; rewrite !mem_cat => /orP[/sub_rule -> // |].
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

Lemma eq_rewrites u : (rewrites R1 u) =i (rewrites R2 u).
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

Lemma mmorph_cat u v : {morph f: x y  / x ++ y}.
Proof. exact: mmorphM. Qed.
Lemma mmorph_flatten (s : seq (word A)) :
  f (flatten s) = flatten [seq f l | l <- s].
Proof. by rewrite flatten_prodE mmorph_prod [RHS]flatten_map_prodE. Qed.

End Morphism.

(* TODO : change the name *)
Definition correctrelat A (R : relat A) (P : pred A) :=
  all (fun p => all P p.1 && all P p.2) R.

Structure pres (A : choiceType) := Pres {
  pgen : seq A;
  prelat : relat A;
  uniq_pgen : uniq pgen;
  wf_relat : correctrelat prelat (mem pgen)
}.


(* assia : introduce a notation for _ = _ %[mod R] which hides the prelat *)

Section Presentation.

Variable (A : choiceType).
Implicit Types (u v w x y : word A).


(* TODO: improve this name *)
Definition words_of (R : pres A) := [pred w | all (mem (pgen R)) w].

Lemma words_of_prelat (R : pres A) r :
  r \in prelat R -> (r.1 \in words_of R) && (r.2 \in words_of R).
Proof. by move=> Rr; move/allP: (wf_relat R) => /(_ r Rr). Qed.

Lemma words_of_cat R u v :
  u ++ v \in words_of R = (u \in words_of R) && (v \in words_of R).
Proof. by rewrite /words_of /= !inE all_cat. Qed.

Lemma rewrites_word_of (R : pres A) u v :
  u \in words_of R -> v \in rewrites (prelat R) u -> v \in words_of R.
Proof.
move=> hu /rewritesP[] pre suf [r1 r2] eu -> hr.
move: hu; rewrite {}eu !words_of_cat /=.
by case/and3P=> -> _ ->; case/andP: (words_of_prelat hr)=> _ ->.
Qed.

Lemma rewrites_to_word_of (R : pres A) u v :
  u \in words_of R -> rewrites_to (prelat R) u v -> v \in words_of R.
Proof.
move=> uinR [pathuv Huv {v}->].
elim: pathuv u uinR Huv => [| p0 pth IHpth] //= u uinR.
by case/andP => /(rewrites_word_of uinR) p0inR /(IHpth _ p0inR).
Qed.


Lemma wf_undirected_pres (R : pres A) :
  correctrelat (undirected (prelat R)) (mem (pgen R)).
Proof.
apply/allP=> /= [[x1 x2]] /=.
have /allP := wf_relat R => /= hwf.
rewrite mem_undirected => /orP [] hx //=; last rewrite andbC.
all: by rewrite (hwf _ hx).
Qed.

Definition undirected_pres (R : pres A) : pres A :=
  Pres (uniq_pgen R) (wf_undirected_pres R).

End Presentation.


Definition rewmorphism A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) :=
  forall u v : word A, u \in words_of R -> v \in words_of R ->
  v \in rewrites (prelat R) u -> rewrites_to (prelat S) (f u) (f v).

(* assia : or may be axiom on generators and this as a theory lemma *)
Definition rewmorphism_in A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) :=
  forall u : word A, u \in words_of R -> (f u \in words_of S).

(* assia: where is this needed? *)
Definition rewmorphism_to A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) :=
  forall u v : word A, u \in words_of R -> v \in words_of R ->
     rewrites_to (prelat R) u v -> rewrites_to (prelat S) (f u) (f v).

Lemma rewmorphism_toP A B (R : pres A) (S : pres B)
  (f : seq A -> seq B) : rewmorphism R S f <-> rewmorphism_to R S f.
Proof.
split; last first.
- by move=> h u v wu wv hrw; apply: h=> //; apply: rewrites_to1.
- move=> h u v wu wv [p hp ->].
  elim: p u hp wu => [u _ _ |p0 pth IHpth u] /=; first exact: rewrites_to_refl.
  move=> /andP[p0_u {}/IHpth] ihp hu.
  have /ihp : p0 \in words_of R by apply: (rewrites_word_of hu p0_u).
  apply: rewrites_to_trans; apply: h => //.
  exact: (rewrites_word_of hu).
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
  v \in rewrites (prelat R) u -> rewrites_to (prelat S) (f u) (f v).
Proof. exact: rewmorphism_subproof. Qed.

Lemma rewmorph_inP u :
  u \in words_of R -> f u \in words_of S.
Proof. exact: rewmorphism_in_subproof. Qed.

Lemma rewmorphP u v :
  u \in words_of R -> v \in words_of R ->
  rewrites_to (prelat R) u v -> rewrites_to (prelat S) (f u) (f v).
Proof.
move=> hu hv [p Hp ->].
elim: p u Hp hu => [u _ _ |p0 pth IHpth u] /=; first exact: rewrites_to_refl.
move=> /andP[p0_u {}/IHpth] ihp hu.
have hp0 : p0 \in words_of R by apply: (rewrites_word_of hu p0_u).
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

HB.instance Definition _  :=
  isRewMorphism.Build A B R S f rewmorphism_toP rewmorphism_to_inP.
HB.end.

(* assia: builds the instance of morphism on symmetrized relations,
from a morphism on the   undirected relations. *)
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

HB.instance Definition _  :=
  isPresMorphism.Build A B R S f
  rewmorphism_to_undirected rewmorphism_in_undirected.
HB.end.


Section IdMor.
Variables (A : choiceType) (R R' : pres A).
Hypothesis eqR : forall u v, u \in words_of R -> v \in words_of R ->
  rewrites_to (prelat R) u v -> rewrites_to (prelat R') u v.
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
      a \in words_of R -> inv (mor a) = a %[mod (prelat R)];
    caninv : forall b : word B,
      b \in words_of S -> mor (inv b) = b %[mod (prelat S)]
  }.

Definition isopres_sym A B (R : pres A) (S : pres B)
  (eq : isopres R S) := IsoPres (caninv eq) (canmor eq).
Lemma isopres_symK  A B (R : pres A) (S : pres B) eq :
  ((@isopres_sym B A S R) \o (@isopres_sym A B R S)) eq = eq.
Proof. by rewrite /isopres_sym; move: eq => [m i cm ci]/=. Qed.


Lemma isopresP A B (R : pres A) (S : pres B) (eq : isopres R S) u v :
  u \in words_of R -> v \in words_of R ->
  eq u = eq v %[mod (prelat S)] <-> u = v %[mod (prelat R)].
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
  inv eq u = inv eq v %[mod (prelat R)] <-> u = v %[mod (prelat S)].
Proof. move=> hu hv; exact: (isopresP (isopres_sym eq)). Qed.


Section IsopresTheory.

Variables (A B C : choiceType) (R : pres A) (S : pres B) (T : pres C).

Definition isopres_refl :=
  let uR := undirected_pres R in IsoPres (mor := idmor uR) (inv := idmor uR)
      (fun a _ => rewrites_to_refl (prelat uR) a)
      (fun a _ => rewrites_to_refl (prelat uR) a).

Variable (eqRS : isopres R S) (eqST : isopres S T).
Fact canmor_trans a :
  a \in words_of R ->
        (inv eqRS \o inv eqST) ((eqST \o eqRS) a) = a %[mod (prelat R)].
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
        (eqST \o eqRS) ((inv eqRS \o inv eqST) c) = c %[mod (prelat T)].
Proof.
move=> wc.
have wiSTc : inv eqST c \in words_of S by apply: rewmorph_inP.
have := caninv eqRS wiSTc; rewrite -(isopres_invP eqST) //=.
- by move/(equiv_trans _); apply; apply canmor; do 3! apply: rewmorph_inP.
- by do 4! apply: rewmorph_inP.
Qed.
Definition isopres_trans := IsoPres canmor_trans invmor_trans.

Lemma isopres_transE : isopres_trans =1 eqST \o eqRS.
Proof. by []. Qed.
Lemma isopres_trans_invE : inv isopres_trans =1 (inv eqRS \o inv eqST).
Proof. by []. Qed.

End IsopresTheory.


Section PresEqEquivTheory.

Variables (A : choiceType) (R R' : pres A).
Hypothesis eqR : forall u v,
    [/\ u \in words_of R, v \in words_of R & u = v %[mod prelat R]] <->
    [/\ u \in words_of R', v \in words_of R' & u = v %[mod prelat R']].

Let mor_subproof u v : u \in words_of R -> v \in words_of R ->
  u = v %[mod prelat R] -> u = v %[mod prelat R'].
Proof.
move=> wu wv Ruv.
have : [/\ u \in words_of R, v \in words_of R & u = v %[mod prelat R]] by split.
by case/eqR.
Qed.

Lemma mor_in_subproof u :
  u \in words_of (undirected_pres R) -> u \in words_of (undirected_pres R').
Proof.
move=> wu.
suff : [/\ u \in words_of R, u \in words_of R & u = u %[mod prelat R]].
  by move/eqR; case.
split=> //; exact: rewrites_to_refl.
Qed.

Let inv_subproof u v :  u \in words_of R' -> v \in words_of R' ->
 u = v %[mod prelat R'] -> u = v %[mod prelat R].
Proof.
move=> wu wv R'uv.
have : [/\ u \in words_of R', v \in words_of R' & u = v %[mod prelat R']] by split.
by case/eqR.
Qed.

Lemma inv_in_subproof u :
  u \in words_of (undirected_pres R') -> u \in words_of (undirected_pres R).
Proof.
move=> wu.
suff : [/\ u \in words_of R', u \in words_of R' & u = u %[mod prelat R']].
  by move/eqR; case.
split=> //; exact: rewrites_to_refl.
Qed.

Let morRR' : {presmorph R -> R'}.
apply: idmorRR'.
- exact: mor_subproof.
- exact: mor_in_subproof.
Defined.

Let morR'R : {presmorph R' -> R}.
apply: idmorRR'.
- exact: inv_subproof.
- exact: inv_in_subproof.
Defined.

Fact canmor_eq a : morR'R (morRR' a) = a %[mod prelat R].
Proof. exact: equiv_refl. Qed.
Fact caninv_eq a : morRR' (morR'R a) = a %[mod prelat R'].
Proof. exact: equiv_refl. Qed.
Definition isopres_eq : isopres R R' :=
  IsoPres (fun _ _ => canmor_eq _) (fun _ _ => caninv_eq _).

End PresEqEquivTheory.


Lemma pres_irrelevance A (R1 R2 : pres A)  :
  pgen R1 = pgen R2 -> prelat R1 = prelat R2 -> isopres R1 R2.
Proof.
move=> geneq releq; apply: isopres_eq => u v.
by rewrite /words_of geneq releq.
Qed.

Lemma pres_irrelevance_perm_eq A (R1 R2 : pres A)  :
  perm_eq (pgen R1) (pgen R2) -> perm_eq (prelat R1) (prelat R2) -> isopres R1 R2.
Proof.
move=> /perm_mem geneq /perm_mem releq; apply: isopres_eq => u v.
have eq_word_of : words_of R1 =i words_of R2.
  by move=> w; apply: eq_all.
rewrite !eq_word_of.
case: (u \in _); rewrite ?orbT //; last by split => [][].
case: (v \in _); rewrite ?orbT //; last by split => [][].
suff /eq_equiv_undirected /(_ u v) Heq :
    undirected (prelat R1) =i undirected (prelat R2).
  by split => [][_ _ /Heq].
by move=> [x y]; rewrite !mem_undirected !releq.
Qed.


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
move=> [p /[swap] {y}->]; elim: p x => [|p0 p IHp] x /=.
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

Lemma wf_ext_pres :
  correctrelat ((u, v) :: (prelat R)) (mem (pgen R)).
Proof.
apply/allP=> /= [[x1 x2]] /=.
have /allP := wf_relat R => /= hwf.
rewrite inE; case/orP; last exact: hwf.
by case/eqP=> -> ->; rewrite pgu.
Qed.

Definition ext_pres : pres A :=  Pres (uniq_pgen R) wf_ext_pres.

Lemma wf_rcons_ext_pres :
  correctrelat (rcons (prelat R) (u, v)) (mem (pgen R)).
Proof.
apply/allP=> /= [[x1 x2]] /=.
have /allP := wf_relat R => /= hwf.
rewrite mem_rcons; case/orP; last exact: hwf.
by case/eqP=> -> ->; rewrite pgu.
Qed.

Definition rcons_ext_pres : pres A :=  Pres (uniq_pgen R) wf_rcons_ext_pres.

Hypothesis (Ruv : u = v %[mod prelat R]).

Lemma equiv_cons_rule_mod x y :
  x = y %[mod prelat R] <-> x = y %[mod (u, v) :: prelat R].
Proof.
rewrite (rewrites_to_cons_rule Ruv).
have rvu : rewrites_to ((u, v) :: undirected (prelat R)) v u.
  by rewrite -(rewrites_to_cons_rule Ruv); apply: equiv_sym.
rewrite (rewrites_to_cons_rule rvu) {rvu}.
apply: eq_rewrites_to => {x y}[[/= x y]].
rewrite !(mem_undirected, inE) -[(y, x) == _](inj_eq swap_inj) /swap /=.
by case: eqP; rewrite !(orbT, orbA).
Qed.

Fact equiv_cons_rule x y :
  [/\ x \in words_of R, y \in words_of R & x = y %[mod prelat R]] <->
  [/\ x \in words_of R, y \in words_of R & x = y %[mod (u, v) :: prelat R]].
Proof.
by split; case=> wx wy Rxy; split=> //; apply/equiv_cons_rule_mod.
Qed.
Definition isopres_cons_rule := @isopres_eq _ _ ext_pres equiv_cons_rule.

Lemma equiv_rcons_rule_mod x y :
  x = y %[mod prelat R] <-> x = y %[mod rcons (prelat R) (u, v)].
Proof.
rewrite (equiv_cons_rule_mod x y); apply eq_equiv => /= p.
by rewrite mem_rcons.
Qed.

Fact equiv_rcons_rule x y :
  [/\ x \in words_of R, y \in words_of R & x = y %[mod prelat R]] <->
  [/\ x \in words_of R, y \in words_of R & x = y %[mod rcons (prelat R) (u, v)]].
Proof.
by split; case=> wx wy Rxy; split=> //; apply/equiv_rcons_rule_mod.
Qed.
Definition isopres_rcons_rule := @isopres_eq _ _ rcons_ext_pres equiv_rcons_rule.

End Tietze1.

Lemma Tietze_add_rel  A (R1 R2 : pres A) (u v : word A) :
  u \in words_of R1 -> v \in words_of R1 ->
  pgen R1 = pgen R2 -> prelat R2 = rcons (prelat R1) (u, v) ->
  u = v %[mod prelat R1] -> isopres R1 R2.
Proof.
move=> allu allv eqgen eqrelat newrelat.
apply: (isopres_trans (isopres_rcons_rule allu allv newrelat)).
exact: pres_irrelevance.
Qed.


Section Tietze2.

Context (A : choiceType) (R : pres A) (gen : A) (w : word A).

Hypothesis wcorr : w \in words_of R.
Hypothesis gen_nP : gen \notin (pgen R).

Let wall : all (mem (pgen R)) w.
Proof. exact: wcorr. Qed.

Implicit Types (u v x y : word A).

Definition Tietze2_gen := rcons (pgen R) gen.
Definition Tietze2_relat := rcons (prelat R) ([:: gen], w).

Lemma subset_Tietze2 : {subset prelat R <= Tietze2_relat}.
Proof. by move=> /= p; rewrite mem_rcons inE orbC => ->. Qed.

Fact Tietze2_gen_uniq : uniq Tietze2_gen.
Proof.
rewrite rcons_uniq gen_nP; exact: uniq_pgen.
Qed.
Fact Tietze2_wf_relat : correctrelat Tietze2_relat (mem Tietze2_gen).
Proof.
have sub_relat : subpred (mem (prelat R)) (mem Tietze2_relat).
  by move=> x Rx; rewrite /= mem_rcons mem_behead.
have sub_gen : subpred (mem (pgen R)) (mem Tietze2_gen).
  by move=> x Rx; rewrite /= mem_rcons mem_behead.
apply/allP=> /= [] r.
rewrite mem_rcons inE; case/orP=> [/eqP | Rr].
- case:r  => r1 r2 [] -> ->; rewrite /= mem_rcons mem_head /=.
  exact: (sub_all sub_gen).
- have /allP/(_ _ Rr) /andP[rr1 Rr2] := wf_relat R.
  by rewrite !(sub_all sub_gen).
Qed.
Definition T2_pres : pres A := Pres Tietze2_gen_uniq Tietze2_wf_relat.


Lemma sub_2 u v : u = v %[mod prelat R] -> u = v %[mod Tietze2_relat].
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

Lemma T2inv_rewrites_to u : rewrites_to Tietze2_relat u (T2inv u).
Proof.
rewrite /T2inv; elim: u => [| u0 u /(rewrites_to_cat _) IHu] /=.
  by rewrite big_nil; exists [::].
rewrite big_cons -mul_catE -cat1s; apply: IHu.
case: eqP => [-> |_] /= ; last exact: rewrites_to_refl.
apply: rewrites_to1; rewrite /Tietze2_relat rewrites_rcons mem_cat.
by rewrite {1}/rewrites /= eq_refl /= cats0 inE eq_refl.
Qed.
Lemma T2invE u : u = T2inv u %[mod (prelat T2_pres)].
Proof. exact: (rewrites_to_equiv (T2inv_rewrites_to u)). Qed.
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

Lemma T2morK u : all (mem (pgen R)) u -> T2inv (T2mor u) = u %[mod prelat R].
Proof. by move/allP_T2inv => ->; apply: equiv_refl. Qed.
Lemma T2invK v : T2mor (T2inv v) = v %[mod prelat T2_pres].
Proof. exact: (equiv_trans (equiv_refl _ _) (equiv_sym (T2invE v))). Qed.

Fact T2invK_in v :
  v \in words_of T2_pres -> T2mor (T2inv v) = v %[mod prelat T2_pres].
Proof. by move => _; exact: T2invK. Qed.
Definition isopres_Tietze2 : isopres R T2_pres :=
  IsoPres T2morK T2invK_in.

End Tietze2.

Lemma Tietze_add_gen_swap A (R1 R2 : pres A) (g : A) (w : word A) :
  pgen R2 = rcons (pgen R1) g -> prelat R2 = rcons (prelat R1) ([:: g], w) ->
  w \in words_of R1 -> g \notin (pgen R1) -> isopres R1 R2.
Proof.
move=> eqgen eqrelat allw gok.
apply: (isopres_trans (isopres_Tietze2 allw gok)).
exact: pres_irrelevance.
Qed.
Lemma Tietze_add_gen A (R1 R2 : pres A) (g : A) (w : word A) :
  pgen R2 = rcons (pgen R1) g -> prelat R2 = rcons (prelat R1) (w, [:: g]) ->
  w \in words_of R1 -> g \notin (pgen R1) -> isopres R1 R2.
Proof.
move=> eqgen eqrelat allw cok.
apply: (isopres_trans (isopres_Tietze2 allw cok)).
apply: isopres_eq => u v.
rewrite /words_of /= /Tietze2_gen {}eqgen.
suff /eq_equiv_undirected /(_ u v) Heq :
    undirected (Tietze2_relat R1 g w) =i undirected (prelat R2).
  by split => [][-> -> /Heq].
move=> [x y]; rewrite !mem_undirected {}eqrelat /Tietze2_relat.
rewrite !mem_rcons !inE.
case: (_ \in prelat R1); rewrite ?orbT //.
case: (_ \in prelat R1); rewrite ?orbT //= !orbF orbC.
by rewrite !xpair_eqE ![_ && (y == _)]andbC.
Qed.


Lemma wf_impl (T : Type) (R : T -> T -> Prop) (S : T -> T -> Prop) :
  (forall x y : T, R x y -> S x y) -> well_founded S -> well_founded R.
Proof.
move=> RS WfS.
suff impl x: Acc S x -> Acc R x by move=> y; apply/impl/WfS.
move: x; apply: (well_founded_induction_type WfS) => x HAcc ASx.
apply: Acc_intro => y Ryx; apply: HAcc; first exact: RS.
by apply: (Acc_inv ASx); exact: RS.
Qed.

Lemma wfP (T : Type) (R : T -> T -> Prop) (S : rel T) :
  (forall x y : T, reflect (R x y) (S x y)) ->
  (well_founded R <-> well_founded S).
Proof. by move => refl; split; apply: wf_impl => x y /refl. Qed.


Section RewritingTheory.

Variable T : choiceType.
Implicit Types (R : relat T) (u v w x y : word T).

Variable C : rel (word T).
Hypothesis Cstable : forall u v1 v2 w,
    C v1 v2 -> C (u ++ v1 ++ w) (u ++ v2 ++ w).

Definition decreasing R := all (fun r => C r.2 r.1) R.
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
Proof. by move=> [w uw vw]; exists w. Qed.
Lemma joinable_stable R u v1 v2 w :
  joinable R v1 v2 -> joinable R (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof. by move=> [r r1 r2]; exists (u ++ r ++ w); apply: rewrites_to_stable. Qed.


Section Confluence.

Variable (R : relat T).
Hypothesis Rconfl : confluent R.

Lemma normalE u v : normal R u -> rewrites_to R u v -> u = v.
Proof.
move/eqP => noru [[_ {v}-> // | w pth /= /andP[/[swap] _ ]]].
by rewrite noru.
Qed.
Lemma confluentE u v1 v2 : normalf R u v1 -> normalf R u v2 -> v1 = v2.
Proof.
move=> [/normalE norv1 /Rconfl HC ] [/normalE norv2 {}/HC].
by move=> [w /norv1-> /norv2->].
Qed.
Lemma confl_rewritesE u1 v1 u2 v2 :
  normalf R u1 v1 -> normalf R u2 v2 -> u2 \in rewrites R u1 -> v1 = v2.
Proof.
move/confluentE => eq [norv2 u2v2] /rewrites_to1/rewrites_to_trans/(_ u2v2) u1v2.
exact: eq.
Qed.
Lemma normalf_rewrite0 u : rewrites R u == [::] -> normalf R u u.
Proof. by move=> H; split; last exact: rewrites_to_refl. Qed.
Lemma normalf_rewrites u v w :
  normalf R u w -> v \in rewrites (undirected R) u -> normalf R v w.
Proof.
move=> [norw u_w]; rewrite rewrites_undirected orbC.
move=> /orP[/rewrites_to1 v_u | /rewrites_to1 u_v]; split; try exact: norw.
  exact: (rewrites_to_trans _ u_w).
by have [w0 /(normalE norw) <-{w0}] := Rconfl u_w u_v.
Qed.
Lemma normalf_equivE u w :
  normalf R u w -> forall v, normalf R v w <-> u = v %[mod R].
Proof.
move=> noruw v; split.
  move=> [_ /rewrites_to_equiv/equiv_sym/(equiv_trans _)]; apply.
  by move: noruw => [_ /rewrites_to_equiv].
move=> [pth Hpth {v}->].
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

Fixpoint norfuel R fuel u :=
  if fuel is fuel'.+1 then
    if rewrites1 R u is Some v then norfuel R fuel' v else (u, true)
  else (u, false).

Lemma rewrites_to_norfuel R fuel u : rewrites_to R u (norfuel R fuel u).1.
Proof.
elim: fuel u => [|fuel IHfuel] u /=; first exact: rewrites_to_refl.
case H : rewrites1 => [a|]; last exact: rewrites_to_refl.
by move/rewrites1P/rewrites_to1/rewrites_to_trans : H; apply.
Qed.
Lemma norfuelT R fuel u :
  (norfuel R fuel u).2 -> normalf R u (norfuel R fuel u).1.
Proof.
have:= rewrites_to_norfuel R fuel u.
case Hnor : norfuel => [v b] /= rew Hb; rewrite {}Hb in Hnor.
split => // {rew}.
move: Hnor; elim: fuel u => //= fuel IHfuel u.
case H : rewrites1 => [w |]; first exact: IHfuel.
by rewrite /normal => [[<-]] {IHfuel}; move/eqP: H; rewrite -rewrites0P.
Qed.
Lemma norfuelF R fuel u :
  ~~ (norfuel R fuel u).2 ->
  exists pth, [/\ path (fun u v => v \in rewrites R u) u pth,
      (norfuel R fuel u).1 = last u pth & size pth = fuel].
Proof.
elim: fuel u => [// | fuel IHfuel] /= u; first by move=> _; exists [::].
case Hrew : rewrites1 => [a | //] {}/IHfuel[pth [Hpth Hlast szpth]].
exists (a :: pth); rewrite /= {}szpth; split => //.
rewrite Hpth andbT.
move: Hrew; rewrite rewrite1E; case: rewrites => [// | b v] /= [->].
by rewrite inE eqxx.
Qed.

Lemma equivalence_fuelP R fuel :
  confluent R -> forall u v,
      let (un, uok) := norfuel R fuel u in
      let (vn, vok) := norfuel R fuel v in
      uok && vok -> reflect (u = v %[mod R]) (un == vn).
Proof.
move=> confl u v.
case: norfuel (@norfuelT R fuel u) => /= un [/(_ is_true_true) uok /=| _];
  last by case: norfuel.
case: norfuel (@norfuelT R fuel v) => /= vn [/(_ is_true_true) vok /= _|//].
exact: normalf_equivP.
Qed.

Lemma terminatingP R : terminating R ->
                       well_founded (fun v u => exists2 w : word T,
                                         w \in rewrites R u & rewrites_to R w v).
Proof.
move=> wf; elim/(well_founded_ind wf) => u IHu.
apply: Acc_intro => v [/= w {}/IHu Accw /rewrites_toP[<- // |]].
move=> [/= w1 w_w1 w1_v].
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
Inductive spair R u v : Prop :=
  SPair: forall (pre mid suf: word T) (rpre rsuf : word T * word T),
      rpre \in R -> rsuf \in R
      -> mid != [::] -> rpre.1 = pre ++ mid -> rsuf.1 = mid ++ suf
      -> u = rpre.2 ++ suf -> v = pre ++ rsuf.2 -> spair R u v.
Inductive npair R u v : Prop :=
  NPair: forall (pre mid suf: word T) (rw rmid : word T * word T),
      rw \in R -> rmid \in R
      -> rw.1 = pre ++ mid ++ suf -> rmid.1 = mid
      -> u = rw.2 -> v = pre ++ rmid.2 ++ suf -> npair R u v.

Definition all_spairs_rule (r1 r2 s1 s2 : seq T) :=
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
  move=> [seqp /allpairsP/=[[[r1 r2] [s1 s2] /= [rinR sinR] {seqp}->]]].
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
move=> [pre mid suf [r1 r2] [s1 s2] rinR sinR /=] midn0 eqr1 eqs1 {u}->{v}->.
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
  move=> [seqp /allpairsP/=[[[r1 r2] [s1 s2] /= [rinR sinR] {seqp}->]]].
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
move=> [pre mid suf [r1 r2] [s1 s2] rinR sinR /= eqr1 eqs1 {u}->{v}->].
exists (all_npairs_rule r1 r2 s1 s2).
  by apply/allpairsP => /=; exists (r1, r2, (s1, s2)).
apply/mapP; exists (size pre).
  rewrite mem_filter mem_iota add0n /= ltnS.
  rewrite eqr1 eqs1 drop_size_cat // take_size_cat // eqxx /=.
  by rewrite !size_cat [size mid + _]addnC addnA addnK leq_addr.
by rewrite eqr1 eqs1 take_size_cat // -size_cat !catA drop_size_cat.
Qed.


Lemma cat2E u v x y :
  size u <= size x -> u ++ v = x ++ y ->
  exists2 mid, v = mid ++ y & x = u ++ mid.
Proof.
move=> ltsize eq.
exists (take (size x - size u) v).
  have := congr1 (drop (size u)) eq.
  rewrite drop_size_cat // => ->; rewrite drop_cat; first last.
  move: ltsize; rewrite leq_eqVlt => /orP[/eqP -> | ->].
    by rewrite ltnn subnn take0 drop0.
  by rewrite take_size_cat // size_drop.
have := congr1 (take (size x)) eq.
rewrite [X in _ = X -> _]take_size_cat // => {1}<-.
by rewrite take_cat ltnNge ltsize /=.
Qed.

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

Variant check_convergence_result :=
  | Ok : check_convergence_result
  | NotDecreasing : check_convergence_result
  | HaveNpair : relat T -> check_convergence_result
  | HaveSpair : (word T * word T) -> check_convergence_result.

Definition is_Ok r := if r is Ok then true else false.

Definition check_convergence fuel R : check_convergence_result :=
  if ~~ (decreasing R) then NotDecreasing
  else if has (fun p => p.1 != p.2) (all_npairs R) then HaveNpair (all_npairs R)
  else let spairs := filter (fun p => p.1 != p.2) (all_spairs R) in
      (* if normalisation fails by out of fuel but results agree *)
      (* we do have confluence                                   *)
  let pos := find (fun p => norfuel R fuel p.1 != norfuel R fuel p.2) spairs in
  if pos < size spairs then HaveSpair (nth ([::], [::]) spairs pos)
  else Ok.

Definition check_convergence_if fuel R : bool :=
  if ~~ (decreasing R) then false
  else if has (fun p => p.1 != p.2) (all_npairs R) then false
  else let spairs := filter (fun p => p.1 != p.2) (all_spairs R) in
      (* if normalisation fails by out of fuel but results agree *)
      (* we do have confluence                                   *)
  all (fun p => norfuel R fuel p.1 == norfuel R fuel p.2) spairs.

Definition check_convergence_and fuel R : bool :=
  [&& (decreasing R),
    all (fun p => p.1 == p.2) (all_npairs R) &
    all (fun p => norfuel R fuel p.1 == norfuel R fuel p.2)
      (filter (fun p => p.1 != p.2) (all_spairs R))].

Lemma check_convergenceE fuel R :
  is_Ok (check_convergence fuel R) = check_convergence_and fuel R.
Proof.
rewrite /check_convergence /check_convergence_and.
case: (decreasing R) => [/=|//].
rewrite has_predC; case: (all _ _) => [/=|//].
move: (filter _ _) => S; rewrite -[all _ _]negbK -has_predC has_find.
by case: ltnP.
Qed.


Section WellFounded.

Hypothesis C_wf : well_founded C.

Lemma decreasing_wf R : decreasing R -> terminating R.
Proof.
move=> /allP /= decr.
apply: (wf_impl _ C_wf) => x y /rewritesP[pre suf r {x}->{y}-> rinR].
by apply: Cstable; apply: decr.
Qed.

Lemma check_convergence_andP fuel R :
  check_convergence_and fuel R -> convergent R.
Proof.
rewrite /check_convergence_and => /=.
case: (boolP (decreasing R)) => [/= dec | //].
case: allP => [/= nonpair | //].
have {nonpair}/spair_confluence loc_confl : forall u v, npair R u v -> u = v.
  by move=> u v /all_npairsP /nonpair /= /eqP ->.
move/allP => /= confl; apply: diamond; first exact: (decreasing_wf dec).
apply: loc_confl => u v Suv.
case: (altP (u =P v)) => [-> | nequv]; first by exists v; apply: rewrites_to_refl.
have /confl/eqP/=eqnor : (u, v) \in filter (fun p => p.1 != p.2) (all_spairs R).
  by rewrite mem_filter /= {}nequv /=; apply/all_spairsP.
by exists (norfuel R fuel u).1 => [|/[!eqnor]]; exact: rewrites_to_norfuel.
Qed.

Lemma check_convergenceP fuel R :
  is_Ok (check_convergence fuel R) -> convergent R.
Proof. by rewrite check_convergenceE; apply: check_convergence_andP. Qed.

End WellFounded.

End RewritingTheory.


Import Order.TTheory.
Import Order.LexiSyntax.

Fact sizelexidisplay : Order.disp_t. Proof. exact: Order.Disp tt tt. Qed.

Section SizeLexi.
Variable (d : Order.disp_t) (T : orderType d).
Implicit Types (u v w x y : seq T).


Definition sizelexi u v :=
  (size u < size v) || (size u == size v) && (u <= v :> seqlexi _)%O.

Lemma sizelexi_le u v : sizelexi u v -> size u <= size v.
Proof. by move=> /orP[/ltnW | /andP[/eqP -> _]]. Qed.

Fact sizelexi_refl : reflexive sizelexi.
Proof. by move=> u; rewrite /sizelexi eqxx lexx /= orbT. Qed.
Fact sizelexi_anti : antisymmetric sizelexi.
Proof.
move=> u v /andP[/orP[ltsz | /andP[/eqP eqsz leuv]]].
  move/orP => []; first by rewrite (leq_gtF (ltnW ltsz)).
  by rewrite (gtn_eqF ltsz).
move=> /orP[| /andP[_ levu]]; first by rewrite eqsz ltnn.
by apply/eqP; rewrite (eq_le (u : seqlexi _)) leuv levu.
Qed.
Fact sizelexi_trans : transitive sizelexi.
Proof.
move=> v u w /orP[ltsz /sizelexi_le | /andP[/eqP eqszuv leuv]].
  by move=> /(leq_trans ltsz) {}ltsz; apply/orP; left.
move=> /orP[ltsz | /andP[/eqP eqszvw levw]].
  by apply/orP; left; rewrite eqszuv.
apply/orP; right; rewrite eqszuv eqszvw eqxx /=.
exact: (le_trans leuv levw).
Qed.
HB.instance Definition _  := Order.Le_isPOrder.Build sizelexidisplay
                               (seq T) sizelexi_refl sizelexi_anti sizelexi_trans.
Fact sizelexi_total : total sizelexi.
Proof.
rewrite /sizelexi => u v; case: (ltngtP (size u) (size v)) => cmpsz //=.
by case: (leP (u : seqlexi _) v) => //= /ltW.
Qed.
HB.instance Definition _  := Order.POrder_isTotal.Build sizelexidisplay
                               (seq T) sizelexi_total.
Fact nil_bot u : ([::] <= u)%O.
Proof.
rewrite /Order.le /= /sizelexi /= eq_sym.
by case: (boolP (size u == 0)) => [/nilP -> |]; last rewrite -lt0n => ->.
Qed.
HB.instance Definition _  := Order.hasBottom.Build sizelexidisplay
                               (seq T) nil_bot.

Lemma le_sizelexiE u v :
  (u <= v)%O =
    (size u < size v) || (size u == size v) && (u <= v :> seqlexi _)%O.
Proof. by []. Qed.

Lemma lt_sizelexiE u v :
  (u < v)%O =
    (size u < size v) || (size u == size v) && (u < v :> seqlexi _)%O.
Proof.
rewrite !lt_neqAle; case: eqP => [-> | _] //=.
by rewrite andbF orbF ltnn.
Qed.

Lemma size_le_sizelexi u v : (u <= v)%O -> size u <= size v.
Proof. by rewrite le_sizelexiE => /orP[/ltnW|/andP[/eqP-> _]]. Qed.

Lemma lt_sizelexi_stable u v1 v2 w :
  (v1 < v2 -> (u ++ v1 ++ w) < (u ++ v2 ++ w))%O.
Proof.
rewrite !lt_sizelexiE => /orP[ltsz | /andP[/eqP eqsz ltlex12]].
  by rewrite !size_cat ltn_add2l ltn_add2r ltsz.
rewrite !size_cat eqsz ltnn eqxx /=.
elim: u => [/=| a u IHu]; last by rewrite /= ltxi_cons lexx.
elim: v1 v2 eqsz ltlex12 => [|h1 v1 IHv1] [|h2 v2]//= [{}/IHv1 rec].
rewrite !ltxi_cons => /andP[->]/= /implyP H.
by apply/implyP => /H/rec.
Qed.

End SizeLexi.


Section SizelexiWF.
Variables (disp : Order.disp_t) (T : orderType disp).
Implicit Types (u v w : seq T).

Hypothesis Twf : well_founded (@Order.lt _ T).

Lemma sizelexi_wf : well_founded (@Order.lt _ (seq T)).
Proof.
pose ltb b u v := ((size v <= b) && (u < v)%O).
suff bwf bnd : well_founded (ltb bnd).
  move=> u; have [n] := ubnPleq (size u).
  elim/(well_founded_induction (bwf n)): u => u IHu szu.
  apply: Acc_intro => y ltyu; apply: IHu; first by rewrite /ltb szu ltyu.
  exact: (leq_trans (size_le_sizelexi (ltW ltyu)) szu).
elim: bnd => [| bnd IHbnd].
  move=> u; apply: Acc_intro => y /andP[/[!leqn0]/nilP ->].
  by rewrite ltNge nil_bot.
have rec u : size u <= bnd -> Acc (ltb bnd.+1) u.
  elim/(well_founded_induction IHbnd) : u => u IHu szu.
  apply: Acc_intro => v /andP[_ ltvu]; apply IHu; first by rewrite /ltb szu ltvu.
  exact: (leq_trans (size_le_sizelexi (ltW ltvu)) szu).
suff rec' u : size u <= bnd.+1 -> Acc (ltb bnd.+1) u.
  move=> u; apply: Acc_intro => y /andP[szu /ltW/size_le_sizelexi].
  by move/leq_trans/(_  szu); apply: rec'.
rewrite leq_eqVlt => /orP[/eqP szu|]; last exact: rec.
case: u szu => [//| u0 u] /= [szu].
elim/(well_founded_induction Twf): u0 u szu => [u0 IHm].
elim/(well_founded_induction IHbnd) => u IHu szu.
apply: Acc_intro => w /andP[/= _].
rewrite lt_sizelexiE /= ltnS => /orP[|]; first by rewrite szu; apply: rec.
case: w => [//| a v] /= /andP[/eqP[/[!szu] szv]].
rewrite Order.SeqLexiOrder.ltxi_cons le_eqVlt => /andP[/orP[/eqP{a}-> | ltam _]].
  rewrite lexx /= => ltlvu; apply IHu; last exact: szv.
  by rewrite /ltb szu leqnn /= lt_sizelexiE orbC szu szv eqxx ltlvu.
exact: (IHm a ltam).
Qed.

End SizelexiWF.

Lemma wf_ltnat : well_founded (@Order.lt _ nat).
Proof. by elim/ltn_ind => n IHn; apply: Acc_intro => m /IHn. Qed.
Lemma sizelexi_nat_wf : well_founded (@Order.lt _ (seq nat)).
Proof. exact: sizelexi_wf wf_ltnat. Qed.

Definition check_convergence_natP fuel R :
  is_Ok (check_convergence <%O fuel R) -> convergent R :=
  check_convergenceP (@lt_sizelexi_stable _ nat) sizelexi_nat_wf
    (fuel := fuel) (R := R).
(*
Definition present_final :=
  [:: (*  c < e < d < a < b. *)
      (*  0 < 1 < 2 < 3 < 4. *)
     ([:: 3; 4], [:: 0]);           (* ab → c *)
     ([:: 4; 3], [:: 2]);           (* ba → d *)
     ([:: 3; 0], [:: 1]);           (* ac → e *)
     ([:: 3; 2], [:: 0; 3]);        (* ad → ca *)
     ([:: 4; 0], [:: 2; 4]);        (* bc → db *)
     ([:: 4; 1], [:: 1; 0]);        (* be → ec *)
     ([:: 2; 3], [:: 1; 3]);        (* da → ea *)
     ([:: 2; 0], [:: 1; 0]);        (* dc → ec *)
     ([:: 2; 1], [:: 1; 1]);        (* de → ee *)
     ([:: 3; 1; 3], [:: 0; 3; 3]);  (* aea → caa *)
     ([:: 3; 1; 0], [:: 0; 1]);     (* aec → ce *)
     ([:: 3; 1; 1], [:: 0; 3; 1])   (* aee → cae*)
   ].

Theorem final_ok : convergent present_final.
Proof. exact: (check_convergence_natP (fuel := 5)). Qed.



Goal ([:: 1; 2; 2] < [:: 2; 2; 1])%O. by []. Qed.
Goal ~~ ([:: 2; 2] < [:: 1])%O. by []. Qed.
Goal ~~ ([:: 1; 2; 2] < [:: 2; 2])%O. by []. Qed.

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]); ([:: 1], [:: 0])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]);
                             ([:: 1], [:: 0]);
                             ([:: 2; 1; 2], [::])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Definition present_page_3_1 :=
  [::
   ([:: 2; 1; 1], [:: 1; 1; 2; 1]);
   ([:: 1; 2], [:: 3]);
   ([:: 2; 1], [:: 4]);
   ([:: 1; 3], [:: 5]);
   ([:: 1; 4], [:: 3; 1]);
   ([:: 2; 3], [:: 4; 2]);
   ([:: 2; 5], [:: 5; 3])].



Goal not (correctrelat present_page_3_1 (geq 3)). by []. Qed.
Goal not (correctrelat present_page_3_1 (geq 4)). by []. Qed.
Goal correctrelat present_page_3_1 (geq 5). by []. Qed.
Goal correctrelat present_page_3_1 (geq 6). by []. Qed.


Lemma step_3_1 : [:: 2; 5] = [:: 5; 3] %[mod present_page_3_1].
Proof.
by exists [::
        [:: 2; 1; 3];
        [:: 2; 1; 1; 2];
        [:: 1; 1; 2; 1; 2];
        [:: 1; 3; 1; 2];
        [:: 5; 1; 2];
        [:: 5; 3]].
Qed.

Eval vm_compute in norfuel present_page_3_1 10 [:: 2; 5].

Eval vm_compute in all_spairs present_page_3_1.
Eval vm_compute in all_npairs present_page_3_1. *)
