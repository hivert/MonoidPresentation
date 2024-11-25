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

Reserved Notation "x = y %[mod e ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %[mod  e ] ']'").


Section Swap.
Context {T : Type}.
Definition swap (p : T * T) := (p.2, p.1).
Lemma swapK : involutive swap. Proof. by move => [i j]. Qed.
Lemma swap_inj : injective swap. Proof. exact: (can_inj swapK). Qed.
End Swap.


Section Nil.
Variable T T' : eqType.
Lemma cat_nil (u v : seq T) : (u ++ v == [::]) = (u == [::]) && (v == [::]).
Proof. by case: u. Qed.
Lemma map_nil (u : seq T) (f : T -> T') : (map f u == [::]) = (u == [::]).
Proof. by case: u. Qed.
End Nil.


Section Defs.

Variable (Alph : choiceType).

Definition word := seq Alph.
Definition relat := seq (word * word).

Implicit Types (R : relat) (u v w x y : word) (p : word * word).

Section RelationsTerminology.

Variable RP : word -> word -> Prop.

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


Inductive rewrites_front_spec R u v : Prop :=
  RewritesFront : forall (suf : word) (rule : word * word),
      u = rule.1 ++ suf -> v = rule.2 ++ suf -> rule \in R
               -> rewrites_front_spec R u v.

Inductive rewrites_spec R u v : Prop :=
  Rewrites : forall (pre suf : word) (rule : word * word),
      u = pre ++ rule.1 ++ suf -> v = pre ++ rule.2 ++ suf -> rule \in R
               -> rewrites_spec R u v.

Lemma rewrite_front_spec_cons R u v r1 r2:
  rewrites_front_spec R u v -> rewrites_front_spec ((r1, r2) :: R) u v.
Proof.
move=> [suf [s1 s2] /= ->{u}->{v} sinR].
by exists suf (s1, s2) => //=; rewrite inE sinR orbT.
Qed.
Lemma rewrites_front_specP R u v pre :
  rewrites_front_spec R u v -> rewrites_spec R (pre ++ u) (pre ++ v).
Proof. by move=> [suf r ->{u}->{v} rinR]; exists pre suf r. Qed.
Lemma cons_rewrites_spec R a u v :
  rewrites_spec R u v -> rewrites_spec R (a :: u) (a :: v).
Proof. by move=> [pre suf r /= ->{u}->{v} rinR]; exists (a :: pre) suf r. Qed.


Fixpoint rewrites1_front R w :=
  if R is (r1, r2) :: R' then
    if prefix r1 w then Some (r2 ++ drop (size r1) w)
    else rewrites1_front R' w
  else None.

Fixpoint rewrites_front R w :=
  if R is (r1, r2) :: R' then
    if prefix r1 w then (r2 ++ drop (size r1) w) :: rewrites_front R' w
    else rewrites_front R' w
  else [::].

Lemma rewrites1_frontP R u v :
  rewrites1_front R u = Some v -> rewrites_front_spec R u v.
Proof.
elim: R => [// | [r1 r2] R IHR] /=.
case: prefixP => [[suf ->{IHR u}] [<-{v}] |_ /IHR/rewrite_front_spec_cons//].
exists (drop (size r1) (r1 ++ suf)) (r1, r2) => //=; last by rewrite inE eqxx.
by rewrite drop_size_cat.
Qed.
Lemma rewrites_frontP R u v :
  reflect (rewrites_front_spec R u v) (v \in rewrites_front R u).
Proof.
apply (iffP idP); elim: R => [|[r1 r2] R IHR] //=.
- case: prefixP => [| _ {}/IHR[suf [s1 s2]/= ->{u}->{v} sinR]]; first last.
    by exists suf (s1, s2) => //=; rewrite inE sinR orbT.
  move=> [suf equ]; subst u => /=.
  rewrite inE => /orP[/eqP->{v IHR} | {}/IHR].
    by exists suf (r1, r2); rewrite ?drop_size_cat // inE eqxx.
  exact: rewrite_front_spec_cons.
- by move=> [].
move=> [suf [s1 s2]/= equ eqv]; subst u v.
rewrite inE => /orP[/eqP[<-{r1}<-{r2}] | sinR].
  by rewrite prefix_prefix inE drop_size_cat // eqxx.
have {}/IHR : rewrites_front_spec R (s1 ++ suf) (s2 ++ suf) by exists suf (s1, s2).
by case: prefixP => _ //; rewrite inE orbC => ->.
Qed.
Lemma rewrites_front0P R u :
  (rewrites_front R u == [::]) = (rewrites1_front R u == None).
Proof.
elim: R => [// | [r1 r2] R IHR] /=.
by case: prefixP => [|_]; last exact: IHR.
Qed.


Section DefRewrites.

Variable (R : relat).

Fixpoint rewrites1 u :=
  if u is a :: u' then
    if rewrites1_front R u is Some u as res then res
    else option_map (cons a) (rewrites1 u')
  else rewrites1_front R [::].

Lemma rewrites1P u v : rewrites1 u = Some v -> rewrites_spec R u v.
Proof.
elim: u v => [| a u IHu] v /=.
  by move/rewrites1_frontP/(rewrites_front_specP [::]).
case Hfront: (rewrites1_front R (a :: u)) => [w|].
  by move=> [<-{v}]; move: Hfront => /rewrites1_frontP/(rewrites_front_specP [::]).
case Hrec: (rewrites1 u) => [w|]//= [<-{v}].
exact: (cons_rewrites_spec _ (IHu _ Hrec)).
Qed.

Fixpoint rewrites u :=
  if u is a :: u'
  then (rewrites_front R u) ++ [seq a :: v | v <- rewrites u']
  else rewrites_front R [::].

Lemma rewritesP u v : reflect (rewrites_spec R u v) (v \in rewrites u).
Proof.
apply (iffP idP); elim: u v => [| a u IHu] v /=.
- by move=> /rewrites_frontP/(rewrites_front_specP [::]).
- rewrite mem_cat => /orP[/rewrites_frontP/(rewrites_front_specP [::]) //|].
  move=> /mapP[/= w {}/IHu /[swap]->{v}].
  exact: cons_rewrites_spec.
- move=> [] [|//] /[swap] [[/= [|//] b]] /= [|//] _ -> rinR /[!cats0].
  by apply/rewrites_frontP; exists [::] ([::], b); rewrite // cats0.
- rewrite mem_cat => -[pre suf [r1 r2] /= /[dup] equ-> ->{v} rinR].
  case: pre equ => [/=| b pre /= [<-{b}]] equ; apply/orP.
    by left; apply/rewrites_frontP; exists suf (r1, r2).
  right; rewrite mem_map; last by move=> ? ? [].
  by apply: IHu; rewrite {}equ; exists pre suf (r1, r2).
Qed.

Lemma rewrites0P u : (rewrites u == [::]) = (rewrites1 u == None).
Proof.
elim: u => [|a u IHu] /=; first exact: rewrites_front0P.
rewrite cat_nil map_nil rewrites_front0P {}IHu.
apply/andP/eqP => [[/eqP-> /eqP->] // |].
by case: (rewrites1_front R (a :: u)) => //; case: (rewrites1 u).
Qed.


Inductive rewrites_to x y : Prop :=
  RewritesTo : forall l, path (fun u v => v \in rewrites u) x l ->
                  y = last x l -> rewrites_to x y.

Arguments RewritesTo {x y} (l).

Lemma rewrites_to1 x y : y \in rewrites x -> rewrites_to x y.
Proof. by move=> rew; exists [:: y]; rewrite //= andbT. Qed.

Lemma rewrites_to_refl : reflexivep rewrites_to.
Proof. by move=> x; exists [::]. Qed.
Lemma rewrites_to_trans : transitivep rewrites_to.
Proof.
move=> x y z [pathxy Hxy Hy] [pathyz Hyz Hz].
exists (pathxy ++ pathyz).
- by rewrite cat_path Hxy -Hy Hyz.
- by rewrite last_cat -Hy.
Qed.

Lemma rewrites_stable u v1 v2 w :
  v2 \in rewrites v1 -> u ++ v2 ++ w \in rewrites (u ++ v1 ++ w).
Proof.
move=> /rewritesP[pre suf [r1 r2] ->{v1} ->{v2} rinR /=].
by apply/rewritesP; exists (u ++ pre) (suf ++ w) (r1, r2); rewrite //= !catA.
Qed.
Lemma rewrites_to_stable : stablep rewrites_to.
Proof.
move=> u v1 v2 w [p path_p ->{v2}].
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
move=> incl CR_refl CR_trans CR_stable u v [p path_p ->{v}].
elim: p u path_p => [//=| p0 p IHp] u /= /andP[p0_u] {}/IHp; apply CR_trans.
move/rewritesP : p0_u => [pre suf [r1 pr] ->{u}->{p0} rinR] /=.
by apply: CR_stable; apply: (incl _ rinR).
Qed.


Section Symmetry.

Hypothesis Rsym : forall u v, (u, v) \in R -> (v, u) \in R.

Lemma rewrites_sym_impl x y :
  x \in rewrites y -> y \in rewrites x.
Proof.
move=> /rewritesP[pre suf [r1 r2] ->{y}->{x} rinR  /=].
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
rewrite last_rcons belast_rcons rev_cons => ->{y} Hpath.
exists (rcons (rev pathxz) x); last by rewrite last_rcons.
set rel := (X in path X _ _) in Hpath.
rewrite (eq_path (e' := rel)) /=; first exact: Hpath.
by rewrite /rel => u v; exact: rewrites_sym.
Qed.
Lemma rewrites_to_symE x y : rewrites_to x y <-> rewrites_to y x.
Proof. split; exact: rewrites_to_sym. Qed.

Lemma rewrites_toP : congruencep rewrites_to.
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
  move=> /rewritesP[pre suf r ->{u}->{v} ].
  by rewrite mem_cat => /orP[]; [left|right]; apply/rewritesP; exists pre suf r.
by move=> []/rewritesP[pre suf r ->{u}->{v} rinR];
       apply/rewritesP; exists pre suf r => //=; rewrite mem_cat rinR ?orbT.
Qed.
Lemma rewrites_cons p R u :
  rewrites (p :: R) u =i (rewrites [:: p] u) ++ (rewrites R u).
Proof. by move=> v; rewrite -cat1s rewrites_cat. Qed.
Lemma rewrites_rcons R p u :
  rewrites (rcons R p) u =i (rewrites [:: p] u) ++ (rewrites R u).
Proof. by move=> v; rewrite -cats1 rewrites_cat !mem_cat orbC. Qed.


Section DefPresentation.

Definition undirected R := R ++ [seq swap p | p <- R].

Lemma rewrites_map_swap_impl R u v :
  (v \in rewrites R u) -> (u \in rewrites [seq swap p | p <- R] v).
Proof.
move=> /rewritesP[pre suf [r1 r2] ->{u}->{v} rinR /=].
apply/rewritesP; exists pre suf (swap (r1, r2)) => //=.
by rewrite (mem_map swap_inj).
Qed.
Lemma rewrites_map_swap R u v :
  (u \in rewrites [seq swap p | p <- R] v) = (v \in rewrites R u).
Proof.
apply/idP/idP; last exact: rewrites_map_swap_impl.
rewrite -{2}(map_id R) -(eq_map swapK) (map_comp swap swap).
exact: rewrites_map_swap_impl.
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
Proof. exact: (rewrites_toP undirected_sym). Qed.
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

End DefPresentation.
Notation "x = y %[mod R ]" := (rewrites_to (undirected R) x y).


Section SubRule.

Variable R1 R2 : relat.
Hypothesis sub_rule : {subset R1 <= R2}.

Lemma sub_rewrites u v : v \in rewrites R1 u -> v \in rewrites R2 u.
Proof.
move=> /rewritesP[pre suf [r1 r2] /= ->{v} ->{u} rinR].
apply/rewritesP; exists pre suf (r1, r2) => //=.
exact: sub_rule.
Qed.
Lemma sub_rewrites_to u v : rewrites_to R1 u v -> rewrites_to R2 u v.
Proof.
move=> [p p_path ->{v}]; exists p => //.
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


Definition rewmorphism A B (R : relat A) (S : relat B) (f : seq A -> seq B) :=
  forall u v : word A, v \in rewrites R u -> rewrites_to S (f u) (f v).
Definition rewmorphism_to A B (R : relat A) (S : relat B) (f : seq A -> seq B) :=
  forall u v : word A, rewrites_to R u v -> rewrites_to S (f u) (f v).

HB.mixin Record isRewMorphism
  A B (R : relat A) (S : relat B) (f : {freemon A} -> {freemon B}) := {
    rewmorphism_subproof : rewmorphism R S f
  }.
HB.structure Definition RewMorphism A B (R : relat A) (S : relat B) :=
  {f of MonMorphism {freemon A} f & isRewMorphism A B R S f}.
Notation "{ 'rewmorph' R -> S }" := (RewMorphism.type R S) : type_scope.
Notation "{ 'presmorph' R -> S }" :=
  (RewMorphism.type (undirected R) (undirected S)) : type_scope.


Section RewMorphismTheory.

Variables (A B : choiceType) (R : relat A) (S : relat B) (f : {rewmorph R -> S}).

Lemma rewmorph_toP u v : v \in rewrites R u -> rewrites_to S (f u) (f v).
Proof. exact: rewmorphism_subproof. Qed.
Lemma rewmorphP u v : rewrites_to R u v -> rewrites_to S (f u) (f v).
Proof.
move=> [p Hp ->{v}].
elim: p u Hp => [u _ |p0 pth IHpth u] /=; first exact: rewrites_to_refl.
move=> /andP[p0_u {}/IHpth]; apply: rewrites_to_trans.
exact: rewmorph_toP.
Qed.

End RewMorphismTheory.


HB.factory Record isRewMorphismTo
  A B (R : relat A) (S : relat B) (f : {freemon A} -> {freemon B}) := {
    rewmorphism_to_subproof : rewmorphism_to R S f
  }.
HB.builders Context A B (R : relat A) (S : relat B) f of
  isRewMorphismTo A B R S f.
Lemma rewmorphism_toP : rewmorphism R S f.
Proof. by move=> u v /rewrites_to1/rewmorphism_to_subproof. Qed.
HB.instance Definition _  :=
  isRewMorphism.Build A B R S f rewmorphism_toP.
HB.end.

HB.factory Record isPresMorphism
  A B (R : relat A) (S : relat B) (f : {freemon A} -> {freemon B}) := {
    presmorphism_subproof : rewmorphism R S f
  }.
HB.builders Context A B (R : relat A) (S : relat B) f of
  isPresMorphism A B R S f.
Lemma rewmorphism_undirected : rewmorphism (undirected R) (undirected S) f.
Proof.
move=> u v; rewrite rewrites_undirected => /orP[|];
  move=> /presmorphism_subproof/rewrites_to_equiv //.
exact: equiv_sym.
Qed.
HB.instance Definition _  :=
  isRewMorphism.Build A B (undirected R) (undirected S) f rewmorphism_undirected.
HB.end.

HB.factory Record isPresMorphismTo
  A B (R : relat A) (S : relat B) (f : {freemon A} -> {freemon B}) := {
    presmorphism_to_subproof : rewmorphism_to R S f
  }.
HB.builders Context A B (R : relat A) (S : relat B) f of
  isPresMorphismTo A B R S f.
Lemma rewmorphism_to_undirected : rewmorphism R S f.
Proof. by move=> u v /rewrites_to1/presmorphism_to_subproof. Qed.
HB.instance Definition _  :=
  isPresMorphism.Build A B R S f rewmorphism_to_undirected.
HB.end.



Section IdMor.
Variables (A : choiceType) (R R' : relat A).
Hypothesis eqR : forall u v, rewrites_to R u v -> rewrites_to R' u v.

Definition idRR' : {freemon A} -> {freemon A} := idfun.
HB.instance Definition _  := MonMorphism.on idRR'.
HB.instance Definition _  := isRewMorphismTo.Build A A R R' idRR' eqR.
Definition idmorRR' : {rewmorph R -> R'} := idRR'.

Lemma morRR'E : idmorRR' =1 id :> (word A -> word A).
Proof. by []. Qed.

End IdMor.
Definition idmor A (R : relat A) : {rewmorph R -> R} :=
  idmorRR' (fun _ _ => idfun).


Section RewMorphismTheory.

Variables (A B C : choiceType) (R : relat A) (S : relat B) (T : relat C)
  (f : {rewmorph R -> S}) (g : {rewmorph S -> T}).

Fact comp_is_rewmorphism : rewmorphism_to R T (g \o f).
Proof. by move=> u v H; do 2! apply rewmorphP. Qed.
HB.instance Definition _ :=
  isRewMorphismTo.Build A C R T (g \o f) comp_is_rewmorphism.

End RewMorphismTheory.


Record isopres (A B : choiceType) (R : relat A) (S : relat B) := IsoPres {
    mor :> {presmorph R -> S};
    inv : {presmorph S -> R};
    canmor : forall a : word A, inv (mor a) = a %[mod R];
    caninv : forall b : word B, mor (inv b) = b %[mod S]
  }.

Definition isopres_sym A B (R : relat A) (S : relat B)
  (eq : isopres R S) := IsoPres (caninv eq) (canmor eq).
Lemma isopres_symK  A B (R : relat A) (S : relat B) eq :
  ((@isopres_sym B A S R) \o (@isopres_sym A B R S)) eq = eq.
Proof. by rewrite /isopres_sym; move: eq => [m i cm ci]/=. Qed.


Lemma isopresP A B (R : relat A) (S : relat B) (eq : isopres R S) u v :
  eq u = eq v %[mod S] <-> u = v %[mod R].
Proof.
split => [/(rewmorphP (inv eq)) H |]; last exact: rewmorphP.
apply: (equiv_trans (equiv_sym (canmor eq u))).
exact: (equiv_trans H (canmor _ _)).
Qed.
Lemma isopres_invP A B (R : relat A) (S : relat B) (eq : isopres R S) u v :
  inv eq u = inv eq v %[mod R] <-> u = v %[mod S].
Proof. exact: (isopresP (isopres_sym eq)). Qed.


Section IsopresTheory.
Variables (A B C : choiceType) (R : relat A) (S : relat B) (T : relat C).

Definition isopres_refl :=
  let uR := undirected R in IsoPres (mor := idmor uR) (inv := idmor uR)
                              (rewrites_to_refl uR) (rewrites_to_refl uR).

Variable (eqRS : isopres R S) (eqST : isopres S T).
Fact canmor_trans a : (inv eqRS \o inv eqST) ((eqST \o eqRS) a) = a %[mod R].
Proof.
have := canmor eqST (eqRS a); rewrite -(isopres_invP eqRS) /=.
by move/equiv_trans; apply; apply canmor.
Qed.
Fact invmor_trans c : (eqST \o eqRS) ((inv eqRS \o inv eqST) c) = c %[mod T].
Proof.
have := caninv eqRS (inv eqST c); rewrite -(isopres_invP eqST) /=.
by move/(equiv_trans _); apply; apply canmor.
Qed.
Definition isopres_trans := IsoPres canmor_trans invmor_trans.
Lemma isopres_transE : isopres_trans =1 eqST \o eqRS.
Proof. by []. Qed.
Lemma isopres_trans_invE : inv isopres_trans =1 (inv eqRS \o inv eqST).
Proof. by []. Qed.

End IsopresTheory.


Section PresEqEquivTheory.
Variables (A : choiceType) (R R' : relat A).
Hypothesis eqR : forall u v, u = v %[mod R] <-> u = v %[mod R'].

Let mor_subproof u v : u = v %[mod R] -> u = v %[mod R'].
Proof. by rewrite eqR. Qed.
Let inv_subproof u v : u = v %[mod R'] -> u = v %[mod R].
Proof. by rewrite eqR. Qed.
Let morRR' : {presmorph R -> R'} := idmorRR' mor_subproof.
Let morR'R : {presmorph R' -> R} := idmorRR' inv_subproof.
Fact canmor_eq a : morR'R (morRR' a) = a %[mod R].
Proof. exact: equiv_refl. Qed.
Fact caninv_eq a : morRR' (morR'R a) = a %[mod R'].
Proof. exact: equiv_refl. Qed.
Definition isopres_eq : isopres R R' := IsoPres canmor_eq caninv_eq.

End PresEqEquivTheory.


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
move=> [p /[swap] ->{y}]; elim: p x => [|p0 p IHp] x /=.
  by move=> _; exists [::].
move=> /andP[p0_rew {}/IHp p0_p].
suff {p0_p} x_p0 : rewrites_to R x p0 by apply: (rewrites_to_trans x_p0 p0_p).
move: p0_rew; rewrite rewrites_cons mem_cat => /orP[]; last exact: rewrites_to1.
move=> /rewritesP[pre suf [r1 r2] ->{x}->{p0} /[!inE]/eqP[->{r1}->{r2}]]/=.
exact: (rewrites_to_stable pre suf cuv).
Qed.


(** First Tietze transformation, equivalence version *)
Variable (R : relat A) (u v : word A) (Ruv : u = v %[mod R]).

Lemma equiv_cons_rule x y : x = y %[mod R] <-> x = y %[mod (u, v) :: R].
Proof.
rewrite (rewrites_to_cons_rule Ruv).
have rvu : rewrites_to ((u, v) :: undirected R) v u.
  by rewrite -(rewrites_to_cons_rule Ruv); apply: equiv_sym.
rewrite (rewrites_to_cons_rule rvu) {rvu}.
apply: eq_rewrites_to => {x y}[[/= x y]].
rewrite !(mem_undirected, inE) -[(y, x) == _](inj_eq swap_inj) /swap /=.
by case: eqP; rewrite !(orbT, orbA).
Qed.
Definition isopres_cons_rule := isopres_eq equiv_cons_rule.

Lemma equiv_rcons_rule x y : x = y %[mod R] <-> x = y %[mod rcons R (u, v)].
Proof.
rewrite (equiv_cons_rule x y); apply eq_equiv => /= p.
by rewrite mem_rcons.
Qed.
Definition isopres_rcons_rule := isopres_eq equiv_rcons_rule.

End Tietze1.


Definition correctpres (R : relat nat) (P : pred nat) :=
  all (fun p => all P p.1 && all P p.2) R.

Section Tietze2.

Context (R : relat nat) (P : pred nat) (gen : nat) (w : word nat).
Hypothesis Rcorr : correctpres R P.
Hypothesis wcorr : all P w.
Hypothesis gen_nP : ~~ P gen.

Implicit Types (u v x y : word nat).

Definition Tietze2 := rcons R ([:: gen], w).

Lemma subset_Tietze2 : {subset R <= Tietze2}.
Proof. by move=> /= p; rewrite mem_rcons inE orbC => ->. Qed.
Lemma sub_Tietze2 u v : u = v %[mod R] -> u = v %[mod Tietze2].
Proof. exact: (sub_equiv subset_Tietze2). Qed.

Definition T2mor : {presmorph R -> Tietze2} := idmorRR' sub_Tietze2.

Definition T2inv : {freemon nat} -> {freemon nat} :=
  fun u => (\prod_(i <- u) if i != gen then [fmon i] else w)%M.
Fact T2inv_monmorphism : monmorphism T2inv.
Proof. by rewrite /T2inv; split => [|u v]; rewrite ?big_nil ?big_cat. Qed.
HB.instance Definition _ :=
  isMonMorphism.Build {freemon nat} {freemon nat} T2inv T2inv_monmorphism.

Lemma T2inv_gen : T2inv [:: gen] = w.
Proof. by rewrite /T2inv big_seq1 eqxx. Qed.
Lemma allP_T2inv u : all P u -> T2inv u = u.
Proof.
rewrite /T2inv; elim: u => [| u0 u IHu] /=; first by rewrite big_nil.
rewrite big_cons => /andP[Pgen {}/IHu ->].
case: eqP gen_nP => [<- /[!Pgen] // | _ _] /=.
by rewrite -mul_catE cat1s.
Qed.
Lemma T2inv_w : T2inv w = w.
Proof. exact: allP_T2inv. Qed.

Lemma T2inv_rewrites_to u : rewrites_to Tietze2 u (T2inv u).
Proof.
rewrite /T2inv; elim: u => [| u0 u /(rewrites_to_cat _) IHu] /=.
  by rewrite big_nil; exists [::].
rewrite big_cons -mul_catE -cat1s; apply: IHu.
case: eqP => [-> |_] /= ; last exact: rewrites_to_refl.
apply: rewrites_to1; rewrite /Tietze2 rewrites_rcons mem_cat.
by rewrite {1}/rewrites /= eq_refl /= cats0 inE eq_refl.
Qed.
Lemma T2invE u : u = T2inv u %[mod Tietze2].
Proof. exact: (rewrites_to_equiv (T2inv_rewrites_to u)). Qed.
Fact rewmorphism_T2inv : rewmorphism Tietze2 R T2inv.
Proof.
rewrite /Tietze2 => u v /rewritesP[pre suf [r1 r2]] ->{u}->{v}.
rewrite mem_rcons inE => /orP[/eqP [->{r1}->{r2}] | rinR] /=.
  rewrite -cat1s !mul_catE !mmorphM /= -!mul_catE; apply: rewrites_to_stable.
  by rewrite T2inv_gen T2inv_w; apply: rewrites_to_refl.
rewrite !mul_catE !mmorphM /= -!mul_catE.
move/allP: Rcorr => /=/(_ _ rinR) /= /andP[/allP_T2inv-> /allP_T2inv->].
by apply: rewrites_to1; apply/rewritesP; exists (T2inv pre) (T2inv suf) (r1, r2).
Qed.
HB.instance Definition _  :=
  isPresMorphism.Build nat nat Tietze2 R T2inv rewmorphism_T2inv.

Lemma T2morK u : all P u -> T2inv (T2mor u) = u %[mod R].
Proof. by move/allP_T2inv => ->; apply: equiv_refl. Qed.
Lemma T2invK v : T2mor (T2inv v) = v %[mod Tietze2].
Proof. exact: (equiv_trans (equiv_refl _ _) (equiv_sym (T2invE v))). Qed.

End Tietze2.


Import Order.TTheory.
Import Order.LexiSyntax.

Fact sizelexidisplay : unit. Proof. by []. Qed.

Section SizeLex.
Variable (d : unit) (T : orderType d).
Implicit Types (u v w x y : seq T).

Definition sizelex u v :=
  (size u < size v) || (size u == size v) && (u <= v :> seqlexi _)%O.

Lemma sizelex_le u v : sizelex u v -> size u <= size v.
Proof. by move=> /orP[/ltnW | /andP[/eqP -> _]]. Qed.

Fact sizelex_refl : reflexive sizelex.
Proof. by move=> u; rewrite /sizelex eqxx lexx /= orbT. Qed.
Fact sizelex_anti : antisymmetric sizelex.
Proof.
move=> u v /andP[/orP[ltsz | /andP[/eqP eqsz leuv]]].
  move/orP => []; first by rewrite (leq_gtF (ltnW ltsz)).
  by rewrite (gtn_eqF ltsz).
move=> /orP[| /andP[_ levu]]; first by rewrite eqsz ltnn.
by apply/eqP; rewrite (eq_le (u : seqlexi _)) leuv levu.
Qed.
Fact sizelex_trans : transitive sizelex.
Proof.
move=> v u w /orP[ltsz /sizelex_le | /andP[/eqP eqszuv leuv]].
  by move=> /(leq_trans ltsz) {}ltsz; apply/orP; left.
move=> /orP[ltsz | /andP[/eqP eqszvw levw]].
  by apply/orP; left; rewrite eqszuv.
apply/orP; right; rewrite eqszuv eqszvw eqxx /=.
exact: (le_trans leuv levw).
Qed.
HB.instance Definition _  := Order.Le_isPOrder.Build sizelexidisplay
                               (seq T) sizelex_refl sizelex_anti sizelex_trans.
Fact sizelex_total : total sizelex.
Proof.
rewrite /sizelex => u v; case: (ltngtP (size u) (size v)) => cmpsz //=.
by case: (leP (u : seqlexi _) v) => //= /ltW.
Qed.
HB.instance Definition _  := Order.POrder_isTotal.Build sizelexidisplay
                               (seq T) sizelex_total.
Fact nil_bot u : ([::] <= u)%O.
Proof.
rewrite /Order.le /= /sizelex /= eq_sym.
by case: (boolP (size u == 0)) => [/nilP -> |]; last rewrite -lt0n => ->.
Qed.
HB.instance Definition _  := Order.hasBottom.Build sizelexidisplay
                               (seq T) nil_bot.

Lemma le_sizelexiE u v :
  (u <= v)%O =
    (size u < size v) || (size u == size v) && (u <=^l v :> seqlexi _)%O.
Proof. by []. Qed.

Lemma lt_sizelexiE u v :
  (u < v)%O =
    (size u < size v) || (size u == size v) && (u <^l v :> seqlexi _)%O.
Proof.
rewrite !lt_neqAle; case: eqP => [-> | _] //=.
by rewrite andbF orbF ltnn.
Qed.

Lemma size_le_sizelexi u v : (u <= v)%O -> size u <= size v.
Proof. by rewrite le_sizelexiE => /orP[/ltnW|/andP[/eqP-> _]]. Qed.

End SizeLex.


Section SizeLexNat.
Implicit Types (u v w x y : seq nat).

Lemma sizelex_wf : well_founded  (@Order.lt _ (seq nat)).
Proof.
pose ltb b u v := is_true ((size v <= b) && (u < v)%O).
suff bwf b : well_founded (ltb b).
  move=> u; have [n] := ubnPleq (size u).
  elim/(well_founded_induction (bwf n)): u => u IHu szu.
  apply: Acc_intro => y ltyu; apply: IHu; first by rewrite /ltb szu ltyu.
  exact: (leq_trans (size_le_sizelexi (ltW ltyu)) szu).
elim: b => [| b IHb].
  move=> u; apply: Acc_intro => y /andP[/[!leqn0]/nilP ->].
  by rewrite ltNge nil_bot.
have rec u : size u <= b -> Acc (ltb b.+1) u.
  elim/(well_founded_induction IHb) : u => u IHu szu.
  apply: Acc_intro => v /andP[_ ltvu]; apply IHu; first by rewrite /ltb szu ltvu.
  exact: (leq_trans (size_le_sizelexi (ltW ltvu)) szu).
suff rec' u : size u <= b.+1 -> Acc (ltb b.+1) u.
  move=> u; apply: Acc_intro => y /andP[szu /ltW/size_le_sizelexi].
  move/leq_trans/(_  szu); exact: rec'.
rewrite leq_eqVlt => /orP[/eqP szu|]; last exact: rec.
case: u szu => [//| u0 u] /= [szu].
have [m] := ubnP u0; elim: m u0 u szu => [| m IHm] u0 u; first by rewrite ltn0.
rewrite ltnS leq_eqVlt => szu /orP[/eqP->{u0}|]; last exact: IHm.
elim/(well_founded_induction IHb) : u szu => u recm szu.
apply: Acc_intro => y /andP[_].
rewrite lt_sizelexiE /= ltnS => /orP[|]; first by rewrite szu; apply: rec.
case: y => [//| a v] /= /andP[/eqP[/[!szu] szv]].
rewrite Order.SeqLexiOrder.ltxi_cons.
rewrite le_eqVlt => /andP[/orP[/eqP->{a} | ltam _]]; last exact: IHm.
rewrite lexx /= => lexvu; apply: recm => //.
by rewrite /ltb szu leqnn /= lt_sizelexiE orbC szu szv eqxx lexvu.
Qed.

End SizeLexNat.



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
   ([:: 2; 1; 1], [::1; 1; 2; 1]);
   ([:: 1; 2], [:: 3]);
   ([:: 2; 1], [:: 4]);
   ([:: 1; 3], [:: 5]);
   ([:: 1; 4], [:: 3; 1]);
   ([:: 2; 3], [:: 4; 2]);
   ([:: 2; 5], [:: 5; 3])].

Goal not (correctpres present_page_3_1 (geq 3)). by []. Qed.
Goal not (correctpres present_page_3_1 (geq 4)). by []. Qed.
Goal correctpres present_page_3_1 (geq 5). by []. Qed.
Goal correctpres present_page_3_1 (geq 6). by []. Qed.


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
