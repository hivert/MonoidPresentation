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

Require Import monoids vectNK.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section Defs.

Variable (Alph : eqType).

Definition word := seq Alph.
Definition relat := seq (word * word).

Implicit Types (R : relat) (u v w x y : word) (p : word * word).

Section RelationsTerminology.

Variable RP : word -> word -> Prop.

Definition reflexivep := forall u, RP u u.
Definition symmetricp := forall u v, RP u v -> RP v u.
Definition transitivep := forall u v w, RP u v -> RP v w -> RP u w.
Definition equivalencep := [/\ reflexivep, symmetricp & transitivep].
Definition stablep :=
  forall a b1 b2 c, RP b1 b2 -> RP (a ++ b1 ++ c) (a ++ b2 ++ c).
Definition congruencep := equivalencep /\ stablep.

End RelationsTerminology.


Section DefPresentation.

Variable (R : relat).

(** TODO : a very inefficient way to compute all the way to rewrite a word *)
Definition rewrites w :=
  flatten [seq [seq (triple.1.1) ++ p.2 ++ (triple.2) | p <- R & p.1 == triple.1.2]
          | triple <- cut3 w ].
Inductive elem_rewrites u v : Prop :=
  IsRelated : forall (pre suf : word) (rule : word * word),
      rule \in R -> u = pre ++ rule.1 ++ suf -> v = pre ++ rule.2 ++ suf
               -> elem_rewrites u v.

Lemma rewritesP u v : reflect (elem_rewrites u v) (v \in rewrites u).
Proof.
apply (iffP flatten_mapP) => /=[[[[pre p1 suf]]]|].
  rewrite -cat3_equiv_cut3 => /eqP->{u} /mapP/=[[r1 r2]] /=.
  rewrite mem_filter => /andP/=[/eqP <-{p1} rinR ->{v}].
  exact: (IsRelated rinR erefl erefl).
move=> [pre suf [p1 p2] inR ->{u} ->{v}] /=.
exists (pre, p1, suf) => /=; first by rewrite -cat3_equiv_cut3.
by apply/mapP => /=; exists (p1, p2); rewrite //= mem_filter /= eqxx.
Qed.

Inductive rewrites_to x y : Prop :=
  Rew : forall l, path (fun u v => v \in rewrites u) x l ->
                  y = last x l -> rewrites_to x y.

Arguments Rew {x y} (l).

Lemma rewrites_to_refl : reflexivep rewrites_to.
Proof. by move=> x; exists [::]. Qed.
Lemma rewrites_to_trans : transitivep rewrites_to.
Proof.
move=> x y z [pathxy Hxy Hy] [pathyz Hyz Hz].
apply: (Rew (pathxy ++ pathyz)).
- by rewrite cat_path Hxy -Hy Hyz.
- by rewrite last_cat -Hy.
Qed.

Lemma rewrites_stable u v1 v2 w :
  v2 \in rewrites v1 -> u ++ v2 ++ w \in rewrites (u ++ v1 ++ w).
Proof.
move=> /rewritesP[pre suf [r1 r2] rinR ->{v1} ->{v2} /=].
by apply/rewritesP; exists (u ++ pre) (suf ++ w) (r1, r2); rewrite //= !catA.
Qed.

Lemma rewrites_to_stable : stablep rewrites_to.
Proof.
move=> u v1 v2 w [p path_p ->{v2}].
pose F b := u ++ b ++ w; rewrite -/(F v1).
exists [seq F b | b <- p]; last by rewrite last_map.
by move: path_p; apply: homo_path => x y; apply: rewrites_stable.
Qed.


Section Symmetry.

Hypothesis Rsym : forall u v, (u, v) \in R -> (v, u) \in R.

Lemma rewrite_sym_impl x y :
  x \in rewrites y -> y \in rewrites x.
Proof.
move=> /rewritesP[pre suf [r1 r2] rinR ->{y} ->{x} /=].
apply/rewritesP; exists pre suf (r2, r1) => //.
exact: Rsym.
Qed.

Lemma rewrite_sym x y :
  (x \in rewrites y) = (y \in rewrites x).
Proof. by apply/idP/idP; exact: rewrite_sym_impl. Qed.

Lemma rewrites_to_sym : symmetricp rewrites_to.
Proof.
move=> x y [pathxy]; rewrite -rev_path => Hxy Hy.
move: Hxy; rewrite -Hy.
case/lastP: pathxy Hy => [/= -> _ | pathxz z]; first exact: (Rew [::]).
rewrite last_rcons belast_rcons rev_cons => ->{y} Hpath.
apply: (Rew (rcons (rev pathxz) x)); last by rewrite last_rcons.
set rel := (X in path X _ _) in Hpath.
rewrite (eq_path (e' := rel)) /=; first exact: Hpath.
by rewrite /rel => u v; exact: rewrite_sym.
Qed.
Lemma rewrites_to_symE x y : rewrites_to x y <-> rewrites_to y x.
Proof. split; exact: rewrites_to_sym. Qed.

Lemma rewrites_toP : congruencep rewrites_to.
Proof.
split; last exact rewrites_to_stable.
split; [exact: rewrites_to_refl | exact: rewrites_to_sym | exact: rewrites_to_trans].
Qed.

End Symmetry.


Lemma rewrites_to_min CR :
  (forall p, p \in R -> CR p.1 p.2) ->
  reflexivep CR -> transitivep CR -> stablep CR ->
  forall u v, rewrites_to u v -> CR u v.
Proof.
move=> incl CR_refl CR_trans CR_stable u v [p path_p ->{v}].
elim: p u path_p => [//=| p0 p IHp] u /= /andP[p0_u] {}/IHp; apply CR_trans.
move/rewritesP : p0_u => [pre suf [p1 p2] inR ->{u} ->{p0}] /=.
by apply: CR_stable; apply: (incl _ inR).
Qed.

End DefPresentation.


Section SubRule.

Variable R1 R2 : relat.
Hypothesis subRule : forall p, p \in R1 -> p \in R2.

Lemma sub_rewrites u v : v \in rewrites R1 u -> v \in rewrites R2 u.
Proof.
move=> /rewritesP[pre suf [r1 r2] rinR /= ->{v} ->{u}].
apply/rewritesP; exists pre suf (r1, r2) => //=.
exact: subRule.
Qed.
Lemma sub_rewrites_to u v : rewrites_to R1 u v -> rewrites_to R2 u v.
Proof.
move=> [p p_path ->{v}]; exists p => //.
by move: p_path; apply (sub_path sub_rewrites).
Qed.

End SubRule.


Section EqRule.

Variable R1 R2 : relat.
Hypothesis eqRule : R1 =i R2.

Lemma eq_rewrites u : (rewrites R1 u) =i (rewrites R2 u).
Proof. by move=> v; apply/idP/idP; apply: sub_rewrites => p /[!eqRule]. Qed.
Lemma eq_rewrites_to u v : rewrites_to R1 u v <-> rewrites_to R2 u v.
Proof. by split; apply: sub_rewrites_to => p /[!eqRule]. Qed.

End EqRule.


Section TietzeAddRule.

Variables (R : relat) (u v : word).
Hypothesis (cuv : rewrites_to R u v).

Let R' := (u, v) :: R.

Lemma rewrites_to_add_rule x y :
  rewrites_to R x y <-> rewrites_to R' x y.
Proof.
rewrite /R'; split.
  by apply: sub_rewrites_to => p p_inR; rewrite inE p_inR orbT.
move=> [p /[swap] ->{y}]; elim: p x => [|p0 p IHp] x /=.
  by move=> _; exists [::].
move=> /andP[p0_rew {}/IHp p0_p].
suff {p0_p} x_p0 : rewrites_to R x p0 by apply: (rewrites_to_trans x_p0 p0_p).
move: p0_rew => /rewritesP[pre suf [r1 r2]].
rewrite inE => /=/orP[/eqP[->{r1}->{r2}] ->{x} eqp0 | rinR eqx eqp0 ]; first last.
  exists [:: p0]; rewrite //= andbT.
  by apply/rewritesP; exists pre suf (r1, r2).
by rewrite {p0}eqp0; apply: (rewrites_to_stable pre suf cuv).
Qed.

End TietzeAddRule.

End Defs.


Definition catmorphism A B (f : seq A -> seq B) : Prop :=
  forall a b : seq A, f (a ++ b) = f a ++ f b.

HB.mixin Record isCatMorphism A B (f : seq A -> seq B) := {
  catmorphism_subproof : catmorphism f
}.
HB.structure Definition CatMorphism A B :=
  {f of isCatMorphism A B f}.
Notation "{ 'catmorphism' U -> V }" := (CatMorphism.type U%type V%type)
    : type_scope.

Lemma idfun_is_catmorphism A : catmorphism (@idfun (seq A)).
Proof. by []. Qed.
HB.instance Definition _ A :=
  isCatMorphism.Build A A (@idfun (seq A)) (@idfun_is_catmorphism A).


Section RelMorphisms.

Variables (A : eqType) (RA : seq A -> seq A -> Prop).
Variables (B : eqType) (RB : seq B -> seq B -> Prop).
Definition relmorphism (f : seq A -> seq B) : Prop :=
  forall a b : seq A, RA a b -> RB (f a) (f b).

End RelMorphisms.





Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]); ([:: 1], [:: 0])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Eval vm_compute in rewrites [:: ([:: 2; 2], [:: 1]);
                             ([:: 1], [:: 0]);
                             ([:: 2; 1; 2], [::])]
                     [:: 1; 2; 1; 2; 2; 1; 2; 2].

Definition rew_page_3_1 :=
  [::
   ([:: 2; 1; 1], [::1; 1; 2; 1]);
   ([:: 1; 2], [:: 3]);
   ([:: 2; 1], [:: 4]);
   ([:: 1; 3], [:: 5]);
   ([:: 1; 4], [:: 3; 1]);
   ([:: 2; 3], [:: 4; 2]);
   ([:: 2; 5], [:: 5; 3])].

Definition present_page_3_1 :=
  rew_page_3_1 ++ [seq (p.2, p.1) | p <- rew_page_3_1].

Lemma step_3_1 : rewrites_to present_page_3_1 [:: 2; 5] [:: 5; 3].
Proof.
by exists [::
        [:: 2; 1; 3];
        [:: 2; 1; 1; 2];
        [:: 1; 1; 2; 1; 2];
        [:: 1; 3; 1; 2];
        [:: 5; 1; 2];
        [:: 5; 3]].
Qed.
