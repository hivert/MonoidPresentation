(** * Various Word Problem Decidability criteria (most are admitted)          *)
(******************************************************************************)
(*      Copyright (C) 2025      Anonymous        *)
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
From Coq Require Import Uint63.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq order.

Require Import well_founded monoids present factor rewcert sizelexi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma flatten0 (T : eqType) (s : seq (seq T)) :
  flatten s = [::] -> all (@nilp _) s.
Proof.
move=> /(congr1 size); rewrite size_flatten /= => /eqP/natnseq0P shape0.
apply/(all_nthP [::]) => i _; apply/eqP.
by rewrite -nth_shape shape0 nth_nseq if_same.
Qed.

Section Fenced.

Context {Alph : choiceType}.
Implicit Types (a b : Alph) (u v w : word Alph).

Variant first_occ_spec (G : pred Alph) u : Type :=
  FirstOcc a u0 u1 : all (predC G) u0 -> G a -> u = u0 ++ a :: u1
                     -> first_occ_spec G u.
Lemma first_occP G u : has G u -> first_occ_spec G u.
Proof.
move=> pu.
have x0 : Alph by case: u pu.
move: pu; case: findP => // i ltiu /(_ x0); set a := nth x0 u i => Hb.
move/(_ a) => before _.
have:= cat_take_drop i u; rewrite (drop_nth x0 ltiu) => eq.
suff : all (predC G) (take i u).
  by exists (nth x0 u i) (take i u) (drop i.+1 u).
apply/allP => x /[dup] xin.
rewrite -{1}index_mem size_take ltiu => {}/before /=.
have:= xin => /(nth_index a); rewrite nth_take => [-> -> //|].
have:= size_take i u; rewrite ltiu => {2}<-.
by rewrite index_mem.
Qed.

Variable (G : pred Alph) (R : relat Alph).
Hypothesis (GR : all (fun r => all G r.1 && all G r.2) R).

Lemma fenced_leq_size u0 a u1 v0 v1 :
  u0 ++ a :: u1 = v0 ++ v1 -> ~~ G a -> all G v0 -> size v0 <= size u0.
Proof.
move=> eq nGa /allP Gv0.
rewrite leqNgt -(size_rcons u0 a) -cats1; apply/negP => ltu0av0.
move: eq; rewrite -cat1s catA => /(cat2E ltu0av0) [w] _ eqr1.
by move: nGa; rewrite Gv0 // eqr1 !mem_cat inE eqxx /= orbT.
Qed.

Lemma fenced_eq u0 a b u1 v0 v1 :
  all G u0 -> ~~ G a -> all G v0 -> ~~ G b ->
  u0 ++ a :: u1 = v0 ++ b :: v1 -> (u0, a, u1) = (v0, b, v1).
Proof.
move=> Gu0 nGa Gv0 nGb /[dup] eq /eqP.
have {eq}/eqseq_cat -> : size u0 = size v0.
  apply anti_leq; apply/andP; split.
  + by move: eq => /esym/fenced_leq_size/(_ nGb); apply.
  + by move: eq => /fenced_leq_size/(_ nGa); apply.
by case/andP => /eqP -> /eqP[->->].
Qed.

Lemma rewrites_count u v :
  v \in rewrites R u -> count (predC G) v = count (predC G) u.
Proof.
case/rewritesP => pre suf [r1 r2] /= {u}-> {v}-> /(allP GR) /andP[/= Gr1 Gr2].
rewrite !count_cat; congr (_ + (_ + _)) => {pre suf}.
suff allGcount u : all G u -> count (predC G) u = 0 by rewrite !allGcount.
by move=> allG; apply/eqP; rewrite -leqn0 leqNgt -has_count has_predC allG.
Qed.
Lemma rewrites_to_count u v :
  rewrites_to R u v -> count (predC G) u = count (predC G) v.
Proof.
case=> pth /[swap] {v}->; elim: pth u => [//| p0 pth IHpth] u /=.
by case/andP => /rewrites_count <- /IHpth.
Qed.
Lemma rewrites_all u v : v \in rewrites R u -> all G u = all G v.
Proof.
move/rewrites_count.
by rewrite -(negbK (all G u)) -(negbK (all G v)) -!has_predC !has_count => ->.
Qed.
Lemma rewrites_to_all u v : rewrites_to R u v -> all G u = all G v.
Proof.
move/rewrites_to_count.
by rewrite -(negbK (all G u)) -(negbK (all G v)) -!has_predC !has_count => ->.
Qed.

Lemma fenced_rewrites (a : Alph) u0 u1 v :
  all G u0 -> ~~ G a -> v \in rewrites R (u0 ++ a :: u1) ->
  (exists v0, v0 \in rewrites R u0 /\ v = v0 ++ a :: u1) \/
  (exists v1, v1 \in rewrites R u1 /\ v = u0 ++ a :: v1).
Proof.
move=> /= Gu0 nGa Ruv.
have /first_occP[b v0 v1] : has (predC G) v.
  by rewrite has_predC -(rewrites_all Ruv) all_cat /= (negbTE nGa) /= andbF.
have /eq_all -> : predC (predC G) =1 G by move=> x; rewrite /= negbK.
rewrite /= => Gv0 nGb eqv; subst v.
move/rewritesP: Ruv => [pre suf [r1 r2]] /= equ eqv.
move=> /[dup] rinR /(allP GR) /= /andP[Gr1 Gr2].
case: (leqP (size pre) (size u0)) => [lepreu0 | ltu0pre].
- left; case: (cat2E lepreu0 (esym equ)) => w eqr1suf equ0 {lepreu0}.
  have ler1w : size r1 <= size w.
    exact: (fenced_leq_size (esym eqr1suf) nGa Gr1).
  move: eqr1suf => /(cat2E ler1w) [x] eqsuf eqw {ler1w}; subst w suf.
  have allG2 : all G ((pre ++ r2) ++ x).
    by move: Gu0; rewrite equ0 !all_cat Gr2 /= => /and3P[-> _ ->].
  have {equ} eqv0 : v0 = pre ++ r2 ++ x.
    by move: eqv; rewrite !catA => /(fenced_eq Gv0 nGb allG2 nGa)[].
  move/eqP: eqv; rewrite eqv0 equ0 !catA eqseq_cat // => /andP[_ /eqP[-> ->]].
  exists ((pre ++ r2) ++ x); rewrite -!catA; split; last by [].
  by apply/rewritesP; exists pre x (r1, r2).
- right; move: ltu0pre.
  rewrite -(size_rcons u0 a) -cats1 => /cat2E H.
  move: equ; rewrite -cat1s catA => {}/H [w equ1 eqpre]; subst pre u1.
  move: eqv; rewrite -!catA cat1s => /(fenced_eq Gv0 nGb Gu0 nGa)[-> -> ->].
  exists (w ++ r2 ++ suf); split; last by [].
  by apply/rewritesP; exists w suf (r1, r2).
Qed.

Lemma fenced_rewrites_to a u0 u1 v :
  all G u0 -> ~~ G a -> rewrites_to R (u0 ++ a :: u1) v ->
  exists v0 v1,
    [/\ rewrites_to R u0 v0, rewrites_to R u1 v1 & v = v0 ++ a :: v1].
Proof.
move=> Gu0 nGa [pth] /[swap] {v}->.
elim: pth => [|p0 pth IHpth] /= in u0 u1 Gu0 *.
  by move=> _; exists u0; exists u1; split => //; exact: rewrites_to_refl.
case/andP=> /(fenced_rewrites Gu0 nGa)[].
- case=> v0 [u0Rv0 {p0}->].
  move: Gu0; rewrite (rewrites_all u0Rv0) => {}/IHpth/[apply].
  case=> w0 [w1] [v0Rw0 v1Rw1 eq]; exists w0; exists w1; split=> //=.
  exact: (rewrites_to_trans (rewrites_to1 u0Rv0)).
- case=> v1 [u1Rv1 {p0}->].
  move: Gu0 => {}/IHpth/[apply].
  case=> w0 [w1] [v0Rw0 v1Rw1 eq]; exists w0; exists w1; split=> //=.
  exact: (rewrites_to_trans (rewrites_to1 u1Rv1)).
Qed.

End Fenced.


Section AlphabetChange.

Context {Alph : choiceType}.

Theorem outwords_of_dec (P : pres Alph) :
  WPdecidable P -> forall u v : word Alph, decidable (u = v %[mod P]).
Proof.
pose G := mem (pgen P).
have GR : all (fun r => all G r.1 && all G r.2) (undirected P).
  rewrite /undirected all_cat.
  have:= wf_relat P; rewrite /all_relwords => ->.
  exact: flipped_pres_subproof.
have cnteq := rewrites_to_count GR.
move=> Hdec u; move: {2}(count _ _) (erefl (count (predC G) u)) => n.
elim: n u => [| n IHn] u.
  move/eqP; rewrite -leqn0 leqNgt -has_count has_predC negbK => Pu v.
  have {}Pu : u \in words_of P by exact: Pu.
  case: (boolP (v \in words_of P)) => [Pv | nPv]; first exact: Hdec.
  by right=> equv; move: nPv; rewrite -(equiv_words_ofE equv) Pu.
move=> cntu v.
have /first_occP[a u0 u1] : has (predC G) u by rewrite has_count cntu.
rewrite all_predC has_predC negbK /= => Gu0 nGa equ.
case: (altP (count (predC G) u =P count (predC G) v)) =>
      [/esym|/negbTE neqout]; last by right => {}/cnteq /eqP; rewrite neqout.
rewrite cntu => cntv.
have {cntv}/first_occP[b v0 v1] : has (predC G) v by rewrite has_count cntv.
rewrite all_predC has_predC negbK /= => Gv0 nGb eqv.
have {nGb} equv : u = v %[mod P] <->
                 [/\ a = b, u0 = v0 %[mod P] & u1 = v1 %[mod P] ].
  rewrite {IHn u cntu}equ {v}eqv.
  split=> [|[eqab eq0 eq1]]; first last.
    apply: (stable_cat (@equiv_trans _ _) (@equiv_stable _ _)) => //.
    rewrite -{}eqab -(cat1s a u1) -(cat1s a v1).
    apply: (stable_cat (@equiv_trans _ _) (@equiv_stable _ _)) => //.
    exact: equiv_refl.
  move/(fenced_rewrites_to GR Gu0 nGa) => [w0][w1][u0Rw0 u1Rw1].
  have Gw0 : all G w0 by rewrite -(rewrites_to_all GR u0Rw0).
  by case/(fenced_eq Gv0 nGb Gw0 nGa)=> -> -> ->.
case: (altP (a =P b)) => [eqab | /negbTE neqab]; first last.
  by right; rewrite {}equv => [[/eqP]]; rewrite neqab.
subst b.
case: (Hdec u0 v0 Gu0 Gv0) => {Gv0} [eq0 | neq0]; first last.
  by right; rewrite equv => [[_ eq0 _]]; exact: neq0.
have : count (predC G) u = (count (predC G) u1).+1.
  move: nGa; rewrite equ count_cat /= => ->; rewrite add1n.
  suff -> : count (predC G) u0 = 0 by [].
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_predC negbK.
rewrite {}cntu => -[] /esym {}/IHn/(_ v1) [eq1 | neq1]; first last.
  by right; rewrite equv => [[_ eq1]]; exact: neq1.
by left; rewrite equv.
Qed.

Corollary eqrelat_dec (P1 P2 : pres Alph) :
  prelat P1 = prelat P2 -> WPdecidable P1 -> WPdecidable P2.
Proof. by move=> eq /outwords_of_dec dec u v _ _; rewrite -eq. Qed.

End AlphabetChange.


Section Trivial.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition trivial_relats P := all (fun r => r.1 == r.2) (prelat P).

Proposition trivial_relats_dec P : trivial_relats P -> WPdecidable P.
Proof.
rewrite /trivial_relats => /= /allP Htriv u v _ _.
case: (altP (u =P v)) => [{u}->| nequv]; first by left; exact: equiv_refl.
right => -[pth Hpth equv]; move: nequv; rewrite {v}equv => /negP; apply.
elim: pth u Hpth => [|p0 pth IHpth] u //=.
case/andP=> [/[swap]{}/IHpth/eqP{1}->]; move: (last _ _) => {p0}v.
case/rewritesP => pre suf [r1 r2] {u}-> {v}-> /=.
by rewrite mem_undirected => /orP[] /Htriv /= => /eqP->.
Qed.
Corollary free_dec P : prelat P = [::] -> WPdecidable P.
Proof. by move=> H; apply: trivial_relats_dec; rewrite /trivial_relats H. Qed.

End Trivial.


Section Rel1Unit.

Let Alph := unit.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Lemma sequnitE u : u = nseq (size u) tt.
Proof. by elim: u => [// |/= [u {1}->]]. Qed.

Theorem unit_1rel_dec P : size (prelat P) = 1 -> WPdecidable P.
Proof.
case Hrel : (prelat P) => [|[r1 r2] []] // _; move: Hrel.
rewrite (sequnitE r1); move: (size r1) => {r1} l1.
rewrite (sequnitE r2); move: (size r2) => {r2} l2.
wlog lt12 : l1 l2 P / l1 > l2.
  move=> Hdec; case: (ltngtP l1 l2) => [lt12 | lt21 | eq12] Hrel.
  - by apply: flipped_pres_dec; apply: (Hdec l2 l1) => {Hdec} //= /[!Hrel].
  - exact: (Hdec _ _ _ _ Hrel).
  - by apply: trivial_relats_dec; rewrite /trivial_relats Hrel eq12 /= eqxx.
move=> Hrel; apply: convergent_dec; apply: diamond.
  apply: (wf_f (f := size) _ wf_ltnat) => u v.
  case/rewritesP => pre suf [r1 r2] {u}-> {v}->.
  rewrite Hrel inE => /eqP[{r1}-> {r2}->] /=.
  by rewrite !size_cat ltn_add2l ltn_add2r !size_nseq.
rewrite {}Hrel => u v1 v2.
case/rewritesP => pre1 suf1 [r1 r2] /= equ1 {v1}->.
rewrite inE => /eqP[eqr {r2}->]; subst r1.
case/rewritesP => pre2 suf2 [r1 r2] /= equ2 {v2}->.
rewrite inE => /eqP[eqr {r2}->]; subst r1.
exists (pre1 ++ nseq l2 tt ++ suf1); first exact: rewrites_to_refl.
suff Hsz : size (pre2 ++ nseq l2 tt ++ suf2) = size (pre1 ++ nseq l2 tt ++ suf1).
  rewrite (sequnitE (pre2 ++ _ ++ _)) Hsz -sequnitE.
  exact: rewrites_to_refl.
apply/eqP; move: equ1; rewrite {}equ2 => /(congr1 size)/eqP.
by rewrite !size_cat ![_ + (_ + _)]addnC -!addnA !eqn_add2l.
Qed.

End Rel1Unit.


Section Monogenic.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition monogenic P : bool := size (pgen P) == 1.

Variables (P : pres Alph) (HP : monogenic P).
Lemma mono_genP : {a : Alph | (pgen P) == [:: a]}.
Proof.
move: HP; rewrite /monogenic; case: (pgen P) => [//| a [|//]] _.
by exists a.
Qed.
Definition mono_gen := val mono_genP.
Lemma mon_exE : (pgen P) = [:: mono_gen].
Proof. by rewrite /mono_gen; case: mono_genP => /= a /eqP. Qed.
Lemma monogenicP w : w \in words_of P -> w = nseq (size w) mono_gen.
Proof.
rewrite unfold_in /= mon_exE.
by elim: w => [// | w0 w IHw] /= /andP[/[!inE]/eqP {w0}-> {}/IHw <-].
Qed.

Let to_unit (u : {freemon Alph}) : {freemon unit} := nseq (size u) tt.
Let from_unit (l : {freemon unit}) : {freemon Alph} := nseq (size l) mono_gen.

Lemma to_unitK u : u \in words_of P -> from_unit (to_unit u) = u.
Proof.
by rewrite /from_unit /to_unit /= size_nseq => /monogenicP <-.
Qed.
Lemma from_unitK l : to_unit (from_unit l) = l.
Proof. by rewrite /from_unit /to_unit /= size_nseq -sequnitE. Qed.

Definition unit_relats := [seq (to_unit r.1, to_unit r.2) | r <- prelat P].
Fact all_relwords_unit_relats : all_relwords unit_relats (mem [:: tt]).
Proof.
apply/allP => /= [[r1 r2]] /= _.
by rewrite (sequnitE r1) (sequnitE r2) !all_nseq !inE eqxx !orbT.
Qed.
Definition unit_pres : pres unit :=
  Pres [:: tt] _ is_true_true all_relwords_unit_relats.

Fact to_unit_monmorphism : monmorphism to_unit.
Proof.
rewrite /to_unit; split => [// | u v].
by rewrite size_cat nseqD.
Qed.
HB.instance Definition _ :=
  isMonMorphism.Build {freemon Alph} {freemon unit}
    to_unit to_unit_monmorphism.
Fact to_unit_presmorphism : rewmorphism P unit_pres to_unit.
Proof.
move=> u v _ _ /rewritesP[pre suf [r1 r2] {u}-> {v}-> /= rin].
apply: rewrites_to1; apply/rewritesP.
exists (to_unit pre) (to_unit suf) (to_unit r1, to_unit r2) => /=.
- by rewrite /to_unit /= !size_cat !nseqD.
- by rewrite /to_unit /= !size_cat !nseqD.
exact: (map_f (fun r => (to_unit r.1, to_unit r.2)) rin).
Qed.
Fact to_unit_in_presmorphism : rewmorphism_in P unit_pres to_unit.
Proof.
by move=> u _; rewrite unfold_in /= /to_unit all_nseq !inE eqxx orbT.
Qed.
HB.instance Definition _ :=
  isPresMorphism.Build _ _ P unit_pres to_unit
    to_unit_presmorphism to_unit_in_presmorphism.


Fact from_unit_monmorphism : monmorphism from_unit.
Proof.
rewrite /from_unit; split => [// | u v].
by rewrite size_cat nseqD.
Qed.
HB.instance Definition _ :=
  isMonMorphism.Build {freemon unit} {freemon Alph} from_unit
    from_unit_monmorphism.
Fact from_unit_presmorphism : rewmorphism unit_pres P from_unit.
Proof.
move=> u v uin vin /rewritesP[pre suf [s1 s2] /= equ eqv /=].
case/mapP => /= [[r1 r2] inP /= [eqs1 eqs2]]; subst u v s1 s2.
rewrite !mmorph_cat /=; apply: rewrites_to1.
have /allP/(_ _ inP)/=/andP[r1P r2P] := wf_relat P.
rewrite !to_unitK //.
by apply/rewritesP; exists (from_unit pre) (from_unit suf) (r1, r2).
Qed.
Fact from_unit_in_presmorphism : rewmorphism_in unit_pres P from_unit.
Proof.
by move=> u _; rewrite unfold_in /= /to_unit all_nseq mon_exE !inE eqxx orbT.
Qed.
HB.instance Definition _ :=
  isPresMorphism.Build _ _ unit_pres P from_unit
    from_unit_presmorphism from_unit_in_presmorphism.

Fact to_unit_eq u :
  u \in words_of P -> from_unit (to_unit u) = u %[mod P].
Proof. by move/to_unitK ->; exact: equiv_refl. Qed.
Fact from_unit_eq l :
  to_unit (from_unit l) = l %[mod unit_pres].
Proof. by rewrite from_unitK; exact: equiv_refl. Qed.
Definition monogenic_isopres_unit : isopres P unit_pres :=
  IsoPres (fun a b => to_unit_eq b) (fun _ _ => from_unit_eq _).

Theorem monogenic_1rel_dec :
  (* TODO: remove this assumption *) size (prelat P) = 1 -> WPdecidable P.
Proof.
move=> Hsz; apply: (isopres_dec monogenic_isopres_unit).
apply: unit_1rel_dec; rewrite -{}Hsz.
by rewrite /= /unit_relats size_map.
Qed.

(* This should be provable by reducing to the 1 relation case but is not
   needed for the database. On can reduce 2 relations to 1 relations :

     < a | u1 = v1, u2 = v2 >

  where ui >= vi reduces to

     < a | gcd(u1 - v1, u2 - v2) + min(v1, v2) = min(v1, v2) >

  Iteratively reducing the first two relations prove that

     < a | gcd(ui - vi | i = 1..n) + min(vi) = min(vi) >

*)
(*
Theorem monogenic_dec P : monogenic P -> WPdecidable P.
*)

End Monogenic.


Section FreeProductMonogenicFree.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition free_product_monogenic_free P :=
  size (undup (flatten (relwords P))) == 1.

Theorem free_product_monogenic_free_1rel_dec P :
  (* TODO: remove this assumption *) size (prelat P) = 1 ->
  free_product_monogenic_free P -> WPdecidable P.
Proof.
rewrite /free_product_monogenic_free => rel1.
case Hgs : (undup (flatten (relwords P))) => [//|g [|//]] _.
have gsrel : all_relwords P (mem [:: g]).
  apply/allP => /= -[r1 r2] /= /mem_relwords.
  suff rnseq r : r \in relwords P -> exists n, r = nseq n g.
    case/andP => /rnseq [n1] {r1}-> /rnseq [n2] {r2}->.
    by rewrite !all_nseq !inE eqxx !orbT.
  move=> H; exists (size r).
  apply/all_pred1P/allP => x xinr /=.
  suff : x \in [:: g] by rewrite inE => ->.
  by rewrite -Hgs mem_undup; apply/flattenP => /=; exists r.
pose Q := Pres [:: g] _ is_true_true gsrel.
apply: (eqrelat_dec (P1 := Q)) => //.
exact: monogenic_1rel_dec.
Qed.

End FreeProductMonogenicFree.


Section CycleFree.

Context {Alph : choiceType}.
Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition left_cycle_free_1rel P : Prop :=
  exists (a b : Alph) (u v : word Alph),
      a != b /\ prelat P = [:: (a :: u, b :: v)].
Definition is_left_cycle_free_1rel P : bool :=
  if (prelat P) is [:: (a :: u, b :: v)] then a != b else false.

Definition right_cyclic_1rel P : Prop :=
  exists (a : Alph) (u v : word Alph),
    prelat P = [:: (rcons u a, rcons v a)].
Definition is_right_cyclic_1rel P : bool :=
  if (prelat P) is [:: (u, v)] then
    if rev u is a :: u' then
      if rev v is b :: v' then a == b else false
    else false
  else false.


Definition cycle_free_1rel P :=
  left_cycle_free_1rel P /\ left_cycle_free_1rel (dual_pres P).
Definition is_cycle_free_1rel P :=
  (is_left_cycle_free_1rel P) && (is_left_cycle_free_1rel (dual_pres P)).

Lemma is_left_cycle_free_1relP P :
  reflect (left_cycle_free_1rel P) (is_left_cycle_free_1rel P).
Proof.
rewrite /is_left_cycle_free_1rel /left_cycle_free_1rel.
case Hrel: (prelat P) => [|r1 l] //=.
  by apply (iffP idP) => [|[a][b][u][v][_]] //.
apply (iffP idP); case: r1 {Hrel} => [[|a u][|b v]] //;
  first 1 [move] || by move=> [a'][b'][u'][v'][neqab] // [-> _ -> _ ->].
by case: l => // neqab; exists a; exists b; exists u; exists v.
Qed.

Lemma is_right_cyclic_1relP P :
  reflect (right_cyclic_1rel P) (is_right_cyclic_1rel P).
Proof.
rewrite /is_right_cyclic_1rel /right_cyclic_1rel.
case Hrel: (prelat P) => [|r1 l] //=.
  by apply (iffP idP) => [|[a][b][_]] //.
apply (iffP idP); case: r1 {Hrel} => [u v]; case: l => //; last first.
- by move=> p l [a][u'][v'].
- by move=> [a][u'][v'][{u}->{v}->]; rewrite !rev_rcons eqxx.
case/lastP: u => // u a; rewrite rev_rcons.
case/lastP: v => // v b; rewrite rev_rcons => /eqP {b}<-.
by exists a; exists u; exists v.
Qed.

Lemma is_cycle_free_1relP P :
  reflect (cycle_free_1rel P) (is_cycle_free_1rel P).
Proof.
rewrite /cycle_free_1rel.
by apply (iffP andP) => -[]/is_left_cycle_free_1relP H1 /is_left_cycle_free_1relP H2.
Qed.


(* Theorem 2.6 in Carl-Fredrik Nyberg-Brodda1,
   The word problem for one-relation monoids: a survey *)
Theorem cycle_free_1rel_dec P : cycle_free_1rel P -> WPdecidable P.
Admitted.

Theorem is_cycle_free_1rel_dec P : is_cycle_free_1rel P -> WPdecidable P.
Proof. move/is_cycle_free_1relP; exact: cycle_free_1rel_dec. Qed.

End CycleFree.


Section NbOcc.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Definition two_letters P : bool := size (pgen P) == 2.

Definition same_number_of_occ P a :=
  forall r, r \in prelat P ->
                 count_mem a r.1 > 0 /\ count_mem a r.1 = count_mem a r.2.
Definition has_same_number_of_occ P a :=
  all (fun r => (count_mem a r.1 > 0) && (count_mem a r.1 == count_mem a r.2))
    (prelat P).
Lemma has_same_number_of_occP P a :
  reflect (same_number_of_occ P a) (has_same_number_of_occ P a).
Proof.
rewrite /has_same_number_of_occ /same_number_of_occ.
by apply (iffP allP) => /= H r {}/H => [/andP[-> /eqP ->]// | [-> /= ->]].
Qed.

(* Theorem 4.9 in Carl-Fredrik Nyberg-Brodda1,
   The word problem for one-relation monoids: a survey *)
Theorem left_cycle_free_1rel_same_number_occ_dec P a :
  right_cyclic_1rel P -> left_cycle_free_1rel P -> same_number_of_occ P a ->
  WPdecidable P.
Admitted.

Corollary check_same_number_occ_dec P a :
  is_right_cyclic_1rel P -> is_left_cycle_free_1rel P ->
  has_same_number_of_occ P a ->
  WPdecidable P.
Proof.
move=> /is_right_cyclic_1relP H1 /is_left_cycle_free_1relP H2
         /has_same_number_of_occP.
exact: left_cycle_free_1rel_same_number_occ_dec.
Qed.

End NbOcc.


Section SmallOverlap.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).
Implicit Type (R : seq (word Alph)).

Variant piece R u : Prop :=
  | PieceEmpty : u = [::] -> piece R u
  | PieceSameWord :
    forall p1 q1 p2 q2,
      p1 != p2 ->
      p1 ++ u ++ q1 = p2 ++ u ++ q2 ->
      p1 ++ u ++ q1 \in R -> piece R u
  | PieceDiffWords :
    forall w1 w2,
      w1 != w2   ->
      w1 \in R   -> w2 \in R ->
      infix u w1 -> infix u w2 -> piece R u.

Definition pieces R :=
  let inf := flatten [seq non_empty_infixes w | w <- R]
  in [::] :: [seq w <- undup inf | count_mem w inf >= 2].

Lemma infix_piece R u v : infix v u -> piece R u -> piece R v.
Proof.
move=> infvu [unil | /= p1 q1 p2 q2 neqp12 puq inR |].
- move: infvu; rewrite {}unil infixs0 => /eqP->; exact: PieceEmpty.
- case/infixP: infvu => [a][b] equ.
  have assoc5 p q : p ++ a ++ v ++ b ++ q = p ++ u ++ q by rewrite equ !catA.
  apply: (@PieceSameWord _ v (p1 ++ a) (b ++ q1) (p2 ++ a) (b ++ q2)).
  + by apply/contra: neqp12 => /eqP/catr_inj ->.
  + by rewrite -!catA !assoc5.
  + by rewrite -!catA assoc5.
- move=>  w1 w2 neqw12 w1R w2R infw1 infw2.
  by apply (@PieceDiffWords _ _ w1 w2) => //; exact: (infix_trans infvu).
Qed.

Lemma piece_cons r R u : piece R u -> piece (r :: R) u.
Proof.
move=> [ueq0 | /= p1 q1 p2 q2 u1 nep12 inR | w1 w2 new12 w1R w2R inf1 inf2].
- exact: PieceEmpty.
- by apply: (@PieceSameWord _ u p1 q1 p2 q2) => //; rewrite inE inR orbT.
- by apply: (@PieceDiffWords _ u w1 w2) => //; rewrite inE orbC ?w1R ?w2R.
Qed.

Lemma mem_piecesE R u :
  (u \in pieces R) =
    (u == [::]) ||
      (count_mem u (flatten [seq non_empty_infixes w | w <- R]) >= 2).
Proof.
rewrite inE mem_filter mem_undup.
by case: ltnP => //= /ltnW; rewrite -has_count has_pred1 => ->.
Qed.

Lemma uniq_piecesP R u : uniq R -> reflect (piece R u) (u \in pieces R).
Proof.
case: (altP (u =P [::])) => [-> _ | /negbTE uneq0].
  by rewrite inE eqxx /=; apply: Bool.ReflectT; exact: PieceEmpty.
rewrite mem_piecesE /=; elim: R => [_ | /= r R IHR].
  by rewrite uneq0; apply (iffP idP) => // -[] // /eqP; rewrite  uneq0.
case/andP => rnotin {}/IHR IHR.
rewrite count_cat; case Cne: (count_mem u (non_empty_infixes r)) => [|[|n]].
- rewrite add0n; apply (iffP idP) => [{}/IHR | Hpieces].
    exact: piece_cons.
  apply/IHR => {IHR}.
  have {}Cne : ~~ infix u r.
    by move/count_memPn: Cne; rewrite -non_empty_infixesP uneq0 /=.
  case: Hpieces => [/eqP | /= p1 q1 p2 q2 u1 nep12 inR |]; first by rewrite uneq0.
    apply: (@PieceSameWord _ u p1 q1 p2 q2) => //.
    move: inR; rewrite inE => /orP[/eqP Habs |//].
    by exfalso; apply: (negP Cne); apply/infixP; exists p1; exists q1.
  move=> w1 w2 new12 w1R w2R inf1 inf2.
  suff step w : w \in r :: R -> infix u w -> w \in R.
    by apply: (@PieceDiffWords _ u w1 w2) => //; apply: step.
  rewrite inE => /orP[/eqP {w}-> |//].
  by rewrite (negbTE Cne).
- have infur : infix u r.
    have {Cne} : count_mem u (non_empty_infixes r) > 0 by rewrite Cne.
    rewrite -has_count => /hasP[/= v].
    by rewrite -non_empty_infixesP => /andP[_ infvr /eqP <-].
  rewrite {IHR} add1n ltnS -has_count uneq0.
  apply (iffP hasP) => /= [[v /[swap]/eqP {v}->] |].
    case/flatten_mapP => /= v vinR.
    rewrite -non_empty_infixesP uneq0 /= => infuv.
    apply: (@PieceDiffWords _ u v r) => //.
    + by move: rnotin; apply contra => /eqP <-.
    + by rewrite inE vinR orbT.
    + by rewrite inE eqxx.
  case=> [/eqP | /= p1 q1 p2 q2 nep12 equ12 inR | ]; first by rewrite uneq0.
    exists u => //; apply/flatten_mapP => /=.
    move: inR; rewrite inE => /orP[/eqP eqr| inR]; first last.
      exists (p1 ++ u ++ q1) => //.
      rewrite -non_empty_infixesP uneq0 /=.
      by apply/infixP; exists p1; exists q1.
    exfalso; suff : count_mem u (non_empty_infixes r) >= 2 by rewrite Cne.
    rewrite count_mem_non_empty_infixesE => //=.
    have <- : size [:: (p1, u, q1); (p2, u, q2)] = 2 by [].
    rewrite -size_filter; apply: uniq_leq_size => //=.
      by rewrite andbT inE !xpair_eqE (negbTE nep12).
    by move=> [[a b] c] /[!inE]/orP[]/eqP[{a}->{b}->{c}->];
      rewrite mem_filter /= eqxx /= mem_cut3 uneq0 /= -?equ12 eqr.
  move=> w1 w2 neqw12 w1in w2in infuw1 infuw2.
  exists u => //; apply/flatten_mapP => /=.
  move: w1in; rewrite inE orbC => /orP[w1in | /eqP eqw1r].
    by exists w1 => //; rewrite -non_empty_infixesP uneq0 infuw1.
  move: w2in; rewrite inE orbC => /orP[w2in | /eqP eqw2r].
    by exists w2 => //; rewrite -non_empty_infixesP uneq0 infuw2.
  by exfalso; move: neqw12; rewrite eqw1r eqw2r eqxx.
rewrite uneq0 /= !addSn ltnS; apply (iffP idP) => [{IHR} _ | //].
move: Cne; rewrite count_mem_non_empty_infixesE /=.
rewrite -size_filter; case Hfilter : (filter _ _) => [|t0[|t1 f]] // _.
have : t0 != t1.
  have: uniq [:: t0, t1 & f] by rewrite -Hfilter; apply/filter_uniq/cut3_uniq.
  by rewrite /= inE negb_or => /andP[/andP[]].
have : t0 \in [:: t0, t1 & f] by rewrite inE eqxx.
rewrite -Hfilter mem_filter /= => /andP[/eqP].
have : t1 \in [:: t0, t1 & f] by rewrite !inE eqxx orbT.
rewrite -{f}Hfilter mem_filter /= => /andP[/eqP].
case: t0 t1 => [[a0 b0] c0][[a1 b1] c1] /= {b1}-> /[swap] {b0}->.
rewrite !mem_cut3 !uneq0 /= => /eqP eqr1 /eqP eqr0 neq01.
rewrite -eqr1 in eqr0.
have:= eqr0 => /PieceSameWord; apply; first last.
- by rewrite eqr0 -eqr1 inE eqxx.
- apply/contra: neq01 => /eqP a01; subst a1.
  by move: eqr0 => /catl_inj/catl_inj <-.
Qed.

Lemma piecesP P u :
  reflect (piece (undup (relwords P)) u) (u \in pieces (undup (relwords P))).
Proof. exact/uniq_piecesP/undup_uniq. Qed.
Lemma infix_pieces P u v : infix v u ->
  u \in pieces (undup (relwords P)) -> v \in pieces (undup (relwords P)).
Proof. by move/infix_piece => Hinf /piecesP/Hinf/piecesP. Qed.


Definition small_overlap (n : nat) P :=
  let rw := undup (relwords P) in
  forall u, u \in rw ->
     forall f : seq (word Alph),
     (forall w, w \in f -> piece rw w) ->
       u = flatten f -> size f >= n.

Lemma small_overlapW P n1 n2 :
  n1 >= n2 -> small_overlap n1 P -> small_overlap n2 P.
Proof.
by rewrite /small_overlap => /= leqn12 Hso u /[swap] f
                               {}/Hso/[apply]/[apply]/(leq_trans leqn12).
Qed.

Definition check_small_overlap n P facts :=
  let rw := undup (relwords P) in
  let p := pieces rw in
  if has (fun f => size f < n) facts then false
  else if size rw != size facts then false
  else all (fun pair_w_f => is_greedy_factorisation (mem p) pair_w_f.1 pair_w_f.2)
           (zip rw facts).

Lemma check_small_overlapP n P (facts : seq (seq (word Alph))) :
  check_small_overlap n P facts -> small_overlap n P.
Proof.
rewrite /check_small_overlap /small_overlap /=.
case: (boolP (has _ facts)) => //; rewrite -all_predC => /allP /= allfacts.
have := undup_uniq (relwords P).
have := infix_pieces (P := P).
have := piecesP P.
case: eqP => //= /eqP; rewrite eqn_leq => /andP[/unzip1_zip + /unzip2_zip].
move: (zip _ _) => pairs <- eqfacts piecesP infix_pairs pairs1_uniq /allP /= allzip.
subst facts.
move=> u /mapP[/= [v fact]/[dup]/allzip/=/is_greedy_min_size Hmin inpairs {u}->].
have /allfacts : fact \in unzip2 pairs by apply/mapP => /=; exists (v, fact).
rewrite -leqNgt => szfact f Hpiece /esym /(Hmin infix_pairs) lesz.
have {}/lesz : all (mem (pieces (unzip1 pairs))) f.
  by apply/allP => /= u /Hpiece /piecesP.
by move/(leq_trans _ ); apply.
Qed.

(* Mark Kambites "Small overlap monoids I: The word problem"
Journal of Algebra Volume 321, Issue 8, 15 April 2009, Pages 2187-2205
Theorem 1

And

John Hermann Remmers. Some Algorithmic Problems for Semigroups: A Geometric Approach.
PhD thesis, University of Michigan, USA, 1971. AAI7123856.
 *)
Theorem c3_monoid_dec P : small_overlap 3 P -> WPdecidable P.
Admitted.

Corollary check_c3_monoid_dec P facts :
  check_small_overlap 3 P facts -> WPdecidable P.
Proof. by move/check_small_overlapP/c3_monoid_dec. Qed.

End SmallOverlap.


Section Watier.

Context {Alph : choiceType}.

Implicit Type (u v w : word Alph).
Implicit Type (P : pres Alph).

Variant isWatier P :=
  | IsWatier : forall (a b : Alph) (u v : word Alph) (k : nat),
      a != b -> pgen P = [:: a; b] ->
      prelat P = [:: (nseq k b ++ a :: u, a :: v)] ->
      ~~ infix (nseq k b) u -> isWatier P.
Definition check_Watier P (a b : Alph) (u v : word Alph) (k : nat) :=
  [&& a != b, pgen P == [:: a; b],
    prelat P == [:: (nseq k b ++ a :: u, a :: v)] &
      ~~ infix (nseq k b) u].
Lemma check_WatierP P a b u v k : check_Watier P a b u v k -> isWatier P.
Proof. by case/and4P => H1 /eqP H2 /eqP H3 H4; exists a b u v k. Qed.

(* Theorem 4.10 in Carl-Fredrik Nyberg-Brodda1,
   The word problem for one-relation monoids: a survey *)
Theorem is_Watier_dec P : isWatier P -> WPdecidable P.
Admitted.
Corollary check_Watier_dec P a b u v k : check_Watier P a b u v k -> WPdecidable P.
Proof. move/check_WatierP; exact: is_Watier_dec. Qed.

End Watier.


Module Examples.
Section Examples.

Definition testWatier :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].

Lemma testWatierP : isWatier testWatier.
Proof. by exists 0 1 [:: 1; 1; 0] [::] 3. Qed.

Definition AB_AAAB_A :=
  make_pres [:: 0; 1] [:: ([:: 1; 1; 1; 0; 1; 1; 0], [:: 0])].
Lemma AB_AAAB_A_dec : WPdecidable AB_AAAB_A.
Proof. exact: (@check_Watier_dec _ _ 0 1 [:: 1; 1; 0] [::] 3). Qed.

Definition A_AAA_A := make_pres [:: 0] [:: ([:: 0; 0; 0], [:: 0])].
Lemma A_AAA_A_dec : WPdecidable A_AAA_A.
Proof. exact: monogenic_1rel_dec. Qed.

Definition AB_BBABAAAA_ABBBBAAABA :=
  make_pres [:: 0;1]
    [:: ([:: 1;1;0;1;0;0;0;0], [:: 0;1;1;1;1;0;0;0;1;0])].
Lemma AB_BBABAAAA_ABBBBAAABA_dec : WPdecidable AB_BBABAAAA_ABBBBAAABA.
Proof. exact: (check_same_number_occ_dec (a := 0)). Qed.

Definition AB_BAAAABBAAA_ABBBAABA :=
  make_pres [:: 0; 1]
       [:: ([:: 1; 0; 0; 0; 0; 1; 1; 0; 0; 0], [:: 0; 1; 1; 1; 0; 0; 1; 0]) ].
Lemma AB_BAAAABBAAA_ABBBAABA_dec : WPdecidable AB_BAAAABBAAA_ABBBAABA.
Proof. exact: (check_c3_monoid_dec (facts := [::
                     [:: [:: 1; 0; 0; 0]; [:: 0; 1; 1]; [:: 0; 0; 0] ];
                     [:: [:: 0; 1; 1]; [:: 1; 0; 0]; [:: 1; 0] ]
                  ])).
Qed.

End Examples.
End Examples.

