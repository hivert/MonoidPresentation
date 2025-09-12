(** * The Short-Lexicographic order on words *)
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
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.


Require Import well_founded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Order.TTheory.
Import Order.LexiSyntax.


Fact sizelexidisplay : Order.disp_t. Proof. exact: Order.Disp tt tt. Qed.

Section SizeLexi.

Context {d : Order.disp_t} {T : orderType d}.
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
Context {disp : Order.disp_t} {T : orderType disp}.
Implicit Types (u v w : seq T).

Hypothesis Twf : well_founded (@Order.lt _ T).

Lemma sizelexi_wf : well_founded (@Order.lt _ (seq T)).
Proof.
pose ltb b u v := ((size v <= b) && (u < v)%O).
suff bwf bnd : well_founded (ltb bnd).
  move=> u; have [n] := ubnPleq (size u).
  elim/(well_founded_induction (bwf n)): u => u IHu szu.
  apply: Acc_intro => y ltyu; apply: IHu; first by rewrite /ltb szu ltyu.
  exact (leq_trans (size_le_sizelexi (ltW ltyu)) szu).
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

Lemma sizelexi_nat_wf : well_founded (@Order.lt _ (seq nat)).
Proof. exact: sizelexi_wf wf_ltnat. Qed.
