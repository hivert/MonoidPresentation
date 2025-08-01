(** * Example of monoid and presentations : the free commutative monoid *)
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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice bigop fintype finfun finset ssralg tuple.
From mathcomp Require Import order.

Require Import monoids present enumnf monpres sizelexi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.SeqLexiSyntax.


Section FreeComoidPres.

Variable n : nat.

Definition comrel m :=
  [seq ([:: i; j], [:: j; i]) | i <- iota 0 m, j <- iota 0 i].

Lemma mem_comrelP m p :
  reflect (exists i j, j < i < m /\ p = ([:: i; j], [:: j; i]))
          (p \in comrel m).
Proof.
apply (iffP allpairsPdep) => /= -[i][j][].
  rewrite !mem_iota !add0n /= => ltim ltji {p}->.
  by exists i; exists j; rewrite ltji.
case/andP => ltji ltim {p}->.
by exists i; exists j; rewrite !mem_iota !add0n.
Qed.
Lemma mem_comrelE i j : (([:: i; j], [:: j; i]) \in comrel n) = (j < i < n).
Proof.
apply/mem_comrelP/idP => [[i0][j0] [lt] [-> ->] | lt] //.
by exists i; exists j.
Qed.

Lemma subset_comrel m : {subset comrel m <= comrel m.+1}.
Proof.
move=> /= [a b] /mem_comrelP [i][j] [/andP[ltim /ltnW leij]] [{a}-> {b}->].
by apply/mem_comrelP; exists i; exists j; rewrite ltim.
Qed.

Lemma all_relwords_comrel : all_relwords (comrel n) (mem (iota 0 n)).
Proof.
apply/all_allpairsP => [/= i j /=].
rewrite !mem_iota !add0n /= => /[dup] + ->.
by move=> /(ltn_trans _)/[apply] ->.
Qed.
Definition FCM_pres : pres nat :=
  Pres (iota 0 n) (comrel n) (iota_uniq 0 n) all_relwords_comrel.

Lemma mem_words_FCM_presP u :
  reflect  {in u, forall i, i < n} (u \in words_of FCM_pres).
Proof. by apply (iffP allP) => /= /[swap] i /[apply]; rewrite mem_iota. Qed.

Lemma FCM_pres_decreassing : decreasing (Order.lt (s := seq nat)) FCM_pres.
Proof.
apply/allP=> /= -[u v] /mem_comrelP[i][j][/andP[ltji ltin]][{u}-> {v}->] /=.
by rewrite lt_sizelexiE /= /Order.lt /= leEnat (ltnW ltji) /= leqNgt ltji.
Qed.

Theorem FCM_pres_convergent : convergent FCM_pres.
Proof.
apply: diamond.
  exact: (decreasing_wf lt_sizelexi_stable sizelexi_nat_wf FCM_pres_decreassing).
apply: nspair_confluence => u v [pre mid suf].
  case=> [lr rr][lm rm] /=.
  case/mem_comrelP => [i][j][/andP[ltji ltin]][{lr}->{rr}->].
  case/mem_comrelP => [k][l][/andP[ltlk ltkn]][{lm}->{rm}->].
  move=> /[swap] {mid}<- /[dup] /(congr1 size).
  rewrite /= size_cat /= !addnS => [][]/esym/eqP.
  rewrite addn_eq0 => /andP[/nilP {pre}-> /nilP {suf}->].
  rewrite !cat0s => [[]{i ltji ltin}-> {j}->] {u}-> {v}->.
  by exists [:: l; k]; apply rewrites_to_refl.
case=> [l1 r1][l2 r2] /=.
case/mem_comrelP => [i][j][/andP[ltji ltin]][{l1}->{r1}->].
case/mem_comrelP => [k][l][/andP[ltlk ltkn]][{l2}->{r2}->].
case: mid => [|m0 [|m1 m]]//= _; first last.
  move=> /[dup]/(congr1 size) => /=; rewrite size_cat /= !addnS => /esym[] /eqP.
  rewrite addn_eq0 => /andP[/nilP {pre}-> /nilP {m}->].
  rewrite !cat0s => [[{m0}<-{m1}<-]][{i ltji ltin}<-{j}<-] <-{suf}{u}->{v}->.
  by exists [:: l; k]; apply rewrites_to_refl.
case: pre => [|p0 [|p1 []]]//= [{p0}<-{m0}<-].
case: suf => [|s0 [|s1]]//= [eqkj {s0}<-] {u}-> {v}->; subst k.
exists [:: l; j; i].
- exists [:: [:: j; l; i]; [:: l; j; i]] => //.
  repeat (apply/andP; split) => //; apply/rewritesP.
  + exists [:: j] [::] ([:: i; l], [:: l; i]) => //.
    by rewrite mem_comrelE (ltn_trans ltlk ltji).
  + exists [::] [:: i] ([:: j; l], [:: l; j]) => //.
    by rewrite mem_comrelE ltlk ltkn.
- exists [:: [:: l; i; j]; [:: l; j; i]] => //.
  + repeat (apply/andP; split) => //; apply/rewritesP.
    exists [::] [:: j] ([:: i; l], [:: l; i]) => //.
    by rewrite mem_comrelE (ltn_trans ltlk ltji).
  + exists [:: l] [::] ([:: i; j], [:: j; i]) => //.
    by rewrite mem_comrelE ltji ltin.
Qed.

Theorem FCM_pres_normalE u :
  u \in words_of FCM_pres -> normal FCM_pres u = sorted leq u.
Proof.
move=> uin; apply/idP/idP.
  move/mem_words_FCM_presP: uin.
  case: u => [|u0 u] //=; elim: u u0 => //= u1 u IHu u0 uin /[dup].
  move/(infix_normal (infix_drop _ 1)) => /= {}/IHu ->; first last.
    by move=> i iin; apply uin; move: iin; rewrite !inE => -> /[!orbT].
  move/(infix_normal (infix_take _ 2)) => /=.
  rewrite andbT take0 leqNgt; apply contraL => ltu10.
  apply/negP; rewrite /normal => /eqP Hnor.
  suff {Hnor} : [:: u1; u0] \in rewrites (comrel n) [:: u0; u1] by rewrite Hnor.
  apply/rewritesP; exists [::] [::] ([:: u0; u1], [:: u1; u0]) => //.
  rewrite mem_comrelE {}ltu10 /=.
  by apply uin; rewrite inE eqxx.
rewrite {uin} /normal; apply: contraLR.
case Hrew : rewrites => [//|v l] _.
have {Hrew} : v \in rewrites FCM_pres u by rewrite Hrew inE eqxx.
case/rewritesP => pre suf [r1 r2] /= {u}-> _.
move/mem_comrelP => [i][j][] /andP[ltij _][{r1 r2}-> _] /=.
apply/negP => /cat_sorted2[_]/=.
by rewrite leqNgt ltij.
Qed.

Lemma FCM_equiv_perm u v : u = v %[mod FCM_pres] -> perm_eq u v.
Proof.
move: u v; apply: equiv_min => [[u v] /= |].
  move/mem_comrelP => [i][j][] /andP[ltij _][{u}->{v}->].
  by rewrite /perm_eq /= !eqxx !addn0 /= [j == i]eq_sym; case: (i == j).
split => [| u v w | pre u v suf | u v].
- exact: perm_refl.
- by move/perm_trans; apply.
- by rewrite perm_cat2l perm_cat2r.
- by rewrite perm_sym.
Qed.

Lemma FCM_normal_of u :
  u \in words_of FCM_pres -> normal_of FCM_pres_convergent.2 u = sort leq u.
Proof.
move=> uin.
have equ := equiv_normal_of FCM_pres_convergent.2 u.
have:= uin; rewrite (equiv_words_ofE equ) => vin.
move/FCM_equiv_perm: equ; rewrite perm_sym => Hperm.
apply: (sorted_eq leq_trans anti_leq).
- by rewrite -FCM_pres_normalE => //; apply: normal_ofP.
- by exact/sort_sorted/leq_total.
by apply: (perm_trans Hperm); rewrite perm_sym perm_sort perm_refl.
Qed.

Lemma perm_equiv_FCM u v :
  u \in words_of FCM_pres -> perm_eq u v -> u = v %[mod FCM_pres].
Proof.
rewrite (@equiv_normal_ofE _ _ FCM_pres_convergent) => uin Hperm.
have vin : v \in words_of FCM_pres.
  by move: uin; rewrite !unfold_in /= (perm_all _ Hperm).
rewrite !FCM_normal_of //.
exact/(perm_sortP leq_total leq_trans anti_leq).
Qed.

End FreeComoidPres.


Section TNthZipTuple.

Variables (n : nat) (T : Type).
Implicit Type t : n.-tuple T.

Lemma tnth_zip t1 t2 i :
  tnth [tuple of zip t1 t2] i = (tnth t1 i, tnth t2 i).
Proof.
case: n t1 t2 i => [|m] t1 t2 i; first by case: i.
case: t1 t2 => [[|h1 v1] sv1]// [[|h2 v2] sv2] //.
by rewrite (tnth_nth (h1, h2)) nth_zip ?size_tuple // (tnth_nth h1) (tnth_nth h2).
Qed.

End TNthZipTuple.


Section FreeCommutativeMonoidTuple.

Variable n : nat.

Definition FCMT := n.-tuple nat.
Local Notation FCMTP := (FCM_pres n).

Implicit Types (x y z : FCMT).

Let FCMT1 : FCMT := [tuple 0%N  | _ < n].
Let FCMTmul x y : FCMT := [tuple of map (fun p => p.1 + p.2)%N (zip x y)].

Fact FCMTmulA : associative FCMTmul.
Proof.
move => x y z; apply: eq_from_tnth => i /=.
by rewrite !(tnth_map, tnth_zip) /= addnA.
Qed.
Fact FCMTmulC : commutative FCMTmul.
Proof.
move => x y; apply: eq_from_tnth => i /=.
by rewrite !(tnth_map, tnth_zip) /= addnC.
Qed.
Fact FCMTmul1m : left_id FCMT1 FCMTmul.
Proof.
move => x; apply: eq_from_tnth => i /=.
by rewrite !(tnth_map, tnth_zip).
Qed.

HB.instance Definition _ := Countable.on FCMT.
HB.instance Definition _ := isComMonoid.Build FCMT FCMTmulA FCMTmulC FCMTmul1m.

Lemma tnth1 i : tnth (1%M%M : FCMT) i = 0%N.
Proof. by rewrite tnth_mktuple. Qed.
Lemma tnthM x y i : tnth (x * y)%M i = tnth x i + tnth y i.
Proof. by rewrite tnth_map tnth_zip. Qed.
Lemma tnth_morph i :
  {morph (fun m : FCMT => tnth m i) : x y / (x * y)%M >-> x + y}.
Proof. by move=> x y; rewrite tnthM. Qed.
Lemma tnth_prod [I : Type] (s : seq I) [P : pred I] [F : I -> FCMT] i :
  tnth (\prod_(x <- s | P x) F x)%M i = (\sum_(x <- s | P x) tnth (F x) i)%N.
Proof. by apply: (big_morph _ (tnth_morph i)); rewrite tnth1. Qed.
Lemma tnthX x k i : tnth (x ^+ k)%M i = (tnth x i * k)%N.
Proof.
elim: k => [|k IHk]; first by rewrite expm0 tnth1 muln0.
by rewrite expmS tnthM mulnS IHk.
Qed.


Let FCMT_mgen (i : nat) : FCMT := [tuple j == i :> nat : nat  | j < n].

Lemma FCMT_morE w :
  univmor FCMT_mgen w = [tuple count_mem (\val i) (w : seq nat)  | i < n].
Proof.
elim: w => /= [| w0 w IHw]; first by rewrite univmor_nil.
apply eq_from_tnth => i.
rewrite univmor_cons !(tnth_map, tnth_zip) /= IHw.
by rewrite !tnth_mktuple tnth_ord_tuple eq_sym.
Qed.

Lemma equiv_comrel_rem m (w : word nat) :
  m \in w -> {in w, forall i : nat, i < m.+1} ->
      w = m :: (rem m w) %[mod comrel m.+1].
Proof.
rewrite remE -index_mem.
move: {2 3 4 5}(index m w) (erefl (index m w)) => i Hind Hsz.
elim: i w Hsz Hind => [| i IHi] w.
  rewrite take0 cat0s => + /eqP + _.
  rewrite -leqn0 -[_ <= 0]ltnS => /in_take_leq <-.
  rewrite -{2}(cat_take_drop 1 w).
  case: w => [| w0 w] //=; rewrite take0 drop0 cat0s inE => /eqP->.
  exact: equiv_refl.
case: w => [// | w0 w] /= {}/IHi Hrec.
case: eqP => // /eqP neqw0m []{}/Hrec Hrec Hin.
have ltw0m : w0 < m.+1.
  have /Hin : w0 \in w0 :: w by rewrite inE eqxx.
  by rewrite ltnS leq_eqVlt (negbTE neqw0m).
have {}/Hrec eqw : {in w, forall i : nat, i < m.+1}.
  by move=> j jinw; apply: Hin; rewrite inE jinw orbT.
move/(equiv_stable (R := comrel m.+1) [:: w0] [::]): eqw.
rewrite !cat1s !cats0 => /equiv_trans; apply.
move: (_ ++ _) => suf {i}; apply: rewrites_to1; apply/rewritesP;
exists [::] suf ([:: w0; m], [:: m; w0]); try by rewrite cat0s.
rewrite mem_undirected; apply/orP.
move: neqw0m; rewrite neq_ltn => /orP[] lt; [right|left].
- apply/allpairsPdep; exists m; exists w0.
  by split => //; rewrite !mem_iota /= add0n.
- apply/allpairsPdep; exists w0; exists m.
  by split => //; rewrite !mem_iota /= add0n.
Qed.

Fact FCMT_mgenP (m : FCMT) :
  exists2 w, w \in words_of FCMTP & univmor FCMT_mgen w = m.
Proof.
have tnth_nseq k (i : 'I_n) (j : nat) :
    tnth (univmor FCMT_mgen (nseq k j)) i = ((i == j :> nat) * k)%N.
  by rewrite univmor_nseq tnthX tnth_mktuple.
exists (flatten [seq nseq (nth 0 m i) i | i <- iota 0 n]).
  by apply/allP=> i /flatten_mapP[/= j] iin /nseqP[-> _].
rewrite flatten_prodE big_map mmorph_prod /=.
apply: eq_from_tnth => i; rewrite tnth_prod.
have iin : \val i \in iota 0 n by rewrite mem_iota /= add0n ltn_ord.
rewrite (bigD1_seq (\val i) iin) /= ?iota_uniq //.
rewrite big1 ?addn0 => [|j /negbTE neqij]; first last.
  by rewrite tnth_nseq eq_sym neqij mul0n.
by rewrite tnth_nseq eqxx mul1n -tnth_nth.
Qed.
Fact FCMT_mgen_eq (u v : seq nat) :
  u \in words_of FCMTP -> v \in words_of FCMTP ->
  (u = v %[mod FCMTP] <-> univmor FCMT_mgen u = univmor FCMT_mgen v).
Proof.
rewrite !FCMT_morE => uin vin; split=> [equv|].
  move: u v equv {uin vin}; apply: equiv_min => /= [[]|].
    rewrite /comrel => /= u v /allpairsPdep[i][j].
    rewrite !mem_iota /= add0n => -[_ _][{u}-> {v}->] /=.
    by apply eq_from_tnth => k; rewrite !tnth_mktuple !addn0 addnC.
  split=> [// | u v w -> -> //| pre u v suf Heq | u v -> //].
  apply eq_from_tnth => k; move/(congr1 (fun t => tnth t k)): Heq.
  by rewrite !tnth_mktuple !count_cat => ->.
move: uin vin => /mem_words_FCM_presP uin /mem_words_FCM_presP vin.
move=> Heq; have {}Heq (i : nat) : count_mem i u = count_mem i v.
case: (ltnP i n) => [ltin | leni] /=.
- move/(congr1 (fun t => tnth t (Ordinal ltin))): Heq.
  by rewrite !tnth_mktuple.
- suff wcnt w : {in w, forall i : nat, i < n} -> count_mem i w = 0.
    by rewrite !wcnt.
  by move=> Hin; apply/count_memPn/negP => /Hin; rewrite ltnNge leni.
rewrite /FCM_pres /=.
elim : n u v uin vin Heq => [|m IHm] u v.
  case: u v => [|u0 u] v; first last.
    by move=> H; have /H : u0 \in u0 :: u by rewrite inE eqxx.
  case: v => [|v0 v _]; first last.
    by move=> H; have /H : v0 \in v0 :: v by rewrite inE eqxx.
  by move=> _ _ _; apply: equiv_refl.
move Hc : (count_mem m u) => c.
elim: c u v Hc => [| c IHc {IHm}] u v Hc uin vin eqcount.
  have {}/IHm Hrec : {in u, forall i : nat, i < m}.
    move=> i /[dup] iin /uin; rewrite ltnS leq_eqVlt => /orP[/eqP eqi |//].
    by subst i; move/count_memPn: Hc; rewrite iin.
  have {}/Hrec : {in v, forall i : nat, i < m}.
    move=> i /[dup] iin /vin; rewrite ltnS leq_eqVlt => /orP[/eqP eqi |//].
    by subst i; move: Hc; rewrite eqcount => /count_memPn; rewrite iin.
  move/(_ eqcount); move: u v {uin vin eqcount Hc}.
  exact/sub_equiv/subset_comrel.
have minu : m \in u by apply/count_memPn; rewrite Hc.
have minv : m \in v by apply/count_memPn; rewrite -eqcount Hc.
have {c Hc}/IHc Hrec : count_mem m (rem m u) = c.
  by rewrite count_mem_rem Hc eqxx subSS subn0.
have {}/Hrec Hrec: {in rem m u, forall i : nat, i < m.+1}.
  by move=> i /mem_rem/uin.
have {}/Hrec Hrec : {in rem m v, forall i : nat, i < m.+1}.
  by move=> i /mem_rem/vin.
have {eqcount}/Hrec Hrec : forall i, count_mem i (rem m u) = count_mem i (rem m v).
  by move=> i; rewrite !count_mem_rem eqcount.
apply: (equiv_trans (equiv_comrel_rem minu uin) (equiv_sym _)).
apply: (equiv_trans (equiv_comrel_rem minv vin) (equiv_sym _)).
move/(equiv_stable (R := comrel m.+1) [:: m] [::]): Hrec.
by rewrite !cat1s !cats0.
Qed.
Definition FCMT_presP : FCMTP \present FCMT :=
  Presentation FCMT_mgenP FCMT_mgen_eq.

End FreeCommutativeMonoidTuple.
