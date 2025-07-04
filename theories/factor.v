From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq.

Require Import monoids.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma cat_eq0 (T : eqType) (u v : seq T) :
  (u ++ v == [::]) = (u == [::]) && (v == [::]).
Proof. by case: u. Qed.
Lemma map_eq0 (T1 T2 : eqType) (u : seq T1) (f : T1 -> T2):
  (map f u == [::]) = (u == [::]).
Proof. by case: u. Qed.


Lemma catRL_eq (T : eqType) (x y z : seq T) :
  (x ++ y ++ z == y) = (x == [::]) && (z == [::]).
Proof.
apply/eqP/andP => [/(congr1 size)/eqP | [/eqP-> /eqP-> /= /[!cats0]] //].
rewrite !size_cat addnC -[X in _ == X]addn0 -addnA eqn_add2l addn_eq0.
by case/andP => /nilP -> /nilP ->.
Qed.

Lemma cat2E (T : eqType) (u v x y : seq T) :
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

Lemma shape_take (T : Type) (s : seq (seq T)) i :
  shape (take i s) = take i (shape s).
Proof. by elim: i s => [| i IHi] [|s0 s] //= /[!IHi]. Qed.
Lemma shape_drop (T : Type) (s : seq (seq T)) i :
  shape (drop i s) = drop i (shape s).
Proof. by elim: i s => [| i IHi] [|s0 s] /=. Qed.


Section LongestPrefix.

Context {Alph : eqType}.

Implicit Type (u v w : seq Alph).

Lemma prefix_drop_nil (u v : seq Alph) :
  prefix u v -> (u == v) = (drop (size u) v == [::]).
Proof.
case/prefixP=> w {v}->.
by rewrite -{1}(cats0 u) drop_size_cat // (inj_eq (@catl_inj _ u)) eq_sym.
Qed.

Lemma prefix_sizeE u v : prefix u v -> size u >= size v -> u = v.
Proof. by rewrite prefixE => /eqP {2}<- /take_oversize. Qed.

Lemma suffix_sizeE u v : suffix u v -> size u >= size v -> u = v.
Proof.
rewrite -prefix_rev => /prefix_sizeE; rewrite !size_rev => /[apply].
exact: (can_inj revK).
Qed.

Fixpoint long_cprefix u v :=
  if (u, v) is (u0 :: u', v0 :: v') then
    if u0 == v0 then u0 :: long_cprefix u' v'
    else [::]
  else [::].
Definition long_csuffix u v :=
  rev (long_cprefix (rev u) (rev v)).

Lemma long_cprefixC u v : long_cprefix u v = long_cprefix v u.
Proof.
elim: u v => [|u0 u IHu] [|v0 v] //=; rewrite {}IHu eq_sym.
by case: eqP => [->|].
Qed.

Lemma long_cprefixl u v : prefix (long_cprefix u v) u.
Proof.
elim: u v => [|u0 u IHu] [|v0 v] //=.
by case: eqP => [->|//]; rewrite eqxx IHu.
Qed.
Lemma long_cprefixr u v : prefix (long_cprefix u v) v.
Proof. by rewrite long_cprefixC long_cprefixl. Qed.
Lemma long_cprefixP u v w :
  prefix w u -> prefix w v -> prefix w (long_cprefix u v).
Proof.
elim: u v w => [|u0 u IHu] [|v0 v] [|w0 w] //=.
  by move=> _ _; exact: prefix0s.
case/andP => /eqP -> {}/IHu IH; case/andP => /eqP -> {}/IH /=.
by rewrite eqxx /= eqxx /=.
Qed.

Lemma long_csuffixC u v : long_csuffix u v = long_csuffix v u.
Proof. by rewrite /long_csuffix long_cprefixC. Qed.
Lemma long_csuffixl u v : suffix (long_csuffix u v) u.
Proof. by rewrite /long_csuffix suffix_revLR long_cprefixl. Qed.
Lemma long_csuffixr u v : suffix (long_csuffix u v) v.
Proof. by rewrite /long_csuffix suffix_revLR long_cprefixr. Qed.
Lemma long_csuffixP u v w :
  suffix w u -> suffix w v -> suffix w (long_csuffix u v).
Proof.
rewrite /long_csuffix -prefix_revLR => pru prv.
by apply: long_cprefixP; rewrite prefix_rev.
Qed.

End LongestPrefix.


Section Infixes.

Context {Alph : choiceType}.

Implicit Type (u v w : seq Alph).

Definition prefixes u := [seq take i u | i <- iota 0 (size u).+1].
Definition non_empty_prefixes u := [seq take i u | i <- iota 1 (size u)].
Definition cut2 u := [seq (take i u, drop i u) | i <- iota 1 (size u)].

Lemma head_prefixes x0 u : head x0 (prefixes u) = [::].
Proof. by rewrite -nth0 (nth_map 0) ?size_iota //= take0. Qed.
Lemma behead_prefixes u : behead (prefixes u) = non_empty_prefixes u.
Proof. by []. Qed.
Lemma prefixes_cut2E u : non_empty_prefixes u = [seq p.1 | p <- cut2 u].
Proof. by rewrite /prefixes /cut2 -map_comp; apply eq_map => i. Qed.

Lemma prefixes_uniq u : uniq (prefixes u).
Proof.
rewrite map_inj_in_uniq ?iota_uniq // => i j.
rewrite !mem_iota /= add0n !ltnS => lti ltj /(congr1 size).
by rewrite !size_take_min (minn_idPl lti) (minn_idPl ltj) => ->.
Qed.
Lemma non_empty_prefixes_uniq u : uniq (non_empty_prefixes u).
Proof. by rewrite -behead_prefixes -drop1 drop_uniq // prefixes_uniq. Qed.
Lemma cut2_uniq u : uniq (cut2 u).
Proof.
by have := non_empty_prefixes_uniq u; rewrite prefixes_cut2E => /map_uniq.
Qed.

Lemma cat_cut2E r : all (fun p => p.1 ++ p.2 == r) (cut2 r).
Proof. by rewrite /cut2 all_mapT //= => i; rewrite cat_take_drop. Qed.
Lemma mem_cut2 r u v : (u, v) \in cut2 r = (u != [::]) && (u ++ v == r).
Proof.
apply/mapP/andP => /=[[i] | [uneq /eqP equ]].
  rewrite mem_iota add1n ltnS => Hi [{u}-> {v}->].
  split; last by rewrite cat_take_drop.
  by case: i r Hi => [|i] [|r0 r].
rewrite -{}equ; exists (size u).
  by rewrite mem_iota add1n ltnS size_cat leq_addr; case: u uneq.
by rewrite take_size_cat // drop_size_cat.
Qed.

Lemma non_empty_prefixes0 u : [::] \notin (non_empty_prefixes u).
Proof.
case: u => [// | u0 u].
rewrite /non_empty_prefixes /=.
by apply/negP=> /mapP[/= [|i]]; rewrite mem_iota.
Qed.
Lemma prefixes_non_emtpyE u : prefixes u = [::] :: (non_empty_prefixes u).
Proof. by rewrite /non_empty_prefixes; case: u. Qed.

Lemma prefixesP u v : (prefix u v) = (u \in prefixes v).
Proof.
rewrite /prefixes; apply/prefixP/idP => [[w {v}->] | /mapP[i]].
- rewrite -{1}(take_size_cat w (erefl (size u))).
  apply: (map_f (fun i => take i (u ++ w))).
  by rewrite mem_iota /= add0n ltnS size_cat leq_addr.
- rewrite mem_iota /= add0n ltnS => leisz {u}->.
  by exists (drop i v); rewrite cat_take_drop.
Qed.
Lemma non_empty_prefixesP u v :
  ((u != [::]) && prefix u v) = (u \in non_empty_prefixes v).
Proof.
rewrite prefixesP prefixes_non_emtpyE.
by case: u => //=; rewrite (negbTE (non_empty_prefixes0 _)).
Qed.

Fixpoint non_empty_infixes u :=
  non_empty_prefixes u ++ if u is _ :: u' then non_empty_infixes u' else [::].
Fixpoint cut3 u :=
  [seq ([::], p.1, p.2) | p <- cut2 u]
    ++
    if u is u0 :: u' then [seq (u0 :: p.1.1, p.1.2, p.2) | p <- cut3 u']
    else [::].
Definition infixes u := [::] :: non_empty_infixes u.

Lemma infixe0s u : [::] \in infixes u.
Proof. by rewrite inE eqxx. Qed.
Lemma head_infixes x0 u : head x0 (infixes u) = [::].
Proof. by case: u. Qed.
Lemma infixes_cons (u0 : Alph) u :
  infixes (u0 :: u) = prefixes (u0 :: u) ++ behead (infixes u).
Proof. by []. Qed.

Lemma infixes_cut3E u : non_empty_infixes u = [seq t.1.2 | t <- cut3 u].
Proof. by elim: u => // u0 u /= ->; rewrite !map_cat /= -!map_comp. Qed.
Lemma cat_cut3E u : all (fun p => p.1.1 ++ p.1.2 ++ p.2 == u) (cut3 u).
Proof.
elim: u => // u0 u IHu /=.
rewrite cat_take_drop !eqxx /= all_cat -!map_comp; apply/andP; split.
  by rewrite all_mapT //= => i; rewrite cat_take_drop.
by move: IHu; rewrite all_map; apply: sub_all => [[[pre mid] suf]] /= /eqP ->.
Qed.
Lemma cut_consE a u :
  cut3 (a :: u) =
    [seq ([::], p.1, p.2) | p <- cut2 (a :: u)]
      ++ [seq (a :: p.1.1, p.1.2, p.2) | p <- cut3 u].
Proof. by []. Qed.
Lemma cut3_uniq u : uniq (cut3 u).
Proof.
elim: u => // u0 u IHu; rewrite cut_consE cat_uniq.
apply/and3P; split.
- rewrite map_inj_uniq; first exact: cut2_uniq.
  by move=> /= -[v1 v2][w1 w2]/= [-> ->].
- apply/negP => /hasP[x]/mapP[y _ {x}->].
  by case/mapP=> [z _ []].
- by rewrite map_inj_uniq // => /= -[[a1 a2] a3][[b1 b2] b3]/= [-> -> ->].
Qed.
Lemma mem_cut3 r u v w :
  (u, v, w) \in cut3 r = (v != [::]) && (u ++ v ++ w == r).
Proof.
elim: r u v w => [/= | r0 r IHr] u v w.
  by rewrite in_nil; case: u; case: v.
rewrite cut_consE mem_cat.
apply/orP/andP => [[|]|].
- case/mapP => /= -[a b].
  by rewrite mem_cut2 => /andP[/= aneq0 eqr] [{u}->{v}->{w}->].
- case/mapP => /= -[[a b] c].
  by rewrite {}IHr => /andP[bneq0 /eqP eqr] [{u}->{v}->{w}->] /=; rewrite eqr.
case=> vneq0 /eqP eqr; case: u eqr => [|u0 u] eqr.
  left; apply/mapP => /=; exists (v, w) => //=.
  by rewrite mem_cut2 vneq0 -eqr /=.
move: eqr => [{u0}-> eqr].
right; apply/mapP => /=; exists (u, v, w) => //=.
by rewrite IHr vneq0 /= eqr.
Qed.

Lemma non_empty_infixes0 u : [::] \notin non_empty_infixes u.
Proof.
elim: u => [|u0 u IHu] //=.
apply/negP; rewrite inE => /orP[//|].
rewrite mem_cat orbC (negbTE IHu) /= => /mapP[i].
by rewrite mem_iota; case: i.
Qed.

Lemma infixes_non_emtpyE u : infixes u = [::] :: (non_empty_infixes u).
Proof. by rewrite /non_empty_infixes; case: u. Qed.

Lemma infixesP u v : (infix u v) = (u \in infixes v).
Proof.
apply/infixP/idP => [[pre][suf] {v}-> | ].
- elim: pre => [| p0 p IHp].
    case: u => [| u0 u]; first exact: infixe0s.
    rewrite cat0s [_ ++ _]/= infixes_cons mem_cat /=.
    by rewrite -prefixesP /= eqxx /= prefix_prefix.
  rewrite [_ ++ _]/= infixes_cons mem_cat;
  move: IHp; rewrite infixes_non_emtpyE /=.
  by case: u => [|u0 u] //=; rewrite inE => /orP[/eqP// | ->] /[!orbT].
- elim: v u => [| v0 v IHv] u.
    by rewrite /= inE => /eqP ->; exists [::]; exists [::].
  case: u => [_ | u0 u]; first by exists [::]; exists (v0 :: v).
  rewrite infixes_cons mem_cat => /orP[{IHv} |].
    rewrite -prefixesP => /= /andP[/eqP {v0}<-] /prefixP[w {v}->].
    by exists [::]; exists w.
  move=> /mem_behead {}/IHv [pre][suf]{v}->.
  by exists (v0 :: pre); exists suf.
Qed.

Lemma non_empty_infixesP u v :
  ((u != [::]) && infix u v) = (u \in non_empty_infixes v).
Proof.
rewrite infixesP infixes_non_emtpyE.
by case: u => //=; rewrite (negbTE (non_empty_infixes0 _)).
Qed.

Lemma count_mem_non_empty_infixesE u r :
  count_mem u (non_empty_infixes r) = count (fun p => p.1.2 == u) (cut3 r).
Proof. by rewrite infixes_cut3E /= count_map; exact: eq_count. Qed.

Lemma count_mem_non_empty_infixes_ge_size u r (s : seq (seq Alph * seq Alph)) :
  u != [::] -> uniq s -> all (fun p => p.1 ++ u ++ p.2 == r) s ->
  count_mem u (non_empty_infixes r) >= size s.
Proof.
rewrite count_mem_non_empty_infixesE => uneq0 uniqs /allP /= alls.
have -> : size s = size [seq (p.1, u, p.2) | p <- s] by rewrite size_map.
rewrite -size_filter; apply: uniq_leq_size.
  by rewrite map_inj_uniq // => -[/= p1 p2][q1 q2] /= [-> ->].
move=> -[[a b] c] /mapP[[pre suf] {}/alls/eqP/=eqr [{a}->{b}->{c}->]].
by rewrite mem_filter /= mem_cut3 uneq0 eqr !eqxx.
Qed.

End Infixes.


Section DropSS.

Context {Alph : eqType}.
Implicit Type (s : seq (seq Alph)).

Fixpoint dropss n s :=
  if s is s0 :: s' then
    if n < size s0 then (drop n s0) :: s'
    else dropss (n - size s0) s'
  else [::].

Lemma dropss0 s : [::] \notin s -> dropss 0 s = s.
Proof. by case: s => [|[|a s0] s]. Qed.

Lemma nil_notin_dropss i s : [::] \notin s -> [::] \notin dropss i s.
Proof.
elim: s i => [|s0 s IHs] //= i; rewrite inE negb_or eq_sym => /andP[s0n0 snon0].
case: ltnP => [lti | gei]; last exact: IHs.
rewrite inE negb_or eq_sym snon0 andbT.
apply/negP => /eqP/(congr1 size)/eqP.
by rewrite size_drop /= subn_eq0 leqNgt lti.
Qed.

Lemma flatten_dropss i s : flatten (dropss i s) = drop i (flatten s).
Proof. by elim: s i => [|s0 s IHs] //= i; rewrite drop_cat; case: ltnP. Qed.

Lemma size_dropss i s : size (dropss i s) <= size s.
Proof.
elim: s i => [|s0 s IHs] //= i.
case: ltnP => [lti | gei] //.
by apply: ltnW; rewrite ltnS; exact: IHs.
Qed.

End DropSS.


Section GreedyFactorisation.

Context {Alph : choiceType}.

Implicit Type (u v w : seq Alph).
Variable p : pred (seq Alph).
Hypothesis pnil : p [::].
Hypothesis pstable : forall u v, infix v u -> p u -> p v.

Lemma all_dropss g n : all p g -> all p (dropss n g).
Proof.
move/allP => /= allpg; apply/allP => /=.
elim: g n allpg => // g0 g IHg n pg => v /=.
have pg0 : p g0 by apply: pg; rewrite inE eqxx.
have {}pg : {in g, forall x : seq Alph, p x}.
  by move=> /= w win; apply: pg; rewrite inE win orbT.
case: ltnP => _; last exact: IHg.
rewrite inE => /orP[/eqP-> | /pg //].
exact/(pstable _ pg0)/infix_drop.
Qed.

(** u is a greedy prefix of v for the pieces accepted by p *)
Definition is_greedy_prefix u v :=
  p u && ((u == v) || prefix u v && ~~ p (take (size u).+1 v)).
Fixpoint is_greedy_rec f :=
  if f is f0 :: tl then
    (is_greedy_prefix f0 (f0 ++ head [::] tl)) && (is_greedy_rec tl)
  else true.
Definition is_greedy_factorisation u f :=
  [&& [::] \notin f, (* to prevent factorisation ending with [::] *)
    flatten f == u &
      is_greedy_rec f].


Lemma is_greedy_prefix_eq u v : is_greedy_prefix u v -> p v -> u = v.
Proof.
rewrite /is_greedy_prefix => /andP[pu /[swap] pv] /orP[/eqP -> // | /andP[pref]].
by have /prefixW/pstable/(_ pv) -> := prefix_take v (size u).+1.
Qed.

Lemma is_greedy_prefix_impl u v1 v2 :
  take (size u).+1 v1 = take (size u).+1 v2 ->
  is_greedy_prefix u v1 -> is_greedy_prefix u v2.
Proof.
rewrite /is_greedy_prefix => eqtake; case: (p u) => //=.
case: eqP => [equv1 _ | /eqP nequv1 /andP[]] /=.
  suff -> : u = v2 by rewrite eqxx.
  move: eqtake; rewrite -{v1}equv1 take_oversize // => /[dup] equ /(congr1 size).
  rewrite size_take; case: ltnP => [_ /eqP| _ eqsz]; first by rewrite ltn_eqF.
  by rewrite equ eqsz take_oversize.
rewrite !prefixE eqtake => /eqP {4}<- ->.
rewrite andbT /=; apply/orP; right; apply/eqP.
move/(congr1 (take (size u))): eqtake.
by rewrite -!take_min; have /minn_idPl -> : size u <= (size u).+1.
Qed.
Lemma is_greedy_prefixE u v1 v2 :
  take (size u).+1 v1 = take (size u).+1 v2 ->
  is_greedy_prefix u v1 = is_greedy_prefix u v2.
Proof. by move=> H; apply/idP/idP; apply: is_greedy_prefix_impl; rewrite H. Qed.

Lemma is_greedy_prefix_take u v :
  is_greedy_prefix u v = is_greedy_prefix u (take (size u).+1 v).
Proof. by apply: is_greedy_prefixE; rewrite -take_min minnn. Qed.

Theorem is_greedy_min_size u (f g : seq (seq Alph)) :
  is_greedy_factorisation u f -> flatten g = u -> all p g -> size f <= size g.
Proof.
move: f g; have [n leMn] := ubnP (size u); elim: n u leMn => // n IHn u.
rewrite ltnS leq_eqVlt => /orP[/eqP szu f g|]; last exact: IHn.
case: n IHn szu => [_ /eqP/nilP -> | n IHn szu].
  rewrite /is_greedy_factorisation /=.
  by case: f => [|[|h0 f0] f] //= /[!andbF].
rewrite /is_greedy_factorisation; case eqf: f => [//| f0 ftl] /and3P[].
rewrite -{2 4}eqf inE negb_or eq_sym => /andP[f0n0 fn0] /eqP flatf /=/andP[greed rec].
case eqg : g => [/= | g0 gtl].
  by move=> equ _; rewrite -equ /= in szu.
rewrite -{1}eqg => flatg /[dup] allpg /= /andP[pg0 _].
have {}greed : is_greedy_prefix f0 u.
  rewrite -flatf {}eqf /=.
  case: ftl fn0 flatf greed {rec} => [_ /eqP | f1 ftl] //=.
  case: f1 => // a f1 _ _ //=; apply: is_greedy_prefix_impl.
  by rewrite !take_cat ltnNge leqnSn /= subSnn /= !take0.
case: (ltnP (size f0) (size g0)) => [lt0 | le0].
  exfalso; have:= flatf; rewrite -flatg /= eqf eqg /= => /cat2E.
  case/(_ (ltnW lt0)) => suff Hsuff eqg0.
  have ptu : p (take (size f0).+1 u).
    apply/(pstable _ pg0)/prefixW.
    suff -> : take (size f0).+1 u = take (size f0).+1 g0 by apply: prefix_take.
    by rewrite -flatg eqg /= takel_cat.
  move: greed; rewrite /is_greedy_prefix {}ptu /= andbF orbF andbC.
  case: eqP => // eqf0u _; subst f0.
  by move: lt0; rewrite -flatg eqg /= size_cat ltnNge leq_addr.
have {rec greed}/IHn greedftl : is_greedy_factorisation (flatten ftl) ftl.
  by rewrite /is_greedy_factorisation /= fn0 eqxx rec /=.
have {}/greedftl lesz : size (flatten ftl) < n.+1.
  rewrite -szu -flatf eqf size_cat; move: f0n0; case f0 => // a0 f0' _.
  by rewrite /= addSn ltnS leq_addl.
rewrite eqf /= ltnS.
case: ftl eqf flatf lesz fn0 => //= f1 ftl eqf flatf lesz.
rewrite inE negb_or eq_sym => /andP[f1n0 _].
case: gtl eqg flatg allpg => [-> | g1 gtl eqg flatg].
  rewrite /= cats0 => eqg0 _; subst g0; exfalso.
  move: flatf le0 => /(congr1 size) <-.
  case: f1 {lesz} f1n0 eqf => // a f1 _ ->.
  by rewrite !size_cat /= addSn addnS ltnNge leq_addr.
rewrite -eqg => allpg.
apply: (leq_trans (lesz (dropss (size f0) g) _ _)) => {lesz}.
- by rewrite flatten_dropss flatg -flatf eqf /= drop_size_cat.
- exact: all_dropss.
- rewrite eqg /= ltnNge le0 /=; case: ltnP => _ //=.
  exact: (leq_trans (size_dropss _ _)).
Qed.


Fixpoint greedy_prefsize_rec u n :=
  if n is n0.+1 then if p (take n u) then n else greedy_prefsize_rec u n0
  else 0.
Definition greedy_prefsize u := greedy_prefsize_rec u (size u).

Lemma greedy_prefsize_full u : p u -> greedy_prefsize u = size u.
Proof.
rewrite /greedy_prefsize.
by case: u => // u0 u /=; rewrite take_size => ->.
Qed.

Lemma greedy_prefsize_rec_le u n : greedy_prefsize_rec u n <= n.
Proof. by elim: n => //= n IHn; case: p => //; exact: (leq_trans IHn). Qed.
Lemma greedy_prefsize_le u : greedy_prefsize u <= size u.
Proof. exact: greedy_prefsize_rec_le. Qed.

Lemma greedy_prefsizeP u :
  is_greedy_prefix (take (greedy_prefsize u) u) u.
Proof.
rewrite /is_greedy_prefix.
case: (boolP (p u)) => [/[dup] pu /greedy_prefsize_full -> | npu].
  by rewrite take_size pu eqxx.
rewrite /greedy_prefsize size_take.
case Hsz : (size u) => [|n] /=.
  by exfalso; move: Hsz npu => /eqP/nilP ->; rewrite pnil.
have nptake1 : ~~ p (take n.+1 u) by rewrite -Hsz take_size.
rewrite (negbTE nptake1) ltnS greedy_prefsize_rec_le.
elim : n {Hsz} nptake1 => [| n IHn] /= nptake.
  by rewrite take0 pnil prefix0s nptake orbC.
case: (boolP (p (take n.+1 u))) => [ptake | /IHn //].
by rewrite ptake nptake prefix_take orbC.
Qed.

Fixpoint greedy_factor_rec u fuel :=
  if fuel is fuel'.+1 then
    if u == [::] then Some [::] else
      let prefsize := greedy_prefsize u in
      if prefsize == 0 then None else
        if greedy_factor_rec (drop prefsize u) fuel' is Some res
        then Some ((take prefsize u) :: res)
        else None
  else None.
Definition greedy_factor u := greedy_factor_rec u (size u).+1.

Implicit Type (s : seq (seq Alph)).

Lemma greedy_factor_recP u fuel s :
  size u < fuel -> greedy_factor_rec u fuel = Some s ->
  is_greedy_factorisation u s.
Proof.
move=> + /eqP.
elim: fuel u s => [| fuel IHfuel] u s //=; rewrite ltnS => szu.
case: (altP (u =P [::])) => [-> /eqP[<-] // | uneq0].
case: (altP (greedy_prefsize u =P 0)) => // grprfsz.
have:= greedy_prefsize_le u; rewrite leq_eqVlt => /orP[/eqP /[dup] Hgr -> | Hgr].
  rewrite drop_size; case: fuel szu {IHfuel} => //= fuel _ /eqP[{s}<-].
  have:= greedy_prefsizeP u; rewrite Hgr take_size.
  by rewrite /is_greedy_factorisation /= cats0 inE eq_sym uneq0 eqxx andbT /=.
have {}/IHfuel : size (drop (greedy_prefsize u) u) < fuel.
  apply: (leq_trans _ szu); rewrite size_drop ltn_subrL.
  by rewrite lt0n grprfsz /=; apply: (leq_ltn_trans _ Hgr).
case: (greedy_factor_rec _ _) => // => fact /(_ fact (eqxx _)) Hfact /eqP[{s}<-].
move: Hfact; rewrite /is_greedy_factorisation /=.
rewrite inE negb_or => /and3P[/[dup] fact0 -> /eqP/[dup] Hfact-> ->].
rewrite cat_take_drop eqxx !andbT andbC /= andbC eq_sym; apply/andP; split.
  case: u uneq0 grprfsz {szu Hgr fact fact0 Hfact} => [|u0 u] // _.
  by case: (greedy_prefsize _).
have {grprfsz} := greedy_prefsizeP u; apply: is_greedy_prefix_impl.
rewrite size_take Hgr.
rewrite -{2}(cat_take_drop (greedy_prefsize u) u) -{}Hfact.
case: fact fact0 => [//| f0 fact] /= Hfact.
rewrite take_cat [in RHS]take_cat size_take Hgr subSnn ltnNge leqnSn /=.
move: Hfact; rewrite inE negb_or eq_sym => /andP[/[swap] _].
by case: f0 => // a f1 _ /=; rewrite !take0.
Qed.
Lemma greedy_factorP u s :
  greedy_factor u = Some s -> is_greedy_factorisation u s.
Proof. exact: greedy_factor_recP. Qed.


Lemma greedy_factor_recNP u fuel :
  size u < fuel ->
  forall s, all p s -> flatten s = u -> greedy_factor_rec u fuel != None.
Proof.
elim: fuel u => [| fuel IHfuel] u //=; rewrite ltnS => szu s /allP allps flats.
have {allps} : all p [seq v <- s | v != [::]].
  by apply/allP => v /[!mem_filter]/andP[_ /allps].
have {flats} : flatten [seq v <- s | v != [::]] = u.
  rewrite -{}flats; elim: s => // s0 s IHs /=.
  by case: eqP => [-> //= | _ /=]; rewrite IHs.
have : [::] \notin [seq v <- s | v != [::]] by rewrite mem_filter eqxx.
case: (filter _ s) => [|[|a s0] {}s] // sn0 flats allps.
  by rewrite -flats eqxx.
rewrite /= in flats; rewrite -{1}flats /=.
case: (altP (greedy_prefsize u =P 0)) => [gr0 | grprfsz].
  exfalso.
  have {allps} pa : p [:: a].
    move: allps => /andP[/pstable Hstable].
    by have {}/Hstable : infix [:: a] (a :: s0)
      by apply: prefixW; rewrite /= eqxx prefix0s.
  have:= greedy_prefsizeP u; rewrite gr0 take0 /is_greedy_prefix.
  by rewrite pnil /= -flats /= take0 pa.
have {}/IHfuel : size (drop (greedy_prefsize u) u) < fuel.
  apply: (leq_trans _ szu); rewrite size_drop ltn_subrL.
  by rewrite lt0n grprfsz /= -flats.
case: (greedy_factor_rec _ _) => //.
move/(_ (dropss (greedy_prefsize u) ((a :: s0) :: s))); apply; first last.
  by rewrite flatten_dropss /= flats.
exact: all_dropss.
Qed.
Lemma greedy_factorNP u :
  forall s, all p s -> flatten s = u -> greedy_factor u != None.
Proof. exact: greedy_factor_recNP. Qed.

End GreedyFactorisation.


Module Tests.
Section Tests.

Let G := [:: [:: 1; 2]; [:: 3; 4; 5]; [:: 6; 7]].
Let f0 := [:: 1; 2; 3].

Goal is_greedy_factorisation predT [:: 1; 2] [:: [:: 1;  2]].
by compute. Qed.
Goal is_greedy_factorisation (fun v => size v <= 1) [:: 1; 2] [:: [:: 1];  [:: 2]].
by compute. Qed.

End Tests.
End Tests.
