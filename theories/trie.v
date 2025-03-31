From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

HB.mixin Record isPointed T := { point : T }.

#[short(type=pointedType)]
HB.structure Definition Pointed := {T of isPointed T & Choice T}.

HB.instance Definition _ := isPointed.Build unit tt.
HB.instance Definition _ := isPointed.Build bool false.
HB.instance Definition _ := isPointed.Build Prop False.
HB.instance Definition _ := isPointed.Build nat 0.
HB.instance Definition _ (T T' : pointedType) :=
  isPointed.Build (T * T')%type (point, point).
HB.instance Definition _ (T : choiceType) := isPointed.Build (option T) None.



Section Defs.

Context {rT : pointedType}.

Inductive trie := Trie of rT * seq trie.

Implicit Types (t : trie) (x y : rT) (v w : seq nat) (s c : seq trie).

Definition emptytrie := Trie (point, [::]).

Section Induction.

Variables (P : trie -> Type) (Ps : seq trie -> Type).
Hypothesis Hnil : Ps [::].
Hypothesis Hcons : forall t s, P t -> Ps s -> Ps (t :: s).
Hypothesis IH : forall s, Ps s -> forall x, P (Trie (x, s)).

Fixpoint rectrie t : P t :=
  let: Trie (x, ch) := t in
  let pch := (fix pchrec sub :=
                match sub return Ps sub with
                | h :: s => Hcons h s (rectrie h) (pchrec s)
                | [::] => Hnil
                end) ch
  in IH ch pch x.

End Induction.

Section Induction.

Variables (P : trie -> Prop) (Ps : seq trie -> Prop).
Hypothesis Hnil : Ps [::].
Hypothesis Hcons : forall t s, P t -> Ps s -> Ps (t :: s).
Hypothesis IH : forall s, Ps s -> forall x, P (Trie (x, s)).

Fixpoint indtrie t : P t :=
  let: Trie (x, ch) := t in
  let pch := (fix pchrec sub :=
                match sub return Ps sub with
                | h :: s => Hcons h s (indtrie h) (pchrec s)
                | [::] => Hnil
                end) ch
  in IH ch pch x.

End Induction.


Fixpoint eqsub (eqtrie : trie -> trie -> bool) sub1 sub2 {struct sub1} :=
  match sub1 with
  | h1 :: s1 => match sub2 with
                | h2 :: s2 => eqtrie h1 h2 && eqsub eqtrie s1 s2
                | [::] => false
                end
  | [::] => if sub2 is [::] then true else false
  end.

Fixpoint eqtrie tr1 tr2 {struct tr1} :=
  let: Trie (x1, ch1) := tr1 in
  let: Trie (x2, ch2) := tr2 in
  (x1 == x2) && (eqsub eqtrie ch1 ch2).

Lemma eqsub_recP (eqtrie : trie -> trie -> bool) sub1 sub2 :
  reflect (size sub1 = size sub2 /\
             forall i, i < size sub1 ->
                       eqtrie (nth emptytrie sub1 i) (nth emptytrie sub2 i))
    (eqsub eqtrie sub1 sub2).
Proof.
elim: sub1 sub2 => [| t1 sub1 IHsub1] [| t2 sub2] //=; apply (iffP idP) => //.
- by move=> [/esym/eqP].
- by move=> [/eqP].
- move=> /andP[eqt /IHsub1[eqsize Hrec]].
  split; first by rewrite eqsize.
  by case=> [_|i] //=; exact: Hrec.
- move=> [[eqsize H]]; apply/andP; split.
    by have /H /= : 0 < (size sub1).+1 by [].
  apply/IHsub1; split; first exact: eqsize.
  by move=> i; rewrite -ltnS => {}/H /=.
Qed.

Lemma eqtrie_subproof tr1 tr2 : reflect (tr1 = tr2) (eqtrie tr1 tr2).
Proof.
pose Ps (s : seq trie) :=
  forall i, let tr1 := nth emptytrie s i in
            forall tr2, reflect (tr1 = tr2) (eqtrie tr1 tr2).
apply/(rectrie _ Ps) : tr1 tr2; rewrite {}/Ps /=.
- move=> i [[x2 ch2]]; rewrite nth_nil /= /emptytrie.
  by apply (iffP andP) => [[/eqP -> /=] | [-> <-]]; first by case: ch2.
- by move=> t s Ht Hs => [[|i]] tr2 /=.
move=> s Hs v [[x2 ch2]].
apply (iffP andP) => [[/eqP -> /=] | [-> <-]].
  move/eqsub_recP => [eqsize Heq]; congr (Trie (_, _)).
  by apply: (eq_from_nth (x0 := emptytrie)) => //= i /Heq/Hs.
split; first by [].
by apply/eqsub_recP; split => [|i Hi]; last exact/Hs.
Qed.

HB.instance Definition _ := hasDecEq.Build trie eqtrie_subproof.


Definition consn t s :=
  if (s == [::]) && (t == emptytrie) then [::] else t :: s.
Infix ":::" := consn (at level 10) : seq_scope.
Definition nconsn t n :=
  if t == emptytrie then [::] else ncons n emptytrie [:: t].

Fixpoint set_nthn s n t {struct n} : seq trie :=
  match s with
  | [::] => nconsn t n
  | x :: s' => match n with
               | 0 => t ::: s'
               | n'.+1 => x ::: (set_nthn s' n' t)
               end
  end.
Definition nolast s := (last emptytrie s == emptytrie) ==> (s == [::]).

Lemma nolast_nil : nolast [::].
Proof. by rewrite /nolast /= !eqxx. Qed.
Lemma nolastP s : reflect (last emptytrie s = emptytrie -> s = [::]) (nolast s).
Proof.
by apply (iffP implyP) => [/[swap]/eqP/[swap]/[apply]/eqP-> // | /[swap]/eqP H ->].
Qed.

Lemma rcons_eqnilF s t : (rcons s t == [::]) = false.
Proof. by case: s. Qed.
Lemma last_ncons T n (x0 : T) (s : seq T) : last x0 (ncons n x0 s) = last x0 s.
Proof. by elim: n. Qed.
Lemma all_ncons T (P : pred T) n (x0 : T) (s : seq T) :
  P x0 -> all P s -> all P (ncons n x0 s).
Proof. by elim: n => //= n IHn /[dup]{}/IHn/[swap]->. Qed.

Lemma nolast_consn t s : nolast s -> nolast (consn t s).
Proof.
rewrite /consn; case/lastP: s => [|sn s] /=; first by case: (altP (_ =P _)).
by rewrite /nolast last_rcons rcons_eqnilF /= last_rcons.
Qed.
Lemma nolast_nconsn t n : nolast (nconsn t n).
Proof.
rewrite /nconsn; apply/nolastP.
case: (altP (_ =P _)) => [_ // |].
by rewrite last_ncons /= => /[swap] -> /[!eqxx].
Qed.
Lemma nolast_consK t s : nolast (t :: s) -> nolast s.
Proof.
case/lastP: s => [_|s sn] /=; first exact: nolast_nil.
move/nolastP; rewrite /= last_rcons => H.
by apply/nolastP; rewrite last_rcons => /H.
Qed.
Lemma nolast_consnK t s : nolast (t ::: s) -> nolast s.
Proof.
case/lastP: s => [_|s sn] /=; first exact: nolast_nil.
move/nolastP; rewrite /consn ?eqxx ?rcons_eqnilF /= last_rcons => H.
by apply/nolastP; rewrite last_rcons => /H.
Qed.

Reserved Notation "'normals' ch" (at level 10).
Fixpoint normal t := let: Trie (x, ch) := t in normals ch
where "'normals' ch" := (all normal ch && nolast ch).
Lemma normalE x ch : normal (Trie (x, ch)) = normals ch.
Proof. by []. Qed.

Structure ntrie : Type := NTrie {trval :> trie; _ : normal trval}.
HB.instance Definition _ := [isSub for trval].
HB.instance Definition _ := [Equality of ntrie by <:].

Lemma ntrieP (t : ntrie) : normal t.
Proof. by case: t. Qed.
Hint Resolve ntrieP : core.

Definition mkntrie (t : ntrie) mktrie : ntrie :=
  mktrie (let: NTrie _ tP := t return normal t in tP).
Lemma mkntrieE (t : ntrie) : mkntrie t (fun sP => @NTrie t sP) = t.
Proof. by case: t. Qed.
Notation "[ 'normaltrie' 'of' s ]" := (mkntrie _ (fun sP => @NTrie s sP))
  (at level 0, format "[ 'normaltrie'  'of'  s ]") : form_scope.

Lemma normals_nil : normals [::].
Proof. by rewrite nolast_nil. Qed.
Lemma normal_empty : normal emptytrie.
Proof. by rewrite normalE /= nolast_nil. Qed.
Canonical norempty := NTrie emptytrie normal_empty.
Hint Resolve nolast_nil normals_nil normal_empty : core.

(*
Let norempty_check : ntrie := emptytrie.
Let norempty_check2 : ntrie := [normaltrie of emptytrie].
 *)

Lemma normals_consK t s : normals (t :: s) -> normal t /\ normals s.
Proof. by move=> /andP[/=/andP[-> ->] /nolast_consK->]. Qed.

Lemma normals_consn t s : normal t -> normals s -> normals (t ::: s).
Proof.
rewrite /consn /=; case: eqP => [->{s} /= | /eqP Hs /= -> /=].
  case: eqP => //= /eqP /negbTE t0 -> _ /=.
  by rewrite /nolast /= t0.
rewrite /nolast => /andP[->]/=.
case/lastP: s Hs => // s sn _.
rewrite !last_rcons; case: eqP => //= _.
by rewrite rcons_eqnilF.
Qed.
Lemma normals_nconsn t n : normal t -> normals (nconsn t n).
Proof.
rewrite nolast_nconsn andbT /nconsn => nort.
by case: eqP => [// | nemp]; apply: all_ncons => //= /[!andbT].
Qed.

Lemma set_nthn_nil n t : set_nthn [::] n t = nconsn t n.
Proof. by case: n. Qed.

Lemma normals_set_nthn s n t : normals s -> normal t -> normals (set_nthn s n t).
Proof.
move=> nors nort; elim: n s nors => [|n IHn] //=; case=> [|s0 s].
- by move=> _; exact: normals_nconsn.
- by case/normals_consK => _ nors; apply: normals_consn.
- by move=> _; exact: normals_nconsn.
- case/normals_consK => nors0 nors.
  by apply: normals_consn; last exact: IHn.
Qed.


Fixpoint updatetrie t v (upd : rT -> rT) :=
  let: Trie (x, ch) := t in
  if v is v0 :: v' then
    let rec := updatetrie (nth emptytrie ch v0) v' upd in
    Trie (x, set_nthn ch v0 rec)
  else
    Trie (upd x, ch).
Definition addtrie t v x := updatetrie t v (fun => x).
Definition instrie t v x := updatetrie t v (fun y => if y == point then x else y).
Definition deltrie t v := updatetrie t v (fun => point).

Fixpoint gettrie t v :=
  if v is v0 :: v' then
    let: Trie (_, ch) := t in gettrie (nth emptytrie ch v0) v'
  else
    let: Trie (res, _) := t in res.

Lemma nth_all_normal s : all normal s -> forall i, normal (nth emptytrie s i).
Proof.
move/allP => Hall i.
case: (ltnP i (size s)) => [/(mem_nth emptytrie)/Hall // | Hsize].
by rewrite nth_default // normal_empty.
Qed.

Lemma updatetrieP t v upd : normal t -> normal (updatetrie t v upd).
Proof.
elim: v t => [| v0 v IHs] [[x ch]] //= /[dup ]nors /andP[all_sub noempt].
apply/(normals_set_nthn _ _ _ nors)/IHs.
exact: nth_all_normal.
Qed.
Canonical norupdate (t : ntrie) v upd :=
  NTrie (updatetrie t v upd) (updatetrieP t v upd (ntrieP t)).
(*
Let update_check (x : rT) : ntrie :=
      updatetrie
         (updatetrie emptytrie [:: 2; 1] (fun=> x))
         [:: 1; 2; 3] (fun=> x).
 *)
Local Lemma update_check x :
  normal (addtrie (addtrie emptytrie [:: 2; 1] x) [:: 1; 2; 3] x).
Proof. exact: ntrieP. Qed.
Local Lemma add_check x :
  normal (addtrie (addtrie emptytrie [:: 2; 1] x) [:: 1; 2; 3] x).
Proof. exact: ntrieP. Qed.

Lemma get_emptytrie v : gettrie emptytrie v = point.
Proof. by elim: v => [|v0 v]; rewrite //= nth_nil. Qed.
Lemma gettrie_cons x s i w :
  gettrie (Trie (x, s)) (i :: w) = gettrie (nth emptytrie s i) w.
Proof. by []. Qed.

Lemma normal_isemptyP t :
  normal t -> reflect (gettrie t =1 fun=> point) (t == emptytrie).
Proof.
move=> nortr; apply (iffP eqP) => [-> w |].
  by rewrite get_emptytrie.
pose Ps (s : seq trie) := all normal s ->
  forall i, let tr1 := nth emptytrie s i in
            gettrie tr1 =1 (fun=> point) -> tr1 = emptytrie.
apply/(rectrie _ Ps): t nortr; rewrite {}/Ps /=.
- by move=> _ i _; rewrite nth_nil.
- by move=> t s IHt IHs /andP[nort nors] [/(IHt nort) -> |i] //=; exact: IHs.
case=> [_ x _ /(_ [::]) /= -> // | s0 s] /=.
move=> IHs x /andP[/[dup] {}/IHs Hrec Hnor n0].
case/lastP: s Hrec Hnor n0 => [| s sn] /= Hrec.
  rewrite andbT => nors0 n0.
  move/(_ 0): Hrec => /= Hrec /= Habs.
  have {Hrec}Habs : s0 = emptytrie by apply/Hrec => w; apply: Habs (0 :: w).
  by move: n0; rewrite /nolast /= Habs eqxx /=.
rewrite all_rcons => /and3P[_ norsn _].
rewrite /nolast /= last_rcons => sn0 Habs.
exfalso; have {sn0} : sn != emptytrie by move: sn0; case: eqP.
move/(_ (size s).+1): Hrec; rewrite /= nth_rcons ltnn eqxx => ->.
  by rewrite eqxx.
move=> w; move/(_ ((size s).+1 :: w)): Habs.
by rewrite gettrie_cons /= nth_rcons ltnn eqxx.
Qed.
Lemma ntriel_isemptyP (t : ntrie) :
  reflect (gettrie t =1 fun=> point) (t == emptytrie).
Proof. exact: normal_isemptyP. Qed.

Lemma normal_eqP tr1 tr2 : normal tr1 -> normal tr2 ->
  reflect (gettrie tr1 =1 gettrie tr2) (tr1 == tr2).
Proof.
move=> nortr1 nortr2; apply (iffP eqP) => [-> //|].
apply/(rectrie _ (fun s : seq trie => all normal s ->
  forall i, let tr1 := nth emptytrie s i in
    forall tr2, normal tr2 ->
      gettrie tr1 =1 gettrie tr2 -> tr1 = tr2)): tr1 tr2 nortr1 nortr2.
- move=> /= _ i t Hempt; rewrite nth_nil => Heq.
  apply/esym/eqP/normal_isemptyP => // w.
  by rewrite -Heq get_emptytrie.
- move=> t s IHtr IHs => /andP[nortr nors] [|i] /= tr2 nortr2; first exact: IHtr.
  exact: IHs.
move=> s IHs x [[v2 s2]] /=
         /andP[/[dup]{}/IHs IHs nors sn0] /= /andP[nors2 s2n0] Heq.
have /= -> := Heq [::]; congr (Trie (_, _)).
suff eq_size : size s = size s2.
  apply: (eq_from_nth (x0 := emptytrie) eq_size) => i lti.
  apply: IHs => [|w]; first exact: nth_all_normal.
  exact: (Heq (i :: w)).
have {IHs Heq} eqnth i : nth emptytrie s i = nth emptytrie s2 i.
  apply: IHs => [|w]; first exact: nth_all_normal.
  by have := Heq (i :: w); rewrite !gettrie_cons.
wlog: s s2 nors nors2 sn0 s2n0 eqnth / size s <= size s2 => [Hwlog|].
  by case: (leqP (size s) (size s2)) => [|/ltnW] /Hwlog->.
rewrite {nors nors2} leq_eqVlt => /orP[/eqP-> // | lts].
exfalso; suff H : last emptytrie s2 == emptytrie.
  by move: lts; rewrite (eqP (implyP s2n0 H)) ltn0.
rewrite -nth_last -{}eqnth nth_default //.
exact: (leq_trans lts (leqSpred _)).
Qed.
Lemma ntrie_eqP (tr1 tr2 : ntrie) :
  reflect (gettrie tr1 =1 gettrie tr2) (tr1 == tr2).
Proof. exact: normal_eqP. Qed.


Lemma nth_consn t s : nth emptytrie (t ::: s) =1 nth emptytrie (t :: s).
Proof.
rewrite /consn; case: eqP => [-> | //].
by case: eqP => [-> | //] [// | n]/=; rewrite nth_nil.
Qed.
Lemma nth_set_nth_seqtrie s i t j :
  nth emptytrie (set_nthn s i t) j = if j == i then t else nth emptytrie s j.
Proof.
elim: s i j => [|/= s0 s IHs] i j.
  rewrite set_nthn_nil nth_nil /nconsn.
  case: eqP => [->|_ ]; first by rewrite nth_nil if_same.
  rewrite nth_ncons; case: (ltngtP i j) => [| // | ->]; last by rewrite subnn.
  rewrite -subn_gt0; case: (j - i) => //= {j}i _.
  by rewrite nth_nil.
by case: i j => [|i] [|j] /=; rewrite !nth_consn ?eqSS /=.
Qed.
Lemma get_updatetrie t v upd w :
  gettrie (updatetrie t v upd) w =
    if w == v then upd (gettrie t w) else gettrie t w.
Proof.
elim: w v t => [| w0 w IHw] [|v0 v] [[x s]] //.
rewrite [updatetrie _ _ _]/= !gettrie_cons eqseq_cons.
rewrite nth_set_nth_seqtrie.
by case eqP => [->|].
Qed.

Lemma updatetrie_comp t v u1 u2 :
  normal t -> updatetrie t v (u1 \o u2) = updatetrie (updatetrie t v u2) v u1.
Proof.
move=> nortr; apply/eqP/normal_eqP; repeat try apply: updatetrieP => //.
by move=> w; rewrite !get_updatetrie /=; case: eqP.
Qed.
Lemma updatetrieC t v w u1 u2 :
  normal t -> v != w ->
  updatetrie (updatetrie t v u1) w u2 = updatetrie (updatetrie t w u2) v u1.
Proof.
move=> nortr neq; apply/eqP/normal_eqP; repeat try apply: updatetrieP => //.
move=> x; rewrite !get_updatetrie /=.
by case eqP => [->| //]; rewrite eq_sym (negbTE neq).
Qed.

Implicit Type (p : (seq nat) * rT).
Notation tpair := (seq ((seq nat) * rT)).
Fixpoint mktallytrie (rec : trie -> tpair) i ch : tpair :=
  if ch is c0 :: c then
    [seq (i :: p.1, p.2) | p <- rec c0] ++ mktallytrie rec i.+1 c
  else [::].
Fixpoint tallytrie t : tpair :=
  let: Trie (x, ch) := t in
  let res := mktallytrie tallytrie 0 ch in
  if x == point then res else ([::], x) :: res.
Definition assoc (ps : tpair) v :=
  (nth (v, point) ps (find (fun p => p.1 == v) ps)).2.
Fixpoint mktrie_rec res (ps : tpair) :=
  if ps is (s, v) :: tl then mktrie_rec (instrie res s v) tl
  else res.
Definition mktrie (ps : tpair) := mktrie_rec emptytrie ps.

Lemma assoc0 v : assoc [::] v = point.
Proof. by []. Qed.
Lemma assoc_cat (p1 p2 : tpair) v :
  assoc (p1 ++ p2) v =
    if has (fun p => p.1 == v) p1 then assoc p1 v else assoc p2 v.
Proof.
rewrite /assoc nth_cat has_find find_cat has_find.
case: findP => /= [nhas | i lti]; last by rewrite !lti.
by rewrite ltnn ltnNge leq_addr /= addKn.
Qed.
Lemma assoc_consl ch u x v :
  assoc ((u, x) :: ch) v = if u == v then x else assoc ch v.
Proof. by rewrite /assoc /=; case: eqP. Qed.

Lemma assoc_map_inj f ch v :
  injective f -> assoc [seq (f p.1, p.2) | p <- ch ] (f v) = assoc ch v.
Proof.
rewrite /assoc find_map => finj.
rewrite (eq_find (a2 := fun p => p.1 == v)); first last.
  by move=> [u x] /=; apply: inj_eq.
move: (find _ _) => pos; case: (ltnP pos (size ch)) => Hpos.
  by rewrite (nth_map (v, point)).
by rewrite !nth_default //= size_map.
Qed.
Lemma assoc_consr ch i v :
  assoc [seq (i :: p.1, p.2) | p <- ch ] (i :: v) = assoc ch v.
Proof. by apply: assoc_map_inj => u {}v []. Qed.
Lemma assoc_point ch v :
  ~~ (has (fun p => p.1 == v) ch) -> assoc ch v = point.
Proof. by rewrite /assoc => /hasNfind ->; rewrite nth_default. Qed.
Lemma has_cons_allpair ich ch i v : i \notin ich ->
  ~~ has (fun p => p.1 == i :: v) [seq (i0 :: p.1, p.2) | i0 <- ich, p <- ch i0].
Proof.
apply contra => /hasP/=[[w x]] /allpairsPdep/=[pos][[u y]].
by case=> + _ /= [{w}-> _{x y} /eqP[<- _]].
Qed.
Lemma assoc_cons_point ich ch i v : i \notin ich ->
  assoc [seq (i0 :: p.1, p.2) | i0 <- ich, p <- ch i0] (i :: v) = point.
Proof. by move/has_cons_allpair/assoc_point. Qed.

Lemma mktallytrieE (rec : trie -> tpair) ch j :
  mktallytrie rec j ch = [seq (i + j :: p.1, p.2) |
                           i <- iota 0 (size ch), p <- rec (nth emptytrie ch i)].
Proof.
elim: ch j => [|c0 c IHc] j //=; congr (_ ++ _).
rewrite -[X in iota X]add1n iotaDl {}IHc; congr flatten.
rewrite -map_comp; apply eq_map => i /=; apply eq_map => p.
by rewrite add1n addSn addnS.
Qed.

Lemma mktallytrie0E (rec : trie -> tpair) ch :
  mktallytrie rec 0 ch = [seq (i :: p.1, p.2) |
      i <- iota 0 (size ch), p <- rec (nth emptytrie ch i)].
Proof. by rewrite mktallytrieE; apply eq_allpairs => [a b]; rewrite addn0. Qed.

Lemma assoc_mktallytrie rec ch i j v :
  i <= j < size ch -> assoc (mktallytrie rec i ch) (j :: v) =
                        assoc (rec (nth emptytrie ch (j - i))) v.
Proof.
rewrite mktallytrieE /=.
elim: ch i j v => [/= |c0 c IHc] i j v; first by rewrite ltn0 andbF.
rewrite [size _]/= ltnS -add1n iotaD /= !add0n assoc_cat has_map.
rewrite leq_eqVlt; case: eqP => [eqij _ | _ /andP[/= ltij ltjsz]] /=.
  subst j; rewrite subnn /= assoc_consr.
  rewrite (eq_has (a2 := fun p => p.1 == v)); first last.
    by move=> w /=; rewrite eqseq_cons eqxx.
  case: (boolP (has _ _)) => // /assoc_point ->; apply: assoc_point.
  apply/hasPn => /= [[w x]] /allpairsPdep /=[pos][[u y]][].
  rewrite mem_iota add1n => Hpos _ [{w}-> _].
  rewrite eqseq_cons; case: pos Hpos => // pos _.
  by rewrite -{2}(add0n i) eqn_add2r.
rewrite (eq_has (a2 := pred0)) ?has_pred0; first last.
  by move=> w /=; rewrite eqseq_cons (ltn_eqF ltij).
case: j ltij ltjsz => [// | j]; rewrite ltnS => leij ltjsz.
rewrite subSn //= -IHc ?leij ?ltjsz //.
rewrite -[X in iota X]add1n iotaDl -map_comp.
under eq_map => k /= do rewrite add1n addSn.
pose shift v :=  match v with [::] => [::] | i :: v => i.+1 :: v end.
have shift_inj : injective shift by move=> [|i1 v1][|i2 v2] //= [-> ->].
rewrite -[RHS](assoc_map_inj _ _ _ shift_inj) /=; congr assoc.
by rewrite map_allpairs /=.
Qed.

Lemma tallytrieE t : assoc (tallytrie t) =1 gettrie t.
Proof.
pose Ps (s : seq trie) :=
  forall i, let tr1 := nth emptytrie s i in assoc (tallytrie tr1) =1 gettrie tr1.
apply/(rectrie _ Ps) : t; rewrite {}/Ps /=.
- move=> i; rewrite nth_nil /= eqxx => {}i /=.
  by rewrite get_emptytrie.
- by move=> t s IHt IHs [|i] /=.
move=> s IHs x w; rewrite [in LHS]fun_if if_arg.
rewrite -cat1s assoc_cat /= orbF {2}/assoc /=.
case: w => [|w0 w] /=.
  case: eqP => // {x}->; apply: assoc_point; rewrite mktallytrie0E.
  by apply/hasPn => /= [[w x]] /allpairsPdep /=[pos][[u y]][] /= _ _ [-> _].
rewrite if_same mktallytrie0E {x}.
case: (ltnP w0 (size s)) => [ltw0sz | leszw0]; first last.
  rewrite nth_default // get_emptytrie.
  by apply: assoc_cons_point; rewrite mem_iota /= add0n -leqNgt.
rewrite -{}IHs -(subnKC ltw0sz) iotaD -addn1 iotaD !add0n /= -catA.
rewrite allpairs_cat /= !assoc_cat [has _ _](negbTE _) /=; first last.
  by apply: has_cons_allpair; rewrite mem_iota /= add0n ltnn.
case: (boolP (has _ _)) => [_| /assoc_point]; rewrite assoc_consr // => ->.
by apply: assoc_cons_point; rewrite mem_iota negb_and -ltnNge addn1 ltnSn.
Qed.

Lemma get_mktrie_rec t h u :
  all (fun p => p.2 != point) h ->
  gettrie (mktrie_rec t h) u =
    if gettrie t u == point then assoc h u else gettrie t u.
Proof.
elim: h t => [|[v x] h IHh] //= t; first by rewrite assoc0; case: eqP.
case/andP => /negbTE xn0 {}/IHh ->; rewrite get_updatetrie /=.
case: (altP (u =P v)) => [{v}<- | /negbTE nequv] /=; rewrite assoc_consl ?eqxx.
  case: (altP (gettrie t u =P point)) => [|/negbTE ->//].
  by rewrite xn0.
case: (altP (gettrie t u =P point)) => [|]//.
by rewrite eq_sym nequv.
Qed.
Lemma get_mktrie h u :
  all (fun p => p.2 != point) h -> gettrie (mktrie h) u = assoc h u.
Proof. by move/get_mktrie_rec => ->; rewrite get_emptytrie eqxx. Qed.

Fixpoint nbnodes t :=
  let: Trie (x, ch) := t in
  (foldl (fun res t => res + nbnodes t) (x != point) ch).

Lemma size_tallytrie t : size (tallytrie t) = nbnodes t.
Proof.
pose Ps (s : seq trie) := forall i n,
  size (mktallytrie tallytrie i s) + n =
  foldl (fun (res : nat) t => res + nbnodes t) n s.
apply/(rectrie _ Ps): t; rewrite {}/Ps //=.
- move=> t s Ht Hs /= i n.
  by rewrite size_cat -addnA size_map Ht -(Hs i.+1) addnC addnA.
by move=> s IHs /= x; case: eqP => _ /=; rewrite -(IHs 0) ?addn0 ?addn1.
Qed.

Section Merge.

Variable op : rT -> rT -> rT.
Hypothesis (oppx : forall x : rT, op point x = x).
Hypothesis (opxp : forall x : rT, op x point = x).

Fixpoint mergesub (mergetrie : trie -> trie -> trie) sub1 sub2 {struct sub1} :=
  match sub1 with
  | h1 :: s1 => match sub2 with
                | h2 :: s2 => mergetrie h1 h2 ::: (mergesub mergetrie s1 s2)
                | [::] => sub1
                end
  | [::] => sub2
  end.

Fixpoint mergetrie tr1 tr2 {struct tr1} :=
  let: Trie (x1, ch1) := tr1 in
  let: Trie (x2, ch2) := tr2 in
  Trie (op x1 x2, mergesub mergetrie ch1 ch2).

Lemma mergesub_nil mergetrie s : mergesub mergetrie s [::] = s.
Proof. by case: s. Qed.
Lemma merge_trieempty t : mergetrie t emptytrie = t.
Proof. by case: t => [[x[|s0 s]]] /=; rewrite opxp. Qed.
Lemma merge_emptytrie t : mergetrie emptytrie t = t.
Proof. by case: t => [[x[|s0 s]]] /=; rewrite oppx. Qed.
Lemma nth_mergesub s1 s2 i :
  nth emptytrie (mergesub mergetrie s1 s2) i =
    mergetrie (nth emptytrie s1 i) (nth emptytrie s2 i).
Proof.
elim: s1 s2 i => [s2 i |s01 s1 IHs1] /=; first by rewrite nth_nil merge_emptytrie.
case=> [|s02 s2] i /=; first by rewrite nth_nil merge_trieempty.
by rewrite nth_consn; case: i => [|i] /=.
Qed.

Lemma normal_mergetrie tr1 tr2 :
  normal tr1 -> normal tr2 -> normal (mergetrie tr1 tr2).
Proof.
pose Ps (s : seq trie) := normals s ->
  forall s2, normals s2 -> normals (mergesub mergetrie s s2).
apply/(rectrie _ Ps): tr1 tr2; rewrite {}/Ps //.
  move=> t s Ht Hs nors [| s02 s2]; first by rewrite mergesub_nil.
  case/normals_consK : nors => nort nors.
  case/normals_consK => nors02 nors2 /=.
  by apply: normals_consn; [exact: Ht | exact: Hs].
by move=> s IHs /= x [[t s2]] nors /=; exact: IHs.
Qed.
Canonical merge_ntrie (tr1 tr2 : ntrie) :=
  NTrie _ (normal_mergetrie _ _ (ntrieP tr1) (ntrieP tr2)).

Lemma get_mergetrie tr1 tr2 v :
  gettrie (mergetrie tr1 tr2) v = op (gettrie tr1 v) (gettrie tr2 v).
Proof.
pose Ps (s1 : seq trie) := forall s2 v i,
  gettrie (nth emptytrie (mergesub mergetrie s1 s2) i) v =
    op (gettrie (nth emptytrie s1 i) v) (gettrie (nth emptytrie s2 i) v).
apply/(rectrie _ Ps): tr1 tr2 v; rewrite {}/Ps /=.
- by move=> s2 v i; rewrite !nth_nil get_emptytrie oppx.
- by move=> t s Ht Hs [|s20 s2] v [|i]; rewrite ?get_emptytrie ?opxp ?nth_consn /=.
by move=> s IHs /= x [[y s']] [|v0 v] /=.
Qed.

Lemma mergetrieC : commutative op -> commutative mergetrie.
Proof.
move=> opC.
pose Ps (s1 : seq trie) : Type := forall s2,
    mergesub mergetrie s1 s2 = mergesub mergetrie s2 s1.
apply/(rectrie _ Ps); rewrite {}/Ps /=.
- by case.
- by move=> t s Ht Hs [|s20 s2]; rewrite //= Ht Hs.
by move=> s Hs x [[x2 ch2]]; rewrite /= opC Hs.
Qed.
Lemma mergetrieA :
  associative op -> {in normal & &, associative mergetrie }.
Proof.
move=> opA a b c anor bnor cnor.
apply/eqP/normal_eqP; repeat try apply normal_mergetrie => //.
by move=> v; rewrite !get_mergetrie opA.
Qed.

(*
Lemma mergetrieA : associative op -> associative mergetrie.
Proof.
move=> opA.
pose Ps (s1 : seq trie) : Type := forall s2 s3,
    mergesub mergetrie s1 (mergesub mergetrie s2 s3) =
      mergesub mergetrie (mergesub mergetrie s1 s2) s3.
apply/(rectrie _ Ps); rewrite {}/Ps //=.
  move=> t s Ht Hs [|s20 s2] [|s30 s3]; rewrite ?mergesub_nil //=.
  rewrite /consn /= !fun_if /= !if_arg /=.
  case: andP => /= [[/eqP Hs2s3 /eqP Hs2s30]|].
    move/(_ s20 s30): Ht; rewrite Hs2s30 merge_trieempty => /[dup] Ht <-.
    move/(_ s2 s3): Hs; rewrite Hs2s3 mergesub_nil => /[dup] Hs <-.
    case: andP Hs Ht => [[/eqP -> /eqP -> -> -> /=]|].
      by case: s30 {Hs2s30} => [[x ch]]; rewrite oppx.
    

-Ht -Hs.
    rewrite Hs2s3 Hs2s30 mergesub_nil 
  case: andP => /= [[/eqP -> /eqP ->]|].
  
    move=> s Hs x [[x2 ch2]] [[x3 ch3]] /=.
rewrite /= opA.
Qed.
*)

End Merge.

End Defs.
