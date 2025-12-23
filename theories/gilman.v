From Corelib Require Import Setoid.
From HB Require Import structures.
From Stdlib Require Import Znat BinIntDef Uint63 Ring Ring63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_boot all_order.

(* Workaround for MathComp / PArray notation incompatibilities *)
Notation "t .[ i ]" := (get t i).
Notation "t .[ i <- a ]" := (set t i a)
  (at level 1, left associativity, format "t .[ i <- a ]").


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import factor int_seq array present rewcert inttrie.

Local Open Scope uint63_scope.

Import Order.TTheory.


Lemma cons_nnil (T : eqType) (i : T) (u : seq T) : (i :: u == rev [::]) = false.
Proof. by apply/negP => /eqP. Qed.

Section RevMap.

Variables (T1 T2 : Type) (f : T1 -> T2).

Definition revmap := foldl (fun s x => f x :: s).

Lemma revmapE acc s : revmap acc s = rev (map f s) ++ acc.
Proof.
rewrite /revmap; elim: s acc => [// | s0 s IHs] /= acc.
by rewrite IHs rev_cons -cats1 -catA.
Qed.

End RevMap.


Section TrieSize.

Context {T : eqType}.
Implicit Type t : @trie T.

Definition nbnodes t :=
  let fix aux t := match t with
    | Trie x a =>
        if length a == 0 then 0%N
        else (foldl_array (fun res t0 => res + aux t0)%N 0%N a).+1
    | Empty => 0%N
    end in aux t.

Definition nbnodes_int t :=
  let fix aux t := match t with
    | Trie x a =>
        if length a == 0 then 0
        else succ (foldl_array (fun res t0 => res + (aux t0)) 0 a)
    | Empty => 0
    end in aux t.

Definition nbnodes_overflow t :=
  let fix aux t := match t with
    | Trie x a =>
        if length a == 0 then C0 0
        else succov
          (foldl_array (fun res t0 => addov res (aux t0)) (C0 0) a)
    | Empty => C0 0
    end in aux t.

Lemma nbnodes_intE t :
  ~~ overflow (nbnodes_overflow t) -> nbnodes_int t = nbnodes_overflow t.
Proof.
rewrite /nbnodes_overflow /nbnodes_int.
set aux_ov := (X in X t); set aux := (X in (X t) = _ ).
move: t; apply: indtrie => [|a _ IHtr x] //=; rewrite !foldl_arrayE.
move/(forall_mem_to_seq
        (fun t : trie T => ~~ _ (_ t) -> aux t = aux_ov t)) in IHtr.
case: eqP => // _.
move=> /succov_impl.
elim/last_ind: (to_seq a) IHtr => [//= | l t IHl] Ht /=.
rewrite !foldl_rcons => /[dup]/addov_impl[].
have /Ht : t \in rcons l t by rewrite mem_rcons inE eqxx.
have {Ht}/IHl : forall x, x \in l -> ~~ overflow (aux_ov x) -> aux x = aux_ov x.
  by move=> y yinl {}/Ht; apply; rewrite mem_rcons inE yinl orbT.
case: (foldl _) => // res /(_ is_true_true) Hfold + _ => /[apply] eqaux.
rewrite -succDl {}Hfold; case: (aux_ov t) eqaux => // i /= {i}<- _.
rewrite -[succc res]/(succov (C0 res)).
rewrite -[res +c aux t]/(addov (C0 res) (C0 (aux t))).
by rewrite !succovE addovE succDl.
Qed.

Lemma nbnodes_overflowE t :
  ~~ overflow (nbnodes_overflow t) -> to_nat (nbnodes_overflow t) = nbnodes t.
Proof.
rewrite /nbnodes_overflow /nbnodes.
set aux := (X in X t); set aux_ov := (X in _ = X t).
move: t; apply: indtrie => [|a Hdef IHtr x] //=; rewrite !foldl_arrayE.
move/(forall_mem_to_seq
        (fun t : trie T => ~~ _ (_ t) -> to_nat (aux t) = _ t)) in IHtr.
case: eqP => // _.
move=> /[dup]/to_nat_succovE -> /succov_impl H; congr _.+1.
elim/last_ind: (to_seq a) IHtr H => [//= | l t IHl] Ht /=.
rewrite !foldl_rcons => /[dup]/addov_impl[nov1 nov2].
move=> /to_nat_addovE->; rewrite Ht //{nov2}; last by rewrite mem_rcons inE eqxx.
rewrite {}IHl // => t1 t1in.
by apply: Ht; rewrite mem_rcons inE t1in orbT.
Qed.

End TrieSize.


Section LHSPrefixes.

Variable trielen : int.
Hypothesis (maxlen : (0 < trielen <= max_length)%O).

Implicit Types (i j : int) (u v w : word int) (r : word int * word int)
  (P : pres int) (R : relat int) (tr : rewtrie).

Variable (R : relat int).
Hypothesis Rcorr : all_relwords R (<%O^~ trielen).

Lemma getsub_mktrie v :
  getsubtrie (mktrie trielen R) v =
    mktrie trielen [seq (drop (size v) r.1, r.2) | r <- R & prefix v r.1].
Proof.
case: v => [| v0 v] /=.
  suff -> : [seq (drop 0 r.1, r.2) | r <- R & prefix [::] r.1] = R.
    by case: mktrie.
  rewrite (eq_filter (a2 := xpredT)); last by move=> [r1 r2]; apply: prefix0s.
  rewrite filter_predT (eq_map (g := id)) ?map_id // => -[r1 r2] /=.
  by rewrite drop0.
elim: R Rcorr => [| [r1 r2] R' IHR] //=.
case/andP => /andP[allr1 allr2 corrR].
rewrite /addpair /addtrie /= getsub_updatetrie //; last exact: is_flmktrie.
case: (boolP (prefix (v0 :: v) r1)) => [pref | _] /=; last exact: IHR.
by rewrite /addpair /addtrie /= IHR.
Qed.

Definition islhsprefix tr u :=
  if getsubtrie tr u is Trie x a then length a != 0 else false.

Lemma islhsprefixP u :
  reflect (exists r, [&& r \in R, prefix u r.1 & u != r.1])
    (islhsprefix (mktrie trielen R) u).
Proof.
rewrite /islhsprefix getsub_mktrie //.
apply (iffP idP).
  have : all (fun r => (r \in R) && (prefix u r.1)) [seq r <- R | prefix u r.1].
    by apply/allP => [/= [r1 r2]]; rewrite mem_filter /= => /andP[-> ->].
  elim: (filter _ _) => [//| /= [r1 r2] R' IHR] /=.
  case/andP => /andP[inR pref] {}/IHR; case: mktrie => [//= _| x a Hrec].
    case Hdrop : (drop (size u) r1) (prefix_drop_nil pref) => [// | i v] /= Heq.
    by move=> _; exists (r1, r2); rewrite /= inR pref /= Heq.
  rewrite /addpair /addtrie /=.
  case Hdrop : (drop (size u) r1) (prefix_drop_nil pref) => [// | i v] /= Heq.
  case: eqP Hrec => [_ _ _| /= _ /(_ is_true_true) + _ //].
  by exists (r1, r2); rewrite /= inR pref /= Heq.
case=> [[r1 r2] /and3P[/= rinR pref nequr1]].
elim: R rinR => [// |[s1 s2] R' IHR] /=.
  rewrite inE => /orP[/eqP[{s1}<- {s2}<- {IHR}] | ] /=.
  rewrite pref /= /addpair /addtrie /=.
  case Hdrop : (drop (size u) r1) (prefix_drop_nil pref) => [| i v] /= Heq.
    exfalso; move: Heq nequr1; rewrite eq_refl => /eqP ->.
    by rewrite eqxx.
  move=> {Heq}; case: mktrie => [| x a]/=.
    by rewrite length_set length_make_trielen // (negbTE (len_neq0 _)).
  case: eqP => [lena | /eqP/negbTE].
    by rewrite  !length_set length_make_trielen // (negbTE (len_neq0 _)).
  by rewrite length_set => ->.
move=> {}/IHR IHR; case: (prefix u s1) => //=.
rewrite /addpair /addtrie /=.
case Hdrop : (drop (size u) s1) => [// | i v] /=.
  by case: mktrie IHR.
case: mktrie {IHR} => [| x a]/=.
  by rewrite length_set length_make_trielen // (negbTE (len_neq0 _)).
case: eqP => [lena | /eqP/negbTE].
  by rewrite  !length_set length_make_trielen // (negbTE (len_neq0 _)).
by rewrite length_set => ->.
Qed.

Fixpoint trie_prefixes_rec rpre tr : seq (word int) :=
  match tr with
  | Trie x a =>
      if length a == 0 then [::]
      else rpre :: flatten
             [seq trie_prefixes_rec (g :: rpre)
                a.[g] | g <- [seq of_nat n | n <- iota 0 (to_nat (length a))]]
  | Empty => [::]
  end.
Definition trie_prefixes tr := [seq rev s | s <- trie_prefixes_rec [::] tr].

Fixpoint trie_prefixes_acc acc rpre tr : seq (word int) :=
    match tr with
    | Trie x a =>
        if length a == 0 then acc
        else foldint
               (fun g ac => trie_prefixes_acc ac (g :: rpre) a.[g])
               0 trielen (rev rpre :: acc)
    | Empty => acc
    end.
Definition trie_prefixes_fast tr := rev (trie_prefixes_acc [::] [::] tr).

Fixpoint trie_prefixes_array_rec resa_i rpre tr : array (seq int) * int :=
    match tr with
    | Trie x a =>
        if length a == 0 then resa_i
        else foldint
               (fun g ac => trie_prefixes_array_rec ac (g :: rpre) a.[g])
               0 (length a) (resa_i.1.[resa_i.2 <- rev rpre], succ resa_i.2)
    | Empty => resa_i
    end.
Definition trie_prefixes_array tr :=
  (trie_prefixes_array_rec (make (nbnodes_overflow tr) [::], 0) [::] tr).1.

Lemma trie_prefixes_array_rec2E ar_acc rpre tr :
  (trie_prefixes_array_rec ar_acc rpre tr).2 = ar_acc.2 + nbnodes_int tr.
Proof.
move: tr rpre ar_acc.
apply: indtrie => [| a _ IHa _] rpre [ar acc] //=; first by ring.
case: eqP => /= _; first by ring.
rewrite /foldl_array !foldintE succDr -succDl.
move: (succ acc) (ar.[_ <- _]) => {}acc {}ar.
apply (for_loop_rel_le_postcond (invar := fun k a b => a.2 = acc + b))
      => //=; last by ring.
move=> i [{}ar x y] [ar' x' y'] /= lti [eq1][{y'}<-] eqx; rewrite {}eqx in eq1.
have:= IHa _ lti (i :: rpre) (ar, acc + y).
rewrite eq1 /= => ->; by ring.
Qed.

(*
Lemma trie_prefixes_array_recE ar i rpre tr :
  is_fltrie trielen tr ->
  let: (res, resi) := trie_prefixes_array_rec (ar, i) rpre tr in
  (resi < length ar)%O ->
  trie_prefixes_acc (rev (take (to_nat i) (to_seq ar))) rpre tr =
    rev (take (to_nat resi) (to_seq res)).
Proof.
move: tr rpre ar i; apply: indtrie => [| a _ IHa _] rpre ar i //=.
case/(flarrayP maxlen) => [[-> //= | lena]] _ /=.
rewrite lena (negbTE (len_neq0 maxlen)) => flta.
rewrite !foldintE.
apply (for_loop_rel_le_postcond
         (invar := fun i sr ar =>
                     let: (res, resi) := ar in
                     (resi < length res)%O ->
                     sr = rev (take (to_nat resi) (to_seq res)))
      ) => //; first last.
- exact: le0x.
- move=> lti.
  apply: (eq_from_nth (x0 := [::])).
  + rewrite /= !size_rev !size_take size_to_seq /=.
- admit.
*)

Lemma trie_prefixes_acc_cat acc rpre tr :
  is_fltrie trielen tr ->
  trie_prefixes_acc acc rpre tr = trie_prefixes_acc [::] rpre tr ++ acc.
Proof.
move: tr rpre acc; apply: indtrie => [| a _ IHa _] rpre acc //=.
case/(flarrayP maxlen) => [[-> //= | lena]] _ /=.
rewrite lena (negbTE (len_neq0 maxlen)) => flta.
set body := (X in foldint X).
suff step s : foldint body 0 trielen s =
                foldint body 0 trielen [::] ++ s.
  by rewrite step [in RHS]step -catA /=.
rewrite !foldintE {acc}.
apply (for_loop_rel_le_postcond
         (invar := fun i a b => a = b ++ s)
         (postcond := fun a b => a = b ++ s)) => //.
move=> i {}x y c d lti [{c}<-] [{d}<-] {x}->.
move/(_ _ lti) : flta => flta.
by rewrite /body IHa ?lena // [in RHS]IHa ?lena // catA.
Qed.

Lemma trie_prefixes_accE acc rpre tr :
  is_fltrie trielen tr ->
  trie_prefixes_acc acc rpre tr =
    rev (map rev (trie_prefixes_rec rpre tr)) ++ acc.
Proof.
move: tr rpre acc; apply: indtrie => [| a _ IHa x] rpre acc //=.
case/(flarrayP maxlen) => [[-> //= | lena]] _ /=.
rewrite lena (negbTE (len_neq0 maxlen)) => flta.
apply foldint_ind; first last.
- by move: maxlen => /andP[/ltW].
- by rewrite to_nat0.
move=> i x0 lti {x0}->.
rewrite to_nat_succ; first last.
  move: lti; rewrite ltEint => /leq_ltn_trans; apply.
  exact: ltwBnat.
rewrite -addn1 iotaD add0n /=.
rewrite  !map_cat flatten_cat /= cats0 map_cat to_natK !rev_cons rev_cat.
move/(_ _ lti) : flta => flta; rewrite -IHa // ?lena //.
rewrite -!cats1 [LHS]trie_prefixes_acc_cat //.
by rewrite [in RHS]trie_prefixes_acc_cat // !catA.
Qed.

Lemma trie_prefixes_fastE tr :
  is_fltrie trielen tr -> trie_prefixes_fast tr = trie_prefixes tr.
Proof.
rewrite /trie_prefixes_fast => /trie_prefixes_accE ->.
by rewrite cats0 revK.
Qed.

Lemma nil_in_trie_prefixes x a :
  (length a != 0) = ([::] \in trie_prefixes (Trie x a)).
Proof.
rewrite /trie_prefixes /=; apply/idP/idP => [/negbTE -> /= |].
  by rewrite inE eqxx.
by case: eqP.
Qed.

Lemma trie_prefixes_recE rpre tr :
  trie_prefixes_rec rpre tr = [seq rev u ++ rpre| u <- trie_prefixes tr].
Proof.
rewrite /trie_prefixes; move: tr rpre.
apply: indtrie => [|a Hdef IHtr x] rpre //=.
case: eqP => // _; rewrite !map_cons revK /=; congr cons.
rewrite -!map_comp map_flatten; congr flatten.
rewrite -map_comp; apply eq_in_map => /= n; rewrite mem_iota add0n /= => ltn.
have /of_natK Hn : n < wBnat by apply: (ltn_trans ltn (lt_lenght_wB _)).
move: ltn; rewrite -{1}Hn -ltEint; move: (of_nat n) {Hn} => {}n ltn.
rewrite IHtr // (IHtr _ _ [:: n]) //.
rewrite -!map_comp; apply eq_map => u /=.
by rewrite !revK -catA cat1s.
Qed.

Lemma suffix_trie_prefixes_rec rpre tr u :
  u \in trie_prefixes_rec rpre tr -> suffix rpre u.
Proof.
by rewrite trie_prefixes_recE => /mapP[/= v _ ->]; apply: suffix_suffix.
Qed.

Lemma mem_trie_prefixesE x a (i : int) u :
  default a = Empty ->
  (i :: u \in trie_prefixes (Trie x a)) = (u \in trie_prefixes a.[i]).
Proof.
move=> defa.
rewrite {1}/trie_prefixes /=; case: (boolP (length a == 0)) => [/eqP|] lena /=.
  rewrite get_out_of_bounds; first last.
    by rewrite lena; apply: (ltx0 i).
  by rewrite /trie_prefixes defa.
rewrite inE cons_nnil /=.
rewrite -(revK (i :: u)) rev_cons (mem_map (can_inj revK)).
apply/flatten_mapP/idP => [[ /= j /mapP[/= n]] | uin].
  rewrite mem_iota /= add0n => ltnl eqi.
  have /of_natK : n < wBnat by apply (ltn_trans ltnl (lt_lenght_wB _)).
  rewrite -eqi => Hn; subst n => {eqi}.
  rewrite -cats1 trie_prefixes_recE => /mapP[/= v /[swap]].
  by move/(congr1 rev); rewrite !rev_cat /= !revK => [[-> ->]].
exists i.
  apply/mapP; exists (to_nat i); last by rewrite to_natK.
  rewrite mem_iota /= add0n -ltEint.
  apply: get_not_default_lt; apply/eqP; rewrite defa.
  by case: eqP uin => // ->.
rewrite -cats1 trie_prefixes_recE.
by apply/mapP; exists u.
Qed.


Section Sorted.

Import DefaultSeqLexiOrder.

Lemma catl_ltxiE u v w : (u ++ v < u ++ w)%O = (v < w)%O.
Proof.
elim: u => [| u0 u]; first by rewrite !cat0s.
by rewrite /= eqhead_ltxiE.
Qed.

Lemma ltxirev_trans : transitive (fun u v => rev u < rev v)%O.
Proof. by move=> y x z; apply: lt_trans. Qed.

Lemma trie_prefixes_rec_sorted rpre tr :
  sorted (fun u v => rev u < rev v)%O (trie_prefixes_rec rpre tr).
Proof.
move: tr rpre; apply: indtrie => //= a _ IH _ rpre.
case eqP => //= _.
have := leqnn (to_nat (length a)).
elim: {1 3}(to_nat (length a)) => [//| n IHn] ltn.
rewrite -(addn1) iotaD /= add0n !map_cat flatten_cat cat_path /= cats0.
rewrite {}IHn ?(ltnW ltn) //=.
rewrite (path_sortedE ltxirev_trans) {}IH; first last.
  rewrite ltEint of_natK //.
  exact/(ltn_trans ltn)/lt_lenght_wB.
rewrite andbT; apply/allP => /= u /suffix_trie_prefixes_rec.
rewrite -prefix_rev rev_cons -cats1 => /prefixP[/= suf ->].
case/lastP Hflat : (flatten _) => [|f fn] /=.
  by rewrite -{1}(cats0 (rev rpre)) -catA catl_ltxiE ltxi0s.
have : fn \in rcons f fn by rewrite mem_rcons inE eqxx.
rewrite last_rcons -{}Hflat => /flatten_mapP[/= i] /mapP[/= m].
rewrite mem_iota /= add0n => ltmn {i}->.
have {}ltmn : (of_nat m < of_nat n)%O.
  rewrite ltEint !of_natK //.
  exact/(ltn_trans ltn)/lt_lenght_wB.
  exact/(ltn_trans ltmn)/(ltn_trans ltn)/lt_lenght_wB.
move/suffix_trie_prefixes_rec.
rewrite -prefix_rev rev_cons -cats1 => /prefixP[/= s2] ->.
rewrite -!catA catl_ltxiE neqhead_ltxiE //.
by move: ltmn; rewrite lt_neqAle => /andP[].
Qed.
Lemma trie_prefixes_sorted tr : sorted <%O (trie_prefixes tr).
Proof. by rewrite /trie_prefixes sorted_map (trie_prefixes_rec_sorted _ _). Qed.

Lemma trie_prefixes_uniq tr : uniq (trie_prefixes tr).
Proof.
exact: (sorted_uniq lt_trans lt_irreflexive (trie_prefixes_sorted _)).
Qed.

Lemma in_prefixes_mktrieE u :
  (islhsprefix (mktrie trielen R) u) = (u \in trie_prefixes (mktrie trielen R)).
Proof.
rewrite /islhsprefix.
move: (mktrie trielen R) (is_flmktrie maxlen R) u.
apply: indtrie => [|a _ IHtr x] /= fla [|u0 u] //=.
  exact: nil_in_trie_prefixes.
case/(flarrayP maxlen): fla => /= lena defa flta.
rewrite mem_trie_prefixesE //.
case: (boolP (u0 < length a)%O) => [ltu0 | /negbTE]; first last.
  move/get_out_of_bounds ->; rewrite defa /= /trie_prefixes /=.
  by case u.
apply: (IHtr u0 ltu0); apply: flta.
apply: (Order.POrderTheory.lt_le_trans ltu0).
by move: lena => []->.
Qed.

Lemma prefixes_mktrieP u :
  reflect (exists r, [&& r \in R, prefix u r.1 & u != r.1])
    (u \in trie_prefixes (mktrie trielen R)).
Proof. by rewrite -in_prefixes_mktrieE; exact/islhsprefixP. Qed.

Lemma trie_prefixesE :
  trie_prefixes (mktrie trielen R) =
    sort <=%O (undup (flatten
                       [seq [seq take n r.1 | n <- iota 0 (size r.1)] | r <- R])).
Proof.
apply (irr_sorted_eq lt_trans lt_irreflexive (trie_prefixes_sorted _)).
  by rewrite sort_lt_sorted; apply: undup_uniq.
move=> u; rewrite mem_sort; apply: perm_mem.
apply: (uniq_perm (trie_prefixes_uniq _) (undup_uniq _)) => /= {}u.
rewrite mem_undup.
apply/prefixes_mktrieP/flatten_mapP => /= -[] [r1 r2].
  case/and3P => rinR /= prefu nequr1; exists (r1, r2) => //.
  move/prefixP: prefu => [/= suf eqr1]; subst r1.
  apply/mapP; exists (size u); last by rewrite take_size_cat.
  rewrite mem_iota /= add0n ltn_neqAle andbC {1}size_cat leq_addr /=.
  apply/contra: nequr1 => /eqP eqsz; apply/eqP.
  by rewrite -[RHS]take_size -eqsz take_size_cat.
move=> rinR /= /mapP[/= n]; rewrite mem_iota /= add0n => ltn {u}->.
exists (r1, r2); rewrite {}rinR prefix_take /=.
by apply/negP => /eqP/(congr1 size)/eqP; rewrite size_take ltn ltn_eqF.
Qed.

End Sorted.

Fixpoint trie_prefixes_pos_acc acc tr : int * (@trie int) :=
  match tr with
  | Trie x a =>
      if length a == 0 then (acc, Empty)
      else let: (newacc, resa) :=
             foldint (fun i acc_ar =>
                      let: (recacc, reca) := trie_prefixes_pos_acc acc_ar.1 a.[i] in
                      (recacc, acc_ar.2.[i <- reca]))
               0 (length a) (acc + 1, make trielen (@Empty int)) in
           (newacc, Trie (Some acc) resa)
  | Empty => (acc, Empty)
  end.
Definition trie_prefixes_length tr := (trie_prefixes_pos_acc 0 tr).1.
Definition trie_prefixes_pos tr := (trie_prefixes_pos_acc 0 tr).2.


(*
Definition loopseq := [seq of_nat n | n <- iota 0 (to_nat trielen)].
Fixpoint trie_prefixes_pos_acc acc tr : int * (@trie int) :=
  match tr with
  | Trie x a =>
      if length a == 0 then (acc, Empty)
      else let: (newacc, resa) :=
             foldl (fun acc_ar g =>
                      let: (recacc, reca) := trie_prefixes_pos_acc acc_ar.1 a.[g] in
                      (recacc, acc_ar.2.[g <- reca]))
               (acc + 1, make trielen (@Empty int)) loopseq in
           (newacc, Trie (Some acc) resa)
  | Empty => (acc, Empty)
  end.
Definition trie_prefixes_length tr := (trie_prefixes_pos_acc 0 tr).1.
Definition trie_prefixes_pos tr := (trie_prefixes_pos_acc 0 tr).2.
*)

(*
Lemma trie_prefixes_lengthE tr :
  is_fltrie trielen tr ->
  trie_prefixes_length tr = nbnodes_int (trie_prefixes_pos tr).
Proof.
rewrite /trie_prefixes_length /trie_prefixes_pos /=.
rewrite /nbnodes_int /nbnodes_generic; set nbnodes_aux := (X in _ = X _ _).
move: 0 => acc; move: tr acc.
apply: indtrie => [// | a _ IHa x] i /=.
case/(flarrayP maxlen) => [[-> // | lena]] _ flta.
rewrite /loopseq lena (negbTE (len_neq0 maxlen)) /=.
set updatei := foldl _ _.

have := leqnn (to_nat trielen).
elim: {1 3 4}(to_nat trielen) => [| n IHn] ltn.
  rewrite /= length_make_trielen // (negbTE (len_neq0 maxlen)) /= /loopseq.
  by elim: (map _ _) => [// | m0 m /= IHm]; last by rewrite get_make.
rewrite -(addn1) iotaD /= add0n !map_cat /= cats1 !foldl_rcons.
move: IHn; set rec := (foldl _ _ _) => /= /(_ (ltnW ltn)).
have: length rec.2 = trielen.
  rewrite /rec; have := @length_make_trielen int trielen maxlen.
  elim: (map _ _) (i + 1) (make _ _) => [//| m0 m IHm]/= j ma lenma.
  case: (trie_prefixes_pos_acc j a.[m0]) => szm0 am0 /=.
  by apply: IHm; rewrite length_set.
have ltnn : (of_nat n < length a)%O.
  rewrite lena ltEint of_natK //.
  by apply: (ltn_trans ltn); rewrite -lena; apply: lt_lenght_wB.
have := ltnn; rewrite lena => /flta.
move/(_ _ ltnn): IHa => /[apply] Heq.
case: rec => acc arec /= lenarec.
rewrite lenarec (negbTE (len_neq0 maxlen)) => ->.
set recn := (foldl _ _ _).
case: trie_prefixes_pos_acc (Heq recn) => recn1 arec1 /= {Heq recn1}->.
rewrite length_set lenarec (negbTE (len_neq0 maxlen)) {}/recn.
move: (succ i) => {acc}i.
rewrite /loopseq.
have := leqnn (to_nat trielen).
elim: {1 2 4 5}(to_nat trielen) ltn => [//| m IHm].
rewrite ltnS leq_eqVlt => /orP[/eqP {IHm m}<-|].
  rewrite -{-1}(addn1) iotaD /= add0n !map_cat /= cats1 !foldl_rcons.
  rewrite get_set_same; last by rewrite lenarec -lena.
  admit.
move=> /[dup] ltnm {}/IHm + /ltnW => /[apply].
rewrite -(addn1) iotaD /= add0n !map_cat /= cats1 !foldl_rcons => <-.

  
  elim: (to_nat trielen) => [//= |].


rewrite of_natK; last by admit.

have ltnn : (of_nat n < length arec)%O.
  rewrite lenarec ltEint of_natK //.
  by apply: (ltn_trans ltn); rewrite -lenarec; apply: lt_lenght_wB.
have := 


case: trie_prefixes_pos_acc => szn an /=.
rewrite length_set lenarec (negbTE (len_neq0 maxlen)).

rewrite IHa /=. rewrite IHn.

have ltnint : (of_nat n < trielen)%O.
  rewrite ltEint of_natK //.
  by apply: (ltn_trans ltn); rewrite -lena; apply: lt_lenght_wB.
rewrite cats1 foldl_rcons {}IHn ?(@ltnW n) // {}IHa ?lena //; last exact: flta.
by rewrite catA /= !rev_cons -rcons_cat map_cat rev_cat.
Qed.
*)

(*
Lemma trie_prefixes_lengthE tr :
  is_fltrie trielen tr ->
  size (trie_prefixes tr) = to_nat (trie_prefixes_length tr).
Proof.
move=> /[dup] /trie_prefixes_fastE <-.
rewrite /trie_prefixes_fast size_rev /trie_prefixes_length /=.
rewrite -(to_natK 0) to_nat0 -/(size ([::] : seq (word int))).
move: [::] [::] => rpre acc; move: tr rpre acc.
apply: indtrie => [// | a _ IHa x] rpre acc /=.
  rewrite of_natK //.

case/(flarrayP maxlen) => [[-> // | lena]] _ /=.
rewrite /loopseq lena (negbTE (len_neq0 maxlen)) => flta /=.
have := leqnn (to_nat trielen).
elim: {1 3 4}(to_nat trielen) => [//=| n IHn] ltn.
  rewrite addnC -to_nat1 -to_natD //; admit.
rewrite -(addn1) iotaD /= add0n !map_cat.
have ltnint : (of_nat n < trielen)%O.
  rewrite ltEint of_natK //.
  by apply: (ltn_trans ltn); rewrite -lena; apply: lt_lenght_wB.


*)

End LHSPrefixes.

Definition loopseq trielen := [seq of_nat n | n <- iota 0 (to_nat trielen)].

Module Example1.
Section Example1.

Definition P := make_pres [::0; 1]
  [::
   ([::1;0], [::0;1]);
   ([::0;0;0], [::0;1]);
   ([::1;1], [::1])
  ].

Let tr := mktrie (pres_trielen P) (prelat P).
Let preftr := trie_prefixes tr.
Let prefarray := trie_prefixes_array tr.
Let postr := trie_prefixes_pos (pres_trielen P) tr.
Let nbpref := trie_prefixes_length (pres_trielen P) tr.
Goal preftr = [:: [::]; [:: 0]; [:: 0; 0]; [:: 1]].
Proof. by []. Qed.

Goal to_seq prefarray = preftr.
Proof. by []. Qed.

Goal [seq gettrie postr p | p <- preftr] = [seq Some i | i <- loopseq nbpref].
Proof. by vm_compute. Qed.
Goal trie_prefixes_fast (pres_trielen P) tr = preftr.
Proof. by []. Qed.

End Example1.
End Example1.


Module Example2.
Section Example2.

Definition AB_AAAAAA_ABAABA :=
  make_pres [::0;1] [:: ([::0;0;0;0;0;0], [::0;1;0;0;1;0])].
Definition cert :=
  [::
       add_rel [::0;1;0;0;1;0] [::0;0;0;0;0;0]
         [:: RTriple 0 0 false];
       add_rel [::0;1;0;0;0;0;0;0;0] [::0;0;0;0;0;0;0;1;0]
         [:: RTriple 0 3 true;
             RTriple 1 0 true];
       rm_rel 0
         [:: RTriple 0 0 false]].
Definition P := @Pres _
                     (gen_cert (pgen AB_AAAAAA_ABAABA) cert)
                     (rel_cert (prelat AB_AAAAAA_ABAABA) cert)
                     is_true_true is_true_true.
Goal (prelat P) =
       [:: ([:: 0; 1; 0; 0; 1; 0], [:: 0; 0; 0; 0; 0; 0]);
        ([:: 0; 1; 0; 0; 0; 0; 0; 0; 0], [:: 0; 0; 0; 0; 0; 0; 0; 1; 0])].
Proof. by []. Qed.

Let tr := mktrie (pres_trielen P) (prelat P).
Let preftr := trie_prefixes tr.
Let prefarray := trie_prefixes_array tr.
Let prefpair := trie_prefixes_pos_acc (pres_trielen P) 0 tr.
Let nbpref := prefpair.1.
Let postr := prefpair.2.
Goal preftr =
       [:: [::]; [:: 0]; [:: 0; 1]; [:: 0; 1; 0]; [:: 0; 1; 0; 0];
        [:: 0; 1; 0; 0; 0]; [:: 0; 1; 0; 0; 0; 0];
        [:: 0; 1; 0; 0; 0; 0; 0]; [:: 0; 1; 0; 0; 0; 0; 0; 0];
        [:: 0; 1; 0; 0; 1]].
Proof. by []. Qed.

Goal to_seq prefarray = preftr.
Proof. by []. Qed.

Goal size preftr = nbnodes tr.
Proof. by vm_compute. Qed.
Goal nbnodes_overflow tr = C0 10.
Proof. by vm_compute. Qed.


Goal [seq gettrie postr p | p <- preftr] = [seq Some i | i <- loopseq nbpref].
Proof. by vm_compute. Qed.
Goal trie_prefixes_fast (pres_trielen P) tr = preftr.
Proof. by []. Qed.

Goal sorted <%O (preftr : seq (seqlexi _)).
Proof. by []. Qed.

End Example2.
End Example2.

Module Example3.
Section Largest.

Load "largest.v".

Let P := Eval vm_compute in present_final.
Let tr := mktrie (pres_trielen P) (prelat P).
Let preftr := trie_prefixes tr.
Let prefarray := trie_prefixes_array tr.
Let prefpair := trie_prefixes_pos_acc (pres_trielen P) 0 tr.
Let nbpref := prefpair.1.
Let postr := prefpair.2.

Goal size preftr = nbnodes tr.
Proof. by vm_compute. Qed.
Goal nbnodes_overflow tr = C0 465.
Proof. by vm_compute. Qed.

Goal [seq gettrie postr p | p <- preftr] = [seq Some i | i <- loopseq nbpref].
Proof. by vm_compute. Qed.
Goal trie_prefixes_fast (pres_trielen P) tr = preftr.
Proof. by vm_compute. Qed.
Goal sorted <%O (preftr : seq (seqlexi _)).
Proof. by vm_compute. Qed.

End Largest.
End Example3.

Require Import RennerB51.

Module Example4.
Section RennerB51.

Let P := Eval vm_compute in RennerB51_rws.
Let tr := mktrie (pres_trielen P) (prelat P).
Let preftr := trie_prefixes tr.
Let prefarray := trie_prefixes_array tr.
Let prefpair := trie_prefixes_pos_acc (pres_trielen P) 0 tr.
Let nbpref := prefpair.1.
Let postr := prefpair.2.

Goal size preftr = nbnodes tr.
Proof. by vm_compute. Qed.
Goal nbnodes_overflow tr = C0 895.
Proof. by vm_compute. Qed.

Goal to_seq prefarray = preftr.
Proof. by vm_compute. Qed.

Goal [seq gettrie postr p | p <- preftr] = [seq Some i | i <- loopseq nbpref].
Proof. by vm_compute. Qed.
Goal trie_prefixes_fast (pres_trielen P) tr = preftr.
Proof. by vm_compute. Qed.
Goal sorted <%O (preftr : seq (seqlexi _)).
Proof. by vm_compute. Qed.

End RennerB51.
End Example4.

(*
Definition is_reduced R :=
  all (fun rel => (size (rewrites R rel.1) == 1%N)
                  && (size (rewrites R rel.2) == 0%N)) R.
*)
