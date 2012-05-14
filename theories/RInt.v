Require Import Reals Div2.
Require Import seq Arithmetique Floor Total_sup Sup_seq.
Require Import ssreflect ssrbool eqtype.

(** * compatibilities with ssreflect *)
(** ** ssrnat *)
Lemma SSR_leq (n m : nat) : ssrbool.is_true (ssrnat.leq n m) <-> (n <= m)%nat.
Proof.
  set H := (@ssrnat.leP n m) ; case: H => H //=.
Qed.

Lemma SSR_minus (n m : nat) : ssrnat.subn n m = (n - m)%nat.
Proof.
  elim: m n => //.
Qed.

Lemma SSR_add (n m : nat) : ssrnat.addn n m = (n + m)%nat.
Proof.
  elim: m n => //.
Qed.

(** ** seq *)
Lemma rcons_ind {T : Type} (P : seq T -> Type) :
  P [::] -> (forall (s : seq T) (t : T), P s -> P (rcons s t)) -> forall s, P s.
Proof.
  move => H0 H.
  suff Hn : (forall (n : nat) (s : seq T), (size s = n)%nat -> P s).
  move => s ; apply (Hn (size s) s) => //.
  elim => [s Hs | n IHn s Hs].
  apply size0nil in Hs ; by rewrite Hs.
  suff : ({s' : seq T & {t' | s = rcons s' t'}}).
  case => s' [t' Hs'] ; rewrite Hs' in Hs |-* ; apply H, IHn.
  rewrite size_rcons in Hs ; apply eq_add_S => //.
  case: s (n) Hs => //.
  move => t s ; move: t ; elim: s => [t n0 Hn0 | t s IHs t0 n0 Hn0].
  exists [::] ; by exists t.
  case: n0 Hn0 => [Hn0| n0 Hn0].
  contradict Hn0 ; apply not_eq_S, sym_not_eq, O_S.
  case: (IHs t n0 (eq_add_S _ _ Hn0)) => s' [t' Hs'].
  exists (t0::s') ; exists t' ; rewrite rcons_cons -Hs' => //.
Qed.
Lemma rcons_dec {T : Type} (P : seq T -> Type) :
  (P [::]) -> (forall s t, P (rcons s t)) -> forall s, P s.
Proof.
  move => H0 H.
  suff Hn : (forall (n : nat) (s : seq T), (size s = n)%nat -> P s).
  move => s ; apply (Hn (size s) s) => //.
  case => [s Hs | n s Hs].
  apply size0nil in Hs ; by rewrite Hs.
  suff : ({s' : seq T & {t' | s = rcons s' t'}}).
  case => s' [t' Hs'] ; rewrite Hs' in Hs |-* ; apply H.
  case: s (n) Hs => //.
  move => t s ; move: t ; elim: s => [t n0 Hn0 | t s IHs t0 n0 Hn0].
  exists [::] ; by exists t.
  case: n0 Hn0 => [Hn0| n0 Hn0].
  contradict Hn0 ; apply not_eq_S, sym_not_eq, O_S.
  case: (IHs t n0 (eq_add_S _ _ Hn0)) => s' [t' Hs'].
  exists (t0::s') ; exists t' ; rewrite rcons_cons -Hs' => //.
Qed.

Lemma head_rcons {T : Type} (x0 : T) (s : seq T) (t : T) : head x0 (rcons s t) = head t s.
Proof.
  case: s x0 t => //.
Qed.
Lemma behead_rcons {T : Type} (s : seq T) (t : T) : 
  (0 < size s)%nat ->  behead (rcons s t) = rcons (behead s) t.
Proof.
  case: s t => // t Hi ; contradict Hi ; apply lt_n_O.
Qed.
Lemma size_rcons_pos {T : Type} (s : seq T) (t : T) : (0 < size (rcons s t))%nat.
Proof.
  rewrite size_rcons /= ; apply lt_O_Sn.
Qed.

Fixpoint belast {T : Type} (s : seq T) :=
  match s with
    | [::] | [:: _] => [::]
    | h :: s => h :: (belast s)
  end.

Lemma behead_rev {T : Type} (s : seq T) : behead (rev s) = rev (belast s).
Proof.
  case: s => // t s ; elim: s t => // t s IHs t0.
  rewrite rev_cons behead_rcons ?IHs ?size_rev -?rev_cons //= ; by apply lt_0_Sn.
Qed.

Lemma size_unzip1 {T T0 : Type} (s : seq (T * T0)) : size (unzip1 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
Lemma size_unzip2 {T T0 : Type} (s : seq (T * T0)) : size (unzip2 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.

(** ** Order *)

Fixpoint sorted {T : Type} (Ord : T -> T -> Prop) (s : seq T) :=
  match s with
    | [::] | [:: _] => True
    | h0 :: (h1 :: t1) as t0 => Ord h0 h1 /\ sorted Ord t0
  end.

Lemma sorted_nth {T : Type} (Ord : T -> T -> Prop) (s : seq T) :
  sorted Ord s <-> (forall i : nat,
    (i < Peano.pred (size s))%nat -> forall x0 : T, Ord (nth x0 s i) (nth x0 s (S i))).
Proof.
  case: s.
  split => // _ i Hi ; contradict Hi ; apply lt_n_O.
  move => t s ; elim: s t => [ t | t s IHs t0] ; split => // H.
  move => i Hi ; contradict Hi ; apply lt_n_O.
  case => [| i] Hi x0 ; simpl in Hi.
  apply H.
  case: (IHs t) => {IHs} IHs _ ;
  apply (IHs (proj2 H) i (lt_S_n _ _ Hi) x0).
  split.
  apply (H O (lt_0_Sn _) t).
  case: (IHs t) => {IHs} _ IHs.
  apply: IHs => i Hi x0 ; apply: (H (S i)) ; simpl ; apply lt_n_S, Hi.
Qed.

Lemma sorted_rcons {T : Type} (Ord : T -> T -> Prop) (s : seq T) (t1 t0 : T) :
  sorted Ord (rcons (rcons s t1) t0) <-> sorted Ord (rcons s t1) /\ Ord t1 t0.
Proof.
  split => H.
(* -> *)
  move: ((proj1 (sorted_nth Ord _)) H) => {H} H ; rewrite ?size_rcons in H ; split.
  apply sorted_nth => i Hi x0 ; rewrite ?size_rcons in Hi ; simpl Peano.pred in Hi, H.
  have : nth x0 (rcons s t1) i = nth x0 (rcons (rcons s t1) t0) i.
  have: (ssrnat.leq (S i) (size (rcons s t1))).
  rewrite SSR_leq size_rcons ; by apply le_n_S, lt_le_weak.
  rewrite (nth_rcons _ _ t0) ; case: (ssrnat.leq (S i) (size (rcons s t1))) => // H'.
  move => -> ; have : nth x0 (rcons s t1) (S i) = nth x0 (rcons (rcons s t1) t0) (S i).
  have: (ssrnat.leq (S (S i)) (size (rcons s t1))).
  rewrite SSR_leq size_rcons ; by apply le_n_S, lt_le_S.
  rewrite (nth_rcons _ _ t0) ; case: (ssrnat.leq (S (S i)) (size (rcons s t1))) => // H'.
  move => -> ; apply H, lt_trans with (1 := Hi), lt_n_Sn.
  have: (t1 = nth t0 (rcons (rcons s t1) t0) (size s)) ; first
  elim: (s) => //.
  move => -> ; have Rw : (t0 = nth t0 (rcons (rcons s t1) t0) (S (size s))) ; first
  elim: (s) => //.
  rewrite {3}Rw ; apply H.
  simpl ; apply lt_n_Sn.
(* <- *)
  apply sorted_nth => i Hi x0.
  rewrite ?size_rcons in Hi ; simpl in Hi ; apply lt_n_Sm_le in Hi ;
  case: (le_lt_eq_dec _ _ Hi) => {Hi} Hi.
  rewrite ?(nth_rcons _ _ t0).
  have: (ssrnat.leq (S i) (size (rcons s t1))).
    rewrite size_rcons ; by apply SSR_leq, le_n_S, lt_le_weak.
  have: (ssrnat.leq (S (S i)) (size (rcons s t1))).
    rewrite size_rcons ; by apply SSR_leq, le_n_S, lt_le_S.
  case: (ssrnat.leq (S i) (size (rcons s t1))) => // ;
  case: (ssrnat.leq (S (S i)) (size (rcons s t1))) => // _ _.
  apply (sorted_nth Ord).
  apply H.
  rewrite size_rcons => //.
  rewrite Hi ; elim: (s) => //= ; apply H.
Qed.

Lemma sorted_le_rev (s : seq R) :
  sorted Rge (rev s) <-> sorted Rle s.
Proof.
  case: s => // ; move => t s ; elim: s t => // t s IHs t0 ; split => H.
  rewrite ?rev_cons in H ; apply sorted_rcons in H ; rewrite -rev_cons in H.
  split.
  apply Rge_le, H.
  apply IHs, H.
  rewrite ?rev_cons ; apply sorted_rcons ; rewrite -rev_cons ; split.
  apply IHs, H.
  apply Rle_ge, H.
Qed.

Lemma zip_cons {S T : Type} hs ht (s : seq S) (t : seq T) :
  zip (hs :: s) (ht :: t) = (hs,ht) :: zip s t.
Proof.
  by [].
Qed.
Lemma zip_rcons {S T : Type} (s : seq S) (t : seq T) hs ht : size s = size t ->
  zip (rcons s hs) (rcons t ht) = rcons (zip s t) (hs,ht).
Proof.
  elim: s t hs ht => [| hs s IHs] ; case => //= ht t hs' ht' Hs.
  rewrite IHs => // ; by apply eq_add_S.
Qed.

Lemma foldr_rcons {T T0 : Type} : forall (f : T0 -> T -> T) x0 s t, 
  foldr f x0 (rcons s t) = foldr f (f t x0) s.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0 t0 ;
  by rewrite IH.
Qed.
Lemma foldl_rcons {T T0 : Type} : forall (f : T -> T0 -> T) x0 s t, 
  foldl f x0 (rcons s t) = f (foldl f x0 s) t.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0 t0 ;
  by rewrite IH.
Qed.
Lemma foldr_rev {T T0 : Type} : forall (f : T0 -> T -> T) x0 s, 
  foldr f x0 (rev s) = foldl (fun x y => f y x) x0 s.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0.
  rewrite rev_cons foldr_rcons ; apply IH.
Qed.
Lemma fold_comm {T : Type} (f : T -> T -> T) x0 (s : seq T) :
  (forall x y, f x y = f y x) -> foldr f x0 s = foldl f x0 (rev s).
Proof.
  move => Hcomm ; move: x0.
  apply rcons_ind with (s := s) => {s} // s t IH x0.
  by rewrite foldr_rcons rev_rcons IH Hcomm.
Qed.

(** * SF_seq and StepFun *)

Lemma StepFun_bound {a b : R} (f : StepFun a b) :
  exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
  case: f => /= f [lx [ly [Hsort [Hhead [Hlast [Hsize Hval]]]]]];
  rename a into a0 ; rename b into b0 ; set a := Rmin a0 b0 ; set b := Rmax a0 b0 ;
  set Rl_max := fun x0 => fix f l := match l with 
    | RList.nil => x0 
    | RList.cons h t => Rmax h (f t)
  end ;
  set f_lx := (fix app l := match l with
    | RList.nil => RList.nil
    | RList.cons h t => RList.cons (f h) (app t)
  end) lx ;
  set M_f_lx := Rl_max (f 0) f_lx ;
  set M_ly := Rl_max 0 ly.
  exists (Rmax M_f_lx M_ly) => x [Hx Hx'].
  rewrite /M_f_lx /f_lx ;
  case: lx Hsort Hhead Hlast Hsize Hval {f_lx M_f_lx}.
(* lx = [::] *)
  move => _ _ _ H ; contradict H ; apply O_S.
  move => h l ; case: l h.
(* lx = [:: h] *)
  move => h _ Ha Hb _ _ ; simpl in Ha, Hb.
  rewrite /a -Ha in Hx ; rewrite /b -Hb in Hx'.
  rewrite (Rle_antisym _ _ Hx Hx') /= ; apply Rle_trans with (2 := RmaxLess1 _ _) ; 
  apply RmaxLess1.
(* lx = [:: h,h'::l] *)
  move => h l h' Hsort Hhead Hlast Hsize Hval.
  apply Rle_lt_or_eq_dec in Hx' ; case: Hx' => Hx'.
  have H : exists i : nat, (i < S (Rlength l))%nat /\
    (pos_Rl (RList.cons h' (RList.cons h l)) i) <= x 
    < (pos_Rl (RList.cons h' (RList.cons h l)) (S i)).
    rewrite /a -Hhead in Hx ; rewrite /b -Hlast in Hx'.
    elim: l h' h Hx Hx' Hsort {Hhead Hlast Hsize Hval} => [| h'' l IH] h' h Hx Hx' Hsort ; simpl in Hx, Hsort.
    case: (Rlt_le_dec x h) => H.
    exists O ; intuition.
    exists O => /= ; intuition.
    case: (Rlt_le_dec x h) => H.
    exists O => /= ; intuition.
    have H0 : ordered_Rlist (RList.cons h (RList.cons h'' l)).
    move => i Hi ; apply (Hsort (S i)) => /= ; apply lt_n_S, Hi.
    case: (IH _ _ H Hx' H0) => {IH} i Hi.
    exists (S i) ; split.
    simpl ; apply lt_n_S, Hi => /=.
    apply Hi.
  case: H => i [Hi [Ht Ht']].
  apply Rle_lt_or_eq_dec in Ht ; case: Ht => Ht.
  rewrite (Hval i Hi x).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  rewrite /M_ly ; case: (ly).
  apply Rle_refl.
  move => y ly' ; elim: ly' (i) y.
  move => i0 y ; case: i0 => //=.
  apply RmaxLess1.
  move => _; apply RmaxLess2.
  move => y ly' IH i0 y' ; case: i0.
  apply RmaxLess1.
  move => n ; apply Rle_trans with (1 := IH n y) ; apply RmaxLess2.
  split => //.
  rewrite -Ht ; apply Rle_trans with (2 := RmaxLess1 _ _).
  case: (i).
  apply RmaxLess1.
  move => n ; elim: n (h) (h') (l).
  move => h0 h'0 l0 ; apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
  move => n IH h0 h'0 l0.
  case: l0.
  apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess2.
  move => h''0 l0 ; apply Rle_trans with (1 := IH h''0 h0 l0), RmaxLess2.
  rewrite Hx' /b -Hlast.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  elim: (l) (h') (h) => [| h''0 l0 IH] h'0 h0.
  apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
  apply Rle_trans with (1 := IH h0 h''0), RmaxLess2.
Qed.

Lemma Riemann_integrable_bound (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
  move => pr ;
  case (pr (mkposreal _ Rlt_0_1)) => {pr} phi [psi [pr _]] ;
  case: (StepFun_bound phi) => M_phi H_phi ;
  case: (StepFun_bound psi) => M_psi H_psi ;
  exists (M_psi + M_phi) => x Hx.
  apply Rle_trans with (2 := Rplus_le_compat _ _ _ _ (H_psi _ Hx) (H_phi _ Hx)).
  have: (f x = (f x - phi x) + phi x) ; first by ring.
  move => -> ; apply Rplus_le_compat_r, Rle_trans with (1 := Rle_abs _), pr, Hx.
Qed.

(** ** SF_seq definition *)

Record SF_seq {T : Type} := mkSF_seq {SF_h : R ; SF_t : seq (R * T)}.
Implicit Arguments SF_h [T].
Implicit Arguments SF_t [T].
Implicit Arguments mkSF_seq [T].
Definition SF_lx {T : Type} (s : @SF_seq T) : seq R := (SF_h s)::(unzip1 (SF_t s)).
Definition SF_ly {T : Type} (s : SF_seq) : seq T := unzip2 (SF_t s).
Definition SF_make {T : Type} (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_seq :=
  mkSF_seq (head 0 lx) (zip (behead lx) ly).

Lemma SF_size_lx_ly {T : Type} (s : @SF_seq T) : size (SF_lx s) = S (size (SF_ly s)).
Proof.
  case: s => sh st ;
  rewrite /SF_lx /SF_ly /= ;
  elim: st => //= t s -> //.
Qed.

Lemma SF_seq_bij {T : Type} (s : @SF_seq T) :
  SF_make (SF_lx s) (SF_ly s) (SF_size_lx_ly s) = s.
Proof.
  case: s => sh st ; by rewrite /SF_make (zip_unzip st).
Qed.
Lemma SF_seq_bij_lx {T : Type} (lx : seq R) (ly : seq T)
  (Hs : size lx = S (size ly)) : SF_lx (SF_make lx ly Hs) = lx.
Proof.
  case: lx Hs => // x lx Hs ;
  rewrite /SF_make / SF_lx unzip1_zip //= ;
  apply SSR_leq, le_S_n ; rewrite -Hs => //.
Qed.
Lemma SF_seq_bij_ly {T : Type} (lx : seq R) (ly : seq T)
  (Hs : size lx = S (size ly)) : SF_ly (SF_make lx ly Hs) = ly.
Proof.
  case: lx Hs => // x lx Hs ;
  rewrite /SF_make / SF_ly unzip2_zip //= ;
  apply SSR_leq, le_S_n ; rewrite -Hs => //.
Qed.

Definition SF_nil {T : Type} (x0 : R) : @SF_seq T := mkSF_seq x0 [::].
Definition SF_cons {T : Type} (h : R*T) (s : SF_seq) :=
  mkSF_seq (fst h) ((SF_h s,snd h)::(SF_t s)).
Lemma SF_cons_dec {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P (SF_cons h s)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; case: st => [| h sf].
  apply Hnil.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf)) => {Hcons} ; 
  rewrite /SF_cons -surjective_pairing //=.
Qed.
Lemma SF_cons_ind {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P s -> P (SF_cons h s)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; elim: st sh => [sh |h sf IHst sh].
  apply Hnil.
  move: (IHst (fst h)) => {IHst} IHst.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf) IHst) => {Hcons} ; 
  rewrite /SF_cons -surjective_pairing //=.
Qed.
Definition SF_rcons {T : Type} (s : @SF_seq T) (t : R*T) :=
  mkSF_seq (SF_h s) (rcons (SF_t s) t).
Lemma SF_rcons_dec {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P (SF_rcons s t)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st ; apply rcons_dec => [| st t].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t).
Qed.
Lemma SF_rcons_ind {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P s -> P (SF_rcons s t)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st sh ;
  apply (rcons_ind (fun st => forall sh, P {| SF_h := sh; SF_t := st |})) => [sh | st t IHst sh].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t) => //.
Qed.

Lemma SF_lx_cons {T : Type} (h : R*T) (s : @SF_seq T) :
  SF_lx (SF_cons h s) = (fst h) :: (SF_lx s).
Proof.
  by [].
Qed.
Lemma SF_ly_cons {T : Type} (h : R*T) (s : @SF_seq T) :
  SF_ly (SF_cons h s) = (snd h) :: (SF_ly s).
Proof.
  by [].
Qed.
Lemma SF_lx_rcons {T : Type} (s : @SF_seq T) (h : R*T) :
  SF_lx (SF_rcons s h) = rcons (SF_lx s) (fst h).
Proof.
  case: s => sh st ; rewrite /SF_lx /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.
Lemma SF_ly_rcons {T : Type} (s : @SF_seq T) (h : R*T) :
  SF_ly (SF_rcons s h) = rcons (SF_ly s) (snd h).
Proof.
  case: s => sh st ; rewrite /SF_ly /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.

Definition SF_rev {T : Type} (s : @SF_seq T) :=
  mkSF_seq (head 0 (rev (SF_lx s))) (zip (behead (rev (SF_lx s))) (rev (SF_ly s))).
Lemma SF_rev_invol {T : Type} (s : @SF_seq T) :
  SF_rev (SF_rev s) = s.
Proof.
  move: s ; apply SF_cons_ind => [x0 | h s IHs] //=.
  rewrite -{2}IHs => {IHs}.
  case: h => x y ; case: s => sh st ; rewrite -(zip_unzip st) 
    /SF_rev /SF_lx /SF_ly /SF_cons /= 
    ?unzip1_zip ?unzip2_zip ?size_behead ?size_rev ; try by elim: st.
  rewrite !rev_cons !head_rcons !(behead_rcons _ _ (size_rcons_pos _ _)) !rev_rcons !revK /=.
  rewrite -!rev_cons /=.
  rewrite (rev_cons sh _) -headI rev_rcons revK zip_unzip.
  rewrite -rev_cons behead_rev revK /= ; case: st => //.
Qed.
Lemma SF_rev_cons {T : Type} (h : R*T) (s : @SF_seq T) :
  SF_rev (SF_cons h s) = SF_rcons (SF_rev s) h.
Proof.
  case: s => sh st ;
  rewrite /SF_rev /SF_cons /SF_rcons /SF_lx /SF_ly /=.
  rewrite !rev_cons ?head_rcons ?(behead_rcons _ _ (size_rcons_pos _ _)).
  rewrite zip_rcons.
  by rewrite -surjective_pairing.
  rewrite size_behead size_rcons ?size_rev size_unzip1 size_unzip2 => //.
Qed.
Lemma SF_rev_rcons {T : Type} (s : @SF_seq T) (t : R*T) :
  SF_rev (SF_rcons s t) = SF_cons t (SF_rev s).
Proof.
  rewrite -{1}(SF_rev_invol s) -SF_rev_cons SF_rev_invol => //.
Qed.

Lemma SF_lx_rev {T : Type} (s : @SF_seq T) : SF_lx (SF_rev s) = rev (SF_lx s).
Proof.
  apply SF_cons_ind with (s := s) => {s} // h s IHs ;
  by rewrite SF_rev_cons SF_lx_cons SF_lx_rcons IHs -rev_cons.
Qed.
Lemma SF_ly_rev {T : Type} (s : @SF_seq T) : SF_ly (SF_rev s) = rev (SF_ly s).
Proof.
  apply SF_cons_ind with (s := s) => {s} // h s IHs ;
  by rewrite SF_rev_cons SF_ly_cons SF_ly_rcons IHs -rev_cons.
Qed.

(** ** SF_size *)

Definition SF_size {T : Type} (s : @SF_seq T) := size (SF_t s).

Lemma SF_size_cons {T : Type} (h : R*T) (s : @SF_seq T) : SF_size (SF_cons h s) = S (SF_size s).
Proof.
  rewrite /SF_cons /SF_size //=.
Qed.

Lemma SF_size_rcons {T : Type} (s : @SF_seq T) (t : R*T) : SF_size (SF_rcons s t) = S (SF_size s).
Proof.
  rewrite /SF_rcons /SF_size size_rcons //=.
Qed.

Lemma SF_size_lx {T : Type} (s : @SF_seq T) : size (SF_lx s) = S (SF_size s).
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.
Lemma SF_size_ly {T : Type} (s : @SF_seq T) : size (SF_ly s) = SF_size s.
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.

Lemma SF_size_rev {T : Type} (s : @SF_seq T) : SF_size (SF_rev s) = SF_size s.
Proof.
  apply SF_cons_ind with (s := s) => {s} // h s IHs ;
  by rewrite SF_rev_cons SF_size_rcons SF_size_cons IHs.
Qed.

(** ** Order *)

Definition SF_sorted {T : Type} (Ord : R -> R -> Prop) (s : @SF_seq T) :=
  sorted Ord (SF_lx s).

Lemma SF_sorted_rev_0 {T : Type} (s : @SF_seq T) :
  SF_sorted Rle s <-> SF_sorted Rge (SF_rev s).
Proof.
  apply SF_cons_dec with (s := s) => {s} // h s.
  move: h ; apply SF_cons_ind with (s := s) => {s} [x0 h | h s IHs h'] ; split => H.
  rewrite SF_rev_cons /SF_sorted => /= ; case: H => /= H _ ; intuition.
  rewrite /SF_sorted => /= ; intuition ; apply Rge_le ; case: H => /= H _ //.
  move: H ; rewrite /SF_sorted !SF_rev_cons !SF_lx_rcons !SF_lx_cons ; case => [H H0] ; 
  apply sorted_rcons ; intuition.
  rewrite -SF_lx_rcons -SF_rev_cons ; by apply IHs.
  move: H ; rewrite /SF_sorted !SF_lx_cons !SF_rev_cons !SF_lx_rcons ; 
  move/sorted_rcons => [H H0] ; split ; intuition.
  apply (IHs h) ; by rewrite SF_rev_cons /SF_sorted SF_lx_rcons.
Qed.
Lemma SF_sorted_rev_1 {T : Type} (s : @SF_seq T) :
  SF_sorted Rge s <-> SF_sorted Rle (SF_rev s).
Proof.
  rewrite -{1}(SF_rev_invol s) ; split ;
  apply SF_sorted_rev_0.
Qed.

(** ** SF_nth **)

Definition SF_nth {T : Type} (x0 : R*T) (s : SF_seq) (i : nat) : R*T :=
  (nth (fst x0) (SF_lx s) i, nth (snd x0) (SF_ly s) i).

Lemma SF_eq_from_nth {T : Type} (x0 : R*T) (s1 s2 : SF_seq) :
  SF_size s1 = SF_size s2 ->
  (forall i, SF_nth x0 s1 i = SF_nth x0 s2 i) -> (s1 = s2).
Proof.
  move => Hs H ; rewrite -(SF_seq_bij s1) -(SF_seq_bij s2).
  have Rw: (SF_lx s1 = SF_lx s2) ; 
    [| move: (SF_size_lx_ly s1) ; rewrite Rw => {Rw}].
    apply eq_from_nth with (x0 := fst x0).
    by rewrite ?SF_size_lx Hs.
    move => i _ ; move: (H i) => {H} H.
    have: (nth (fst x0) (SF_lx s1) i = fst (SF_nth x0 s1 i)) ; 
      [by []|move => ->] ; by rewrite H.
  have: (SF_ly s1 = SF_ly s2) ; [| by move => ->].
    apply eq_from_nth with (x0 := snd x0).
    by rewrite ?SF_size_ly Hs.
    move => i _ ; move: (H i) => {H} H.
    have: (nth (snd x0) (SF_ly s1) i = snd (SF_nth x0 s1 i)) ; 
      [by []|move => ->] ; by rewrite H.
Qed.

Lemma SF_nth_cons {T : Type} x0 (h : R*T) (s : SF_seq) (i : nat) :
  SF_nth x0 (SF_cons h s) (S i) = SF_nth x0 s i.
Proof.
  rewrite /SF_nth //=.
Qed.

(** ** SF_map *)



Definition SF_map {T T0 : Type} (f : T -> T0) (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (map (fun x => (fst x,f (snd x))) (SF_t s)).

(** ** SF_fun definition *)

Fixpoint SF_fun_aux {T : Type} (s : seq (R*T)) (x0 : T) (x : R) :=
  match s with
    | (hx,hy)::s => 
      match (Rlt_dec x hx) with
        | left _ => hy
        | right _ => SF_fun_aux s x0 x
      end
    | _ => x0
  end.
Definition SF_fun {T : Type} (s : @SF_seq T) (x0 : T) (x : R) :=
  SF_fun_aux ((SF_h s,x0)::SF_t s) x0 x.

Lemma SF_fun_incr {T : Type} (s : @SF_seq T) (x0 : T) (x : R) (i : nat) :
  SF_sorted Rle s -> (i < SF_size s)%nat -> 
  nth 0 (SF_lx s) i <= x < nth 0 (SF_lx s) (S i) -> SF_fun s x0 x = nth x0 (SF_ly s) i.
Proof.
  move: s x0 ; elim: i.
(* i = 0 *)
  move => s ; apply SF_cons_dec with (s := s) => {s} //=.
(* s = SF_nil *)
  move => x0 x1 _ H ; contradict H ; apply lt_n_O.
(* s = SF_cons _ _ *)
  move => h s x0 _ _ Hx ; rewrite /SF_fun /=.
  case: (Rlt_dec x (fst h)) => Hx1.
  contradict Hx1 ; apply Rle_not_lt, Hx.
  case: (Rlt_dec x (SF_h s)) => // Hx2.
  contradict Hx2 ; apply Hx.
(* i = S _ *)
  move => i IHi s ; apply SF_cons_dec with (s := s) => {s} //=.
(* s = SF_nil *)
  move => x0 x1 _ H ; contradict H ; apply lt_n_O.
(* s = SF_cons _ _ *)
  move => h s x0 Hsort ; rewrite SF_size_cons => Hs Hx.
  rewrite -IHi /SF_fun /=.
  case: (Rlt_dec x (fst h)) => Hx1.
  contradict Hx1 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx).
  elim: (i) Hs => /= [ Hs | n IHn Hs].
  apply Hsort.
  apply Rle_trans with (r2 := nth 0 (SF_h s :: unzip1 (SF_t s)) n).
  apply IHn, lt_trans with (2 := Hs), lt_n_Sn.
  apply (proj1 (sorted_nth Rle (SF_h s :: unzip1 (SF_t s)))) => /=.
  apply Hsort.
  case: (s) Hs ; rewrite /SF_size /= => sh st Hs ; rewrite size_unzip1 ; 
  apply lt_trans with (1 := lt_n_Sn _), lt_S_n, Hs.
  case: (Rlt_dec x (SF_h s)) => // Hx2 ; contradict Hx2 ; apply Rle_not_lt ; 
  apply Rle_trans with (2 := proj1 Hx).
  elim: (i) Hs => /= [ Hs | n IHn Hs].
  apply Rle_refl.
  apply Rle_trans with (r2 := nth 0 (SF_h s :: unzip1 (SF_t s)) n).
  apply IHn, lt_trans with (2 := Hs), lt_n_Sn.
  apply (proj1 (sorted_nth Rle (SF_h s :: unzip1 (SF_t s)))) => /=.
  apply Hsort.
  rewrite size_unzip1 ; apply lt_trans with (1 := lt_n_Sn _), lt_S_n, Hs.
  apply Hsort.
  apply lt_S_n, Hs.
  apply Hx.
Qed.

Lemma SF_fun_decr {T : Type} (s : @SF_seq T) (x0 : T) (x : R) (i : nat) :
  SF_sorted Rge s -> (i < SF_size s)%nat -> 
  nth 0 (SF_lx s) (S i) <= x < nth 0 (SF_lx s) i -> 
  SF_fun (SF_rev s) x0 x = nth x0 (SF_ly s) i.
Proof.
  move => Hs Hi Hx ; rewrite -{2}(SF_rev_invol s).
  set Hi' := (lt_le_S _ _ Hi).
  rewrite SF_ly_rev nth_rev ?SSR_minus ?SSR_leq SF_size_ly ?SF_ly_rev 
    SF_size_rev -?SF_ly_rev => //.
  apply SF_fun_incr.
  apply SF_sorted_rev_1, Hs.
  rewrite SF_size_rev ; apply lt_minus ; [apply lt_le_S, Hi|apply lt_O_Sn].
  rewrite minus_Sn_m -?SSR_minus ?ssrnat.subSS ?SSR_minus => //.
  rewrite SF_lx_rev ?nth_rev ?SSR_minus ?SSR_leq SF_size_lx !minus_Sn_m ; 
  first rewrite -?SSR_minus ?ssrnat.subn_subA ?SSR_minus ?SSR_add ?SSR_leq ?minus_plus ; 
  intuition.
Qed.

Lemma SF_fun_map {T T0 : Type} (f : T -> T0) (s : SF_seq) x0 :
  forall x, SF_fun (SF_map f s) (f x0) x = f (SF_fun s x0 x).
Proof.
  move => x ; rewrite /SF_fun ; case: s => s0 sl /=.
  case: (Rlt_dec x s0) => // H.
  elim: sl => [|[sx sy] sl IH] //=.
  case: (Rlt_dec x sx) => // H0.
Qed.

(** ** (seq R) and Rlist *)

Fixpoint seq2Rlist (s : seq R) :=
  match s with
    | [::] => RList.nil
    | h::t => RList.cons h (seq2Rlist t)
  end.
Fixpoint Rlist2seq (s : Rlist) : seq R :=
  match s with
    | RList.nil => [::]
    | RList.cons h t => h::(Rlist2seq t)
  end.

Lemma seq2Rlist_bij (s : Rlist) :
  seq2Rlist (Rlist2seq s) = s.
Proof.
  by elim: s => //= h s ->.
Qed.
Lemma Rlist2seq_bij (s : seq R) :
  Rlist2seq (seq2Rlist s) = s.
Proof.
  by elim: s => //= h s ->.
Qed.

Lemma size_compat (s : seq R) :
  Rlength (seq2Rlist s) = size s.
Proof.
  elim: s => // t s IHs /= ; by rewrite IHs.
Qed.

Lemma nth_compat (s : seq R) (n : nat) :
  pos_Rl (seq2Rlist s) n = nth 0 s n.
Proof.
  elim: s n => [n|t s IHs n] /= ;
  case: n => //=.
Qed.

Lemma sorted_compat (s : seq R) :
  sorted Rle s <-> ordered_Rlist (seq2Rlist s).
Proof.
  case: s => [| h s].
(* s = [::] *)
  split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
  elim: s h => [h | h s IHs h'].
(* s = [::_] *)
  split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
(* s = _::(_::_) *)
  split => H.
  case => [ /= | i] ; rewrite size_compat => Hi ; simpl in Hi.
  apply H.
  apply (proj1 (IHs h) (proj2 H) i) ; rewrite size_compat /= ; apply lt_S_n => //.
  split.
  apply (H O) ; rewrite size_compat /= ; apply lt_O_Sn.
  apply IHs => i ; rewrite size_compat /= => Hi ; apply (H (S i)) ; 
  rewrite size_compat /= ; apply lt_n_S, Hi.
Qed.

Lemma SF_sorted_compat {T : Type} (s : @SF_seq T) :
  SF_sorted Rle s <-> ordered_Rlist (seq2Rlist (SF_lx s)).
Proof.
  split => H ; apply sorted_compat => //.
Qed.

Lemma ad_SF_compat_le (s : SF_seq) (pr : SF_sorted Rle s) : 
  adapted_couple (SF_fun s 0) (head 0 (SF_lx s)) (last 0 (SF_lx s))
    (seq2Rlist (SF_lx s)) (seq2Rlist (SF_ly s)).
Proof.
(* head and last *)
  have H : ((head 0 (SF_lx s)) <= (last 0 (SF_lx s))).
    move: pr ; rewrite /SF_sorted ; case: s => sh st /=.
    case: (unzip1 st) ; intuition.
    rewrite (last_nth 0) /=.
    have H1 : (forall n, (n <= size s)%nat -> sh <= nth 0 (t::s) n).
      elim => // n IHn Hs.
      apply Rle_trans with (r2 := nth 0 (t :: s) n).
      apply IHn, le_trans with (2 := Hs), le_n_Sn.
      apply sorted_nth => //.
    apply H1 => //.
  rewrite /adapted_couple ?nth_compat ?size_compat ?nth0 ?nth_last 
  /Rmin /Rmax ?SF_size_lx ?SF_size_ly ;
  case: (Rle_dec (head 0 (SF_lx s)) (last 0 (SF_lx s))) => // {H} _ ; intuition.
(* sorted *)
  apply sorted_compat => //.
(* adapted *)
  rewrite ?nth_compat => x [Hx Hx'].
  apply SF_fun_incr => // ; split => // ; apply Rlt_le => //.
Qed.

Lemma ad_SF_compat_ge (s : @SF_seq R) (pr : SF_sorted Rge s) : 
  adapted_couple (SF_fun (SF_rev s) 0) (head 0 (SF_lx s)) (last 0 (SF_lx s))
    (seq2Rlist (SF_lx (SF_rev s))) (seq2Rlist (SF_ly (SF_rev s))).
Proof.
  apply StepFun_P2.
  have: (last 0 (SF_lx s) = head 0 (SF_lx (SF_rev s))) ; [| move => ->].
    rewrite SF_lx_rev ; elim: (SF_lx s) (0) => // {s pr} t s IH x0.
    rewrite rev_cons head_rcons /= ; apply IH.
  have: (head 0 (SF_lx s) = last 0 (SF_lx (SF_rev s))) ; [| move => ->].
    rewrite SF_lx_rev ; elim: (SF_lx s) (0) => // {s pr} t s IH x0.
    by rewrite rev_cons last_rcons /=.
  by apply ad_SF_compat_le, SF_sorted_rev_1.
Qed.

Lemma is_SF_compat_le (s : @SF_seq R) (pr : SF_sorted Rle s) : 
  IsStepFun (SF_fun s 0) (head 0 (SF_lx s)) (last 0 (SF_lx s)).
Proof.
  exists (seq2Rlist (SF_lx s)) ; exists (seq2Rlist (SF_ly s)).
  apply ad_SF_compat_le, pr.
Qed.

Lemma is_SF_compat_ge (s : @SF_seq R) (pr : SF_sorted Rge s) : 
  IsStepFun (SF_fun (SF_rev s) 0) (head 0 (SF_lx s)) (last 0 (SF_lx s)).
Proof.
  exists (seq2Rlist (SF_lx (SF_rev s))) ; exists (seq2Rlist (SF_ly (SF_rev s))).
  apply ad_SF_compat_ge, pr.
Qed.

Definition SF_compat_le (s : @SF_seq R) (pr : SF_sorted Rle s) : 
  StepFun (head 0 (SF_lx s)) (last 0 (SF_lx s)) := 
  mkStepFun (is_SF_compat_le s pr).
Definition SF_compat_ge (s : @SF_seq R) (pr : SF_sorted Rge s) : 
  StepFun (head 0 (SF_lx s)) (last 0 (SF_lx s)) := 
  mkStepFun (is_SF_compat_ge s pr).

(** * Build sequences *)

(** ** sequence ly : partition of [a,b] *)

Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1%nat
    | S n => (2 * pow2 n)%nat
  end.

Lemma pow2_INR (n : nat) : INR (pow2 n) = 2^n.
Proof.
  elim: n => //= n IH ;
  rewrite ?plus_INR ?IH /= ; field.
Qed.

Definition RInt_part (a b : R) (n : nat) : seq R := 
  mkseq (fun i => a + (INR i) * (b - a) / (2^n)) (S (pow2 n)).

Lemma RInt_part_bound (a b : R) (n : nat) : 
  RInt_part a b n = rev (RInt_part b a n).
Proof.
  apply (@eq_from_nth R 0) ; rewrite ?size_rev ?size_mkseq => // ;
  move => i Hi ; apply SSR_leq in Hi.
  rewrite nth_rev ?SSR_leq ?SSR_minus ?size_mkseq => //.
  rewrite ?nth_mkseq ?SSR_leq => //.
  rewrite minus_INR ?S_INR ?pow2_INR => // ; field.
  apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
  apply INR_le ; rewrite ?S_INR minus_INR ?S_INR ?pow2_INR => //.
  ring_simplify ;
  apply Rplus_le_compat_r ; rewrite -{2}(Rplus_0_r (2^n)) ;
  apply Rplus_le_compat_l, Ropp_le_cancel ; rewrite Ropp_0 Ropp_involutive ;
  apply pos_INR.
Qed.

Lemma RInt_part_nat_0 (a b : R) (n : nat) (x : R) : (a <= x < b)
  -> { i : nat | nth 0 (RInt_part a b n) i <= x < nth 0 (RInt_part a b n) (S i) /\ (i < pow2 n)%nat}.
Proof.
  move => Hx ; have Hab : (a < b) ; [apply Rle_lt_trans with (r2 := x) ; intuition|].
(* a <= x < b *)
  case: Hx => Hx Hx'.
  case: (nfloor_ex ((2^n)/(b - a) * (x - a))) => [| i Hi].
  apply Rmult_le_pos ; [apply Rdiv_le_pos ; 
  [apply Rlt_le, pow_lt, Rlt_R0_R2|by apply Rlt_Rminus]|apply (Rminus_le_0 a x)] ;
  apply Hx.
  exists i ; rewrite ?nth_mkseq ; try apply SSR_leq.
  split.
  have : (x = a + ((2^n)/(b - a) * (x - a)) * (b-a)/(2^n)).
  field ; split.
  by apply Rgt_not_eq, Rlt_Rminus.
  apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
  move => -> ; split.
  apply Rplus_le_compat_l, Rmult_le_compat_r ;
  [apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2 |
  apply Rmult_le_compat_r ; intuition ;
  by apply Rlt_le, Rlt_Rminus]. 
  apply Rplus_lt_compat_l, Rmult_lt_compat_r ;
  [ apply Rinv_0_lt_compat, pow_lt, Rlt_R0_R2 | 
  apply Rmult_lt_compat_r ; [by apply Rlt_Rminus|
  rewrite (S_INR i) ; intuition]].
  apply INR_lt, (Rle_mult_Rlt (/(b-a)*(x-a))).
  rewrite pow2_INR ; apply pow_lt, Rlt_R0_R2.
  rewrite (Rinv_l_sym (b-a)).
  apply Rmult_lt_compat_l.
  by apply Rinv_0_lt_compat, Rlt_Rminus.
  by apply Rplus_lt_compat_r.
  by apply Rgt_not_eq, Rlt_Rminus.
  rewrite -Rmult_assoc pow2_INR ; intuition.
  apply le_n_S, lt_le_S, INR_lt, (Rle_mult_Rlt (/(b-a)*(x-a))).
  rewrite pow2_INR ; apply pow_lt, Rlt_R0_R2.
  rewrite (Rinv_l_sym (b-a)).
  apply Rmult_lt_compat_l.
  by apply Rinv_0_lt_compat, Rlt_Rminus.
  by apply Rplus_lt_compat_r.
  by apply Rgt_not_eq, Rlt_Rminus.
  rewrite -Rmult_assoc pow2_INR ; intuition.
  apply le_n_S, INR_le, Rlt_le, (Rle_mult_Rlt (/(b-a)*(x-a))).
  rewrite pow2_INR ; apply pow_lt, Rlt_R0_R2.
  rewrite (Rinv_l_sym (b-a)).
  apply Rmult_lt_compat_l.
  by apply Rinv_0_lt_compat, Rlt_Rminus.
  by apply Rplus_lt_compat_r.
  by apply Rgt_not_eq, Rlt_Rminus.
  rewrite -Rmult_assoc pow2_INR ; intuition.
Qed.

Lemma RInt_part_nat_1 (a b : R) (n : nat) (x : R) : (b <= x < a)
  -> { i : nat | nth 0 (RInt_part a b n) (S i) <= x <= nth 0 (RInt_part a b n) i /\ (i < pow2 n)%nat }.
Proof.
  move => Hx ;
  case: (RInt_part_nat_0 _ _ n x Hx) => i [Hi Hin].
  rewrite RInt_part_bound in Hi => //.
  rewrite nth_rev size_mkseq ?SSR_minus in Hi ; [ | by apply SSR_leq, le_n_S, lt_le_weak].
  rewrite nth_rev size_mkseq ?ssrnat.subSS ?SSR_minus in Hi ; 
  [ | by apply SSR_leq, lt_le_S, lt_n_S].
  rewrite -minus_Sn_m in Hi ; [ | by apply lt_le_S].
  exists (pow2 n - S i)%nat ; intuition.
Qed.

Lemma RInt_part_sorted_0 (a b : R) (n : nat) : (a <= b) -> sorted Rle (RInt_part a b n).
Proof.
  move => Hab ; apply sorted_compat => i ; 
  rewrite ?nth_compat size_compat size_mkseq => Hi ; simpl in Hi.
  rewrite ?nth_mkseq ?SSR_leq.
  rewrite -(Rplus_0_r (a + INR i * (b - a) / (2^n))) ;
  have: (a + INR (S i) * (b - a) / (2^n) = 
    (a + INR i * (b - a) / (2^n) + (b-a)/(2^n))).
    rewrite S_INR ; field ;
    apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
  move => -> ; apply Rplus_le_compat_l, Rmult_le_pos.
  by apply (Rminus_le_0 a b).
  apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
  by apply le_n_S, lt_le_S.
  by apply le_n_S, lt_le_weak.
Qed.
Lemma RInt_part_sorted_1 (a b : R) (n : nat) : (b <= a) -> sorted Rge (RInt_part a b n).
Proof.
  move => Hab ; 
  rewrite (RInt_part_bound _ _ _ ) ;
  by apply sorted_le_rev, RInt_part_sorted_0.
Qed.

(** ** sequences lx *)

(** *** Values *)

Definition SF_val_ly (f : R -> R) (a b : R) (n : nat) : seq R :=
  belast (map f (RInt_part a b n)).

Lemma SF_val_size (f : R -> R) (a b : R) (n : nat) :
  size (RInt_part a b n) = S (size (SF_val_ly f a b n)).
Proof.
  rewrite /SF_val_ly.
  have: (0 < size (RInt_part a b n))%nat ; 
  [rewrite size_mkseq ; apply lt_O_Sn|] ;
  case: (RInt_part a b n) => // {a b n} [Hs | t s _].
  contradict Hs ; apply lt_n_O.
  elim: s t => //= t s IH t0 ; by rewrite (IH t).
Qed.

Definition SF_val_seq (f : R -> R) (a b : R) (n : nat) : SF_seq := 
  SF_make (RInt_part a b n) (SF_val_ly f a b n) (SF_val_size f a b n).

Lemma ad_SF_val_fun (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (SF_fun (SF_val_seq f a b n) 0) a b 
      (seq2Rlist (RInt_part a b n)) (seq2Rlist (SF_val_ly f a b n)))
  /\ (~(a <= b) -> adapted_couple (SF_fun (SF_rev (SF_val_seq f a b n)) 0) a b 
      (seq2Rlist (rev (RInt_part a b n))) (seq2Rlist (rev (SF_val_ly f a b n)))).
Proof.
  have : SF_lx (SF_val_seq f a b n) = RInt_part a b n ; 
    [apply SF_seq_bij_lx | move => <-].
  have : SF_ly (SF_val_seq f a b n) = SF_val_ly f a b n ;
    [apply SF_seq_bij_ly | move => <-].
  have : head 0 (SF_lx (SF_val_seq f a b n)) = a ;
    [rewrite SF_seq_bij_lx -nth0 /= ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2 |
    move => {3 8}<-].
  have : last 0 (SF_lx (SF_val_seq f a b n)) = b ;
    [rewrite SF_seq_bij_lx -nth_last size_mkseq nth_mkseq //= pow2_INR ;
    field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2|
    move => {4 10}<-].
  case: (Rle_dec a b) => Hab ; split => // _.
  apply ad_SF_compat_le ; rewrite /SF_sorted SF_seq_bij_lx ;
  by apply RInt_part_sorted_0.
  apply Rnot_le_lt in Hab ; rewrite  -SF_lx_rev -SF_ly_rev ; 
  apply ad_SF_compat_ge ; rewrite /SF_sorted SF_seq_bij_lx ;
  by apply RInt_part_sorted_1, Rlt_le.
Qed.

Definition SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  case : (Rle_dec a b) => Hab.
  exists (SF_fun (SF_val_seq f a b n) 0) ;
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
  exists (SF_fun (SF_rev (SF_val_seq f a b n)) 0) ;
  exists (seq2Rlist (rev (RInt_part a b n))) ;
  exists (seq2Rlist (rev (SF_val_ly f a b n))) ; by apply ad_SF_val_fun.
Defined.
Lemma SF_val_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (rev (RInt_part a b n))
  end.
Proof.
  rewrite /SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_val_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (SF_val_ly f a b n)
    | right _ => seq2Rlist (rev (SF_val_ly f a b n))
  end.
Proof.
  rewrite /SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.

(** *** Local sup and inf *)

Lemma ex_Im_fct (f : R -> R) (a b : R) : 
  exists x, (fun y => exists x, y = f x /\ Rmin a b <= x <= Rmax a b) x.
Proof.
  exists (f a) ; exists a ; split => // ; by apply Rmin_Rmax_l.
Qed.

Definition Sup_fct (f : R -> R) (a b : R) : Rbar :=
  (Lub_Rbar_ne (fun y => exists x, y = f x /\ Rmin a b <= x <= Rmax a b) (ex_Im_fct f a b)).
Definition Inf_fct (f : R -> R) (a b : R) : Rbar :=
  (Glb_Rbar_ne (fun y => exists x, y = f x /\ Rmin a b <= x <= Rmax a b) (ex_Im_fct f a b)).

Lemma Sup_fct_bound (f : R -> R) (a b : R) :
  Sup_fct f a b = Sup_fct f b a.
Proof.
  apply Lub_Rbar_ne_eqset => x ; split => [[x0 Hx0]|[x0 Hx0]] ; exists x0 ; intuition ;
  try rewrite Rmin_comm => // ; try rewrite Rmax_comm => //.
Qed.
Lemma Inf_fct_bound (f : R -> R) (a b : R) :
  Inf_fct f a b = Inf_fct f b a.
Proof.
  apply Glb_Rbar_ne_eqset => x ; split => [[x0 Hx0]|[x0 Hx0]] ; exists x0 ; intuition ;
  try rewrite Rmin_comm => // ; try rewrite Rmax_comm => //.
Qed.

Lemma Sup_fct_le (f : R -> R) (a b : R) (x : R) : (Rmin a b <= x <= Rmax a b) ->
  Rbar_le (Finite (f x)) (Sup_fct f a b).
Proof.
  rewrite /Sup_fct /Lub_Rbar_ne ; 
  case: (ex_lub_Rbar_ne _ _) => /= Sf Hsf Hx ;
  apply Hsf ; exists x ; intuition.
Qed.
Lemma Inf_fct_le (f : R -> R) (a b : R) (x : R) : (Rmin a b <= x <= Rmax a b) ->
  Rbar_le (Inf_fct f a b) (Finite (f x)).
Proof.
  rewrite /Inf_fct /Glb_Rbar_ne ; 
  case: (ex_glb_Rbar_ne _ _) => /= If Hif Hx ;
  apply Hif ; exists x ; intuition.
Qed.

(** *** SF_seq of local sup *)

Fixpoint SF_sup_P_aux (f : R -> R) (P : seq R) x0 : seq (R*Rbar) :=
  behead (pairmap (fun x y => (y,Sup_fct f x y)) x0 P).
Definition SF_sup_P (f : R -> R) (P : seq R) x0 : SF_seq :=
  mkSF_seq (head x0 P) (SF_sup_P_aux f P (head x0 P)).

Lemma SF_sup_P_lx (f : R -> R) (P : seq R) (x0 : R) :
  SF_lx (SF_sup_P f P x0) = (head x0 P) :: (behead P).
Proof.
  case: P => //= h P ;
  have : (unzip1 (pairmap (fun x y : R => (y, Sup_fct f x y)) h P) = P) ;
  [| rewrite /SF_sup_P /SF_lx /= ; by move => ->] ;
  by elim: P h => {x0} //= h P -> h0.
Qed.
Lemma SF_sup_P_ly (f : R -> R) (P : seq R) (x0 : R) :
  SF_ly (SF_sup_P f P x0) = behead (pairmap (Sup_fct f) x0 P).
Proof.
  case: P => //= h P ; rewrite /SF_sup_P /SF_ly //= ;
  by elim: P h => {x0} //= h P -> h0.
Qed.

Lemma cons_SF_sup_P (f : R -> R) (h0 h1 : R) (P : seq R) (x0 : R) :
  SF_sup_P f (cons h0 (cons h1 P)) x0 = 
    SF_cons (h0,Sup_fct f h0 h1) (SF_sup_P f (cons h1 P) x0).
Proof.
  by [].
Qed.
Lemma rcons_SF_sup_P (f : R -> R) (P : seq R) (t1 t0 : R) (x0 : R) :
  SF_sup_P f (rcons (rcons P t1) t0) x0 = 
    SF_rcons (SF_sup_P f (rcons P t1) x0) (t0,Sup_fct f t1 t0).
Proof.
  elim: P => //= h P ; 
  have: (exists h1, exists P1, rcons P t1 = h1 :: P1) ; 
    [|case => h1 [P1 H1] ; rewrite H1 /=].
    case: P t1 => {t0 x0 f} [| t P] t1.
    exists t1 ; by exists [::].
    exists t ; by exists (rcons P t1).
  have: (exists h0, exists P0, rcons P1 t0 = h0 :: P0) ;
    [|case => h0 [P0 H0] ; rewrite H0 /=].
    case: (P1) t0 => [| t P1'] t0.
    exists t0 ; by exists [::].
    exists t ; by exists (rcons P1' t0).
  have: (SF_sup_P f [:: h, h1, h0 & P0] x0 =
    SF_cons (h,Sup_fct f h h1) (SF_sup_P f [::h1,h0& P0] x0)) ;
    [by []| by move => -> ->].
Qed.

Lemma nth_SF_sup_P (f : R -> R) (P : seq R) (x0 : R) (i : nat) : (S i < size P)%nat ->
  SF_nth (0,Finite 0) (SF_sup_P f P x0) i = (nth 0 P i,Sup_fct f (nth 0 P i) (nth 0 P (S i))).
Proof.
  move: i ; case: P => [| h P].
  move => i Hi ; by apply lt_n_O in Hi.
  elim: P h => /= [|h P IH] h0 i Hi ; apply lt_S_n in Hi.
  by apply lt_n_O in Hi.
  rewrite /SF_nth SF_sup_P_lx SF_sup_P_ly //= ;
  case: i Hi => [|i] Hi //= ; apply lt_S_n in Hi ;
  rewrite (nth_pairmap 0) // ; apply SSR_leq ; intuition.
Qed.

Lemma SF_sup_P_bound (f : R -> R) (P : seq R) (x0 : R) :
  SF_sup_P f (rev P) x0 = SF_rev (SF_sup_P f P x0).
Proof.
  apply rcons_dec with (s := P) => // {P} P.
  apply rcons_ind with (s := P) => // {P} P t IHP t0.
  rewrite rcons_SF_sup_P ?SF_rev_rcons -IHP ?rev_rcons Sup_fct_bound => //=.
Qed.

(** *** SF_seq of local sup *)

Fixpoint SF_inf_P_aux (f : R -> R) (P : seq R) x0 : seq (R*Rbar) :=
  behead (pairmap (fun x y => (y,Inf_fct f x y)) x0 P).
Definition SF_inf_P (f : R -> R) (P : seq R) x0 : SF_seq :=
  mkSF_seq (head x0 P) (SF_inf_P_aux f P x0).

Lemma SF_inf_P_lx (f : R -> R) (P : seq R) (x0 : R) :
  SF_lx (SF_inf_P f P x0) = (head x0 P) :: (behead P).
Proof.
  case: P => //= h P ;
  have : (unzip1 (pairmap (fun x y : R => (y, Inf_fct f x y)) h P) = P) ;
  [| rewrite /SF_inf_P /SF_lx /= ; by move => ->] ;
  by elim: P h => {x0} //= h P -> h0.
Qed.
Lemma SF_inf_P_ly (f : R -> R) (P : seq R) (x0 : R) :
  SF_ly (SF_inf_P f P x0) = behead (pairmap (Inf_fct f) x0 P).
Proof.
  case: P => //= h P ; rewrite /SF_inf_P /SF_ly //= ;
  by elim: P h => {x0} //= h P -> h0.
Qed.

Lemma cons_SF_inf_P (f : R -> R) (h0 h1 : R) (P : seq R) (x0 : R) : 
  SF_inf_P f (cons h0 (cons h1 P)) x0 = 
    SF_cons (h0,Inf_fct f h0 h1) (SF_inf_P f (cons h1 P) x0).
Proof.
  by [].
Qed.
Lemma rcons_SF_inf_P (f : R -> R) (P : seq R) (t1 t0 : R) (x0 : R) : 
  SF_inf_P f (rcons (rcons P t1) t0) x0 = 
    SF_rcons (SF_inf_P f (rcons P t1) x0) (t0,Inf_fct f t1 t0).
Proof.
  elim: P => //= h P.
  have: (exists h1, exists P1, rcons P t1 = h1 :: P1) ; 
    [|case => h1 [P1 H1] ; rewrite H1 /=].
    case: P t1 => {t0 x0 f} [| t P] t1.
    exists t1 ; by exists [::].
    exists t ; by exists (rcons P t1).
  have: (exists h0, exists P0, rcons P1 t0 = h0 :: P0) ;
    [|case => h0 [P0 H0] ; rewrite H0 /=].
    case: (P1) t0 => [| t P1'] t0.
    exists t0 ; by exists [::].
    exists t ; by exists (rcons P1' t0).
  have: (SF_inf_P f [:: h, h1, h0 & P0] x0 =
    SF_cons (h,Inf_fct f h h1) (SF_inf_P f [::h1,h0& P0] x0)) ;
    [by []| by move => -> ->].
Qed.

Lemma nth_SF_inf_P (f : R -> R) (P : seq R) (x0 : R) (i : nat) : (S i < size P)%nat ->
  SF_nth (0,Finite 0) (SF_inf_P f P x0) i = (nth 0 P i, Inf_fct f (nth 0 P i) (nth 0 P (S i))).
Proof.
  move: i ; case: P => [| h P].
  move => i Hi ; by apply lt_n_O in Hi.
  elim: P h => /= [|h P IH] h0 i Hi ; apply lt_S_n in Hi.
  by apply lt_n_O in Hi.
  rewrite /SF_nth SF_inf_P_lx SF_inf_P_ly //= ;
  case: i Hi => [|i] Hi //= ; apply lt_S_n in Hi ;
  rewrite (nth_pairmap 0) // ; apply SSR_leq ; intuition.
Qed.

Lemma SF_inf_P_bound (f : R -> R) (P : seq R) (x0 : R) :
  SF_inf_P f (rev P) x0 = SF_rev (SF_inf_P f P x0).
Proof.
  apply rcons_dec with (s := P) => // {P} P.
  apply rcons_ind with (s := P) => // {P} P t IHP t0.
  rewrite rcons_SF_inf_P ?SF_rev_rcons -IHP ?rev_rcons Inf_fct_bound => //=.
Qed.

(** *** SF_sup and SF_inf *)

Definition SF_sup (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  (SF_sup_P f (RInt_part a b n) 0).
Definition SF_sup_real (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_map real (SF_sup f a b n).

Definition SF_inf (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  (SF_inf_P f (RInt_part a b n) 0).
Definition SF_inf_real (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_map real (SF_inf f a b n).

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_sup f a b n) = SF_sup f b a n.
Proof.
  rewrite {2}/SF_sup RInt_part_bound SF_sup_P_bound => //.
Qed.
Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) : 
  SF_rev (SF_inf f a b n) = SF_inf f b a n.
Proof.
  rewrite {2}/SF_inf (RInt_part_bound b a) SF_inf_P_bound => //.
Qed.

Definition SF_sup_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_sup f a b n) (Finite 0) x
    | right _ => SF_fun (SF_sup f b a n) (Finite 0) x
  end.
Definition SF_inf_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_inf f a b n) (Finite 0) x
    | right _ => SF_fun (SF_inf f b a n) (Finite 0) x
  end.

Lemma SF_sup_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) :
  SF_sup_fun f a b n x = SF_sup_fun f b a n x.
Proof.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
  by rewrite (Rle_antisym _ _ Hab Hba).
  by contradict Hba ; apply Rlt_le, Rnot_le_lt.
Qed.
Lemma SF_inf_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) :
  SF_inf_fun f a b n x = SF_inf_fun f b a n x.
Proof.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
  by rewrite (Rle_antisym _ _ Hab Hba).
  by contradict Hba ; apply Rlt_le, Rnot_le_lt.
Qed.

Lemma SF_sup_fun_val (f : R -> R) (a b : R) (n i : nat) (x : R) : 
  a <= b -> (i < pow2 n)%nat ->
  let a0 := nth 0 (RInt_part a b n) i in
  let b0 := nth 0 (RInt_part a b n) (S i) in
  (a0 <= x < b0) -> SF_sup_fun f a b n x = Sup_fct f a0 b0.
Proof.
  move => Hab Hi ; have H : (S (pow2 n) = size (RInt_part a b n)) ;
    [by rewrite size_mkseq | apply lt_n_S in Hi ; rewrite H in Hi => {H}] ;
  move : Hi (RInt_part_sorted_0 a b n Hab) ; rewrite /SF_sup_fun ;
  case: (Rle_dec a b) => // _ ; rewrite /SF_sup.
  case: (RInt_part a b n) i => [| h s] i Hi ; simpl in Hi.
    by apply lt_n_O in Hi.
  move/lt_S_n: Hi ; move: i ; elim: s h => [h i Hi|h s IH h0].
    by apply lt_n_O in Hi.
  case => [|i] Hi Hs /= Hx.
  set Hx' := Rle_not_lt _ _ (proj1 Hx) ; set Hx'' := proj2 Hx.
  rewrite /SF_fun /= ; case: (Rlt_dec x h0) => // _ ; case: (Rlt_dec x h) => // _.
  simpl in Hi ; apply lt_S_n in Hi ; rewrite -(IH h i) /SF_fun //=.
  have H : ~(x < h).
    apply Rle_not_lt, Rle_trans with (2 := proj1 Hx) ; have: (h = nth 0 (h :: s) 0) ; [by [] | move => {1}->].
    elim: (i) Hi => {i Hx IH} [|i IH] Hi.
    apply Rle_refl.
    apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hi)), sorted_nth => /=.
    apply Hs.
    apply lt_trans with (2 := Hi), lt_n_Sn.
  case: (Rlt_dec x h0) => Hx0.
  contradict H ; apply Rlt_le_trans with (1 := Hx0), Hs.
  case: (Rlt_dec x h) => //.
  apply Hs.
Qed.
Lemma SF_inf_fun_val (f : R -> R) (a b : R) (n i : nat) (x : R) : 
  a <= b -> (i < pow2 n)%nat ->
  let a0 := nth 0 (RInt_part a b n) i in
  let b0 := nth 0 (RInt_part a b n) (S i) in
  (a0 <= x < b0) -> SF_inf_fun f a b n x = Inf_fct f a0 b0.
Proof.
  move => Hab Hi ; have H : (S (pow2 n) = size (RInt_part a b n)) ;
    [by rewrite size_mkseq | apply lt_n_S in Hi ; rewrite H in Hi => {H}] ;
  move : Hi (RInt_part_sorted_0 a b n Hab) ; rewrite /SF_inf_fun ;
  case: (Rle_dec a b) => // _ ; rewrite /SF_inf.
  case: (RInt_part a b n) i => [| h s] i Hi ; simpl in Hi.
    by apply lt_n_O in Hi.
  move/lt_S_n: Hi ; move: i ; elim: s h => [h i Hi|h s IH h0].
    by apply lt_n_O in Hi.
  case => [|i] Hi Hs /= Hx.
  set Hx' := Rle_not_lt _ _ (proj1 Hx) ; set Hx'' := proj2 Hx.
  rewrite /SF_fun /= ; case: (Rlt_dec x h0) => // _ ; case: (Rlt_dec x h) => // _.
  simpl in Hi ; apply lt_S_n in Hi ; rewrite -(IH h i) /SF_fun //=.
  have H : ~(x < h).
    apply Rle_not_lt, Rle_trans with (2 := proj1 Hx) ; have: (h = nth 0 (h :: s) 0) ; [by [] | move => {1}->].
    elim: (i) Hi => {i Hx IH} [|i IH] Hi.
    apply Rle_refl.
    apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hi)), sorted_nth => /=.
    apply Hs.
    apply lt_trans with (2 := Hi), lt_n_Sn.
  case: (Rlt_dec x h0) => Hx0.
  contradict H ; apply Rlt_le_trans with (1 := Hx0), Hs.
  case: (Rlt_dec x h) => //.
  apply Hs.
Qed.

Lemma SF_sup_ge_f (f : R -> R) (a b : R) (n : nat) (x : R) :
  (Rmin a b < x < Rmax a b) -> Rbar_le (Finite (f x)) (SF_sup_fun f a b n x).
Proof.
  wlog : a b / (a <= b) => [Hw|].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm SF_sup_fun_bound ; 
    by apply Hw, Rlt_le, Rnot_le_lt.
  rewrite /Rmin /Rmax ; case: (Rle_dec a b) => // _ Hab Hx ;
  case: (RInt_part_nat_0 a b n x) ; [intuition|] => {Hx} i [Hi Hx].
  rewrite (SF_sup_fun_val f a b n i x) => //.
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l [ub _] /=.
  apply: ub ; exists x ;
  have : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hi), Hi |] ;
  rewrite /Rmin /Rmax ; case: (Rle_dec _ _) ; intuition.
Qed.

Lemma SF_inf_le_f (f : R -> R) (a b : R) (n : nat) (x : R) :
  (Rmin a b < x < Rmax a b) -> Rbar_le (SF_inf_fun f a b n x) (Finite (f x)).
Proof.
  wlog : a b / (a <= b) => [Hw|].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm SF_inf_fun_bound ; 
    by apply Hw, Rlt_le, Rnot_le_lt.
  rewrite /Rmin /Rmax ; case: (Rle_dec a b) => // _ Hab Hx ;
  case: (RInt_part_nat_0 a b n x) ; [intuition|] => {Hx} i [Hi Hx].
  rewrite (SF_inf_fun_val f a b n i x) => //.
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => l [ub _] /=.
  apply: ub ; exists x ;
  have : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hi), Hi |] ;
  rewrite /Rmin /Rmax ; case: (Rle_dec _ _) ; intuition.
Qed.

Lemma SF_sup_decr (f : R -> R) (a b : R) (n : nat) (x : R) :
  Rbar_le (SF_sup_fun f a b (S n) x) (SF_sup_fun f a b n x).
Proof.
  wlog: a b / (a <= b) => [Hw| Hab].
    case: (Rle_lt_dec a b) => Hab.
    apply Hw, Hab.
    rewrite ?(SF_sup_fun_bound f a b) ; apply Hw, Rlt_le, Hab.
  wlog: x / (a <= x < b) => [| Hx].
    rewrite /SF_sup_fun ; case: (Rle_dec a b) => // _ Hw.
    case: (Rlt_dec x b) => Hxb ; [case: (Rle_lt_dec a x) => Hax|].
    apply Hw ; split => //.
    rewrite /SF_fun /= ;
    have: ((a + 0 * (b - a) / (2 * 2 ^ n)) = a) ; 
    [field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2 | move => ->] ;
    have : ((a + 0 * (b - a) / 2 ^ n) = a) ;
    [field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2 | move => ->] ;
    case: (Rlt_dec _ _) => // _ ; by right.
    have H0 : forall n, SF_fun (SF_sup f a b n) (Finite 0) x = Finite 0.
    have H : forall s x, SF_sorted Rle s -> ~x < last 0 (SF_lx s) -> 
      SF_fun s (Finite 0) x = Finite 0 => [{f n x a b Hab Hw Hxb} s|].
      apply SF_cons_ind with (s := s) => {s} /= [x0| h s IH] x Hs Hl ;
      rewrite /SF_fun /= ; case: (Rlt_dec _ _) => // Hx.
      rewrite -{2}(IH x) /SF_fun //=.
      case: (Rlt_dec _ _) => // H ; contradict Hl ; 
      apply Rlt_le_trans with (1 := H) ; rewrite /SF_sorted /= in Hs.
      elim: (unzip1 (SF_t s)) (SF_h s) (proj2 Hs) => /= {h s IH x Hx H Hs} [x _|h s IH x Hs].
      apply Rle_refl.
      apply Rle_trans with (1 := proj1 Hs), IH, Hs.
      apply Hs.
    move => n0 ; apply H.
    rewrite /SF_sorted SF_sup_P_lx ; apply (RInt_part_sorted_0 a b n0), Hab.
    rewrite SF_sup_P_lx.
    have: ((head 0 (RInt_part a b n0) :: behead (RInt_part a b n0)) = (RInt_part a b n0)) ;
    [| move => ->].
    have: (0 < size (RInt_part a b n0))%nat ; [rewrite size_mkseq ; apply lt_O_Sn | ] ;
    case : (RInt_part a b n0) => // H0 ; by apply lt_n_O in H0.
    rewrite -nth_last size_mkseq /= nth_mkseq //= pow2_INR ; contradict Hxb ;
    apply Rlt_le_trans with (1 := Hxb), Req_le ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
    rewrite ?H0 ; by right.
  case: (RInt_part_nat_0 a b (S n) x Hx) => {Hx} i [Hx Hi].
    have H1 : (sum {j : nat | i = (2*j)%nat} {j : nat | i = S (2*j)}).
        elim: (i) => {i Hx Hi} [|i].
        left ; exists 0%nat ; intuition.
        case ; case => j Hj.
        right ; exists j ; intuition.
        left ; exists (S j) ; intuition.
    have Hi' : (div2 i < pow2 n)%nat.
      have H0: (forall m n, (2*m < 2*n)%nat -> (m<n)%nat).
        elim => [| m IH] ; intuition.
      case: H1 ; case => j Hj ; rewrite Hj in Hi |-* ;
      [rewrite div2_double|rewrite div2_double_plus_one] ;
      apply H0, le_lt_trans with (2 := Hi) ; intuition.
    have H0 : (forall i, INR (2*i) = 2*INR i).
      elim => {H1} // [| I HI] ; intuition.
      have: (2* (S I) = S (S (2*I)))%nat.
        elim: (I) => {I HI} [| I IH] ; intuition.
      move => -> ; rewrite ?S_INR HI ; ring.
    have Hx' : nth 0 (RInt_part a b n) (div2 i) <= x < nth 0 (RInt_part a b n) (S (div2 i)).
      rewrite ?nth_mkseq in Hx |-* ; try apply SSR_leq ; intuition ;
      try case: a0 => j Hj ; try case: b0 => j Hj ; 
      rewrite Hj ?div2_double ?div2_double_plus_one ?S_INR ?H0 -?tech_pow_Rmult in H, H2 |- *.
      apply Rle_trans with (2 := H), Req_le ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
      apply Rlt_le_trans with (1 := H2).
      rewrite -(Rplus_0_r (a + (2 * INR j + 1) * (b - a) / (2 * 2 ^ n))) ;
      have: (a + (INR j + 1) * (b - a) / 2 ^ n = 
        a + (2 * INR j + 1) * (b - a) / (2 * 2 ^ n) + (b-a)/(2*2^n)) ; 
        [field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
      apply Rplus_le_compat_l, Rdiv_le_pos.
      apply (Rminus_le_0 a b), Hab.
      apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2.
      apply Rle_trans with (2 := H).
      rewrite -(Rplus_0_r (a + (INR j) * (b - a) / (2 ^ n))) ;
      have: (a + (2 * INR j + 1) * (b - a) / (2 * 2 ^ n) =
        a + INR j * (b - a) / 2 ^ n + (b-a) / (2* 2^n)) ; 
        [field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
      apply Rplus_le_compat_l, Rdiv_le_pos.
      apply (Rminus_le_0 a b), Hab.
      apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2.
      apply Rlt_le_trans with (1 := H2), Req_le ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
      
    rewrite (SF_sup_fun_val f a b (S n) i x) => // ;
    rewrite (SF_sup_fun_val f a b n (div2 i) x) => //.
    rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l1 [ub1 lub1] ;
    case: (ex_lub_Rbar_ne _ _) => l0 [ub0 lub0] /=.
    apply: lub1 => {ub1} _ [x' [-> H]] ; apply: ub0 => {lub0} ; exists x' ; 
    split ; auto.
    have: (nth 0 (RInt_part a b n) (div2 i)) <= (nth 0 (RInt_part a b n) (S (div2 i))).
      case : Hx' => Hx0 Hx1 ; apply Rlt_le in Hx1 ; by apply Rle_trans with (r2 := x).
    have: ((nth 0 (RInt_part a b (S n)) i) <= (nth 0 (RInt_part a b (S n)) (S i))).
      case: Hx => Hx0 Hx1 ; apply Rlt_le in Hx1 ; by apply Rle_trans with (r2 := x).
    move: H ; rewrite /Rmin /Rmax ; case: (Rle_dec _ _) => // _ ;
    case: (Rle_dec _ _) => // _ [H6 H7] _ _.
      rewrite ?nth_mkseq in H6, H7 |-* ; try apply SSR_leq ; intuition ;
      try case: a0 => j Hj ; try case: b0 => j Hj ; 
      rewrite Hj ?div2_double ?div2_double_plus_one ?S_INR ?H0 -?tech_pow_Rmult in H6, H7 |- *.
      apply Rle_trans with (2 := H6), Req_le ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
      apply Rle_trans with (1 := H7).
      rewrite -(Rplus_0_r (a + (2 * INR j + 1) * (b - a) / (2 * 2 ^ n))) ;
      have: (a + (INR j + 1) * (b - a) / 2 ^ n = 
        a + (2 * INR j + 1) * (b - a) / (2 * 2 ^ n) + (b-a)/(2*2^n)) ; 
        [field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
      apply Rplus_le_compat_l, Rdiv_le_pos.
      apply (Rminus_le_0 a b), Hab.
      apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2.
      apply Rle_trans with (2 := H6).
      rewrite -(Rplus_0_r (a + (INR j) * (b - a) / (2 ^ n))) ;
      have: (a + (2 * INR j + 1) * (b - a) / (2 * 2 ^ n) =
        a + INR j * (b - a) / 2 ^ n + (b-a) / (2* 2^n)) ; 
        [field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
      apply Rplus_le_compat_l, Rdiv_le_pos.
      apply (Rminus_le_0 a b), Hab.
      apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2.
      apply Rle_trans with (1 := H7), Req_le ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
Qed.

Lemma SF_inf_incr (f : R -> R) (a b : R) (n : nat) (x : R) :
  Rbar_le (SF_inf_fun f a b n x) (SF_inf_fun f a b (S n) x).
Admitted.



(** * A trier *)

Lemma SF_size_sup (f : R -> R) (a b : R) (n : nat) :
  SF_size (SF_sup f a b n) = pow2 n.
Proof.
  apply eq_add_S ; rewrite -SF_size_lx SF_sup_P_lx .
Qed.
Lemma SF_size_inf (f : R -> R) (a b : R) (n : nat) :
  SF_size (SF_inf f a b n) = pow2 n.
Proof.
  apply eq_add_S ; by rewrite -SF_size_lx SF_inf_P_lx size_mkseq.
Qed.

Lemma SF_sup_sorted_0 (f : R -> R) (a b : R) (n : nat) : (a <= b) ->
  SF_sorted Rle (SF_sup f a b n).
Proof.
  move => Hab ; rewrite /SF_sorted /SF_sup SF_sup_P_lx.
  have: (exists h, exists t, RInt_part a b n = h::t) ;
    [| case => h [t H] ; rewrite H -H => {h t H}].
    have: (size (RInt_part a b n) = S(pow2 n)).
      by rewrite size_mkseq.
    case: (RInt_part a b n) => // t s _ ;
    exists t ; by exists s.
  by apply RInt_part_sorted_0.
Qed.
Lemma SF_sup_sorted_1 (f : R -> R) (a b : R) (n : nat) : (b <= a) ->
  SF_sorted Rge (SF_sup f a b n).
Proof.
  move => Hab ; rewrite /SF_sorted /SF_sup SF_sup_P_lx.
  have: (exists h, exists t, RInt_part a b n = h::t) ;
    [| case => h [t H] ; rewrite H -H => {h t H}].
    have: (size (RInt_part a b n) = S(pow2 n)).
      by rewrite size_mkseq.
    case: (RInt_part a b n) => // t s _ ;
    exists t ; by exists s.
  by apply RInt_part_sorted_1.
Qed.
Lemma SF_inf_sorted_0 (f : R -> R) (a b : R) (n : nat) : (a <= b) ->
  SF_sorted Rle (SF_inf f a b n).
Proof.
  move => H ; rewrite /SF_sorted /SF_inf SF_inf_P_lx /= ;
  by apply (RInt_part_sorted_0 a b n).
Qed.
Lemma SF_inf_sorted_1 (f : R -> R) (a b : R) (n : nat) : (b <= a) ->
  SF_sorted Rge (SF_inf f a b n).
Proof.
  move => H ; rewrite /SF_sorted /SF_inf SF_inf_P_lx /= ;
  by apply (RInt_part_sorted_1 a b n).
Qed.

Lemma SF_sup_ge_f_0 (f : R -> R) (a b : R) (n : nat) : 
  forall x, (a <= x < b) -> Rbar_le (Finite (f x)) (SF_fun (SF_sup f a b n) (Finite 0) x).
Proof.
  move => x Hx.
  case: (RInt_part_nat_0 a b n x Hx) => i [Hi Hin].
  rewrite (SF_fun_incr _ _ _ i).
  have: ((nth (Finite 0) (SF_ly (SF_sup f a b n)) i) =
    snd (SF_nth (0, Finite 0) (SF_sup_P f (RInt_part a b n) 0) i)) ; 
    [by [] | move => -> ] ;
  rewrite nth_SF_sup_P /snd.
  have H : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)).
    apply Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => s Hs /= ; apply Hs ; 
  exists x ; rewrite /Rmin /Rmax ; case : (Rle_dec (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i))) ; intuition.
  rewrite size_mkseq ; apply lt_n_S, Hin.
  apply SF_sup_sorted_0, Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  rewrite SF_size_sup ; apply Hin.
  by rewrite SF_sup_P_lx.
Qed.
Lemma SF_sup_ge_f_1 (f : R -> R) (a b : R) (n : nat) : 
  forall x, (b <= x < a) -> Rbar_le (Finite (f x)) (SF_fun (SF_rev (SF_sup f a b n)) (Finite 0) x).
Proof.
  move => Hn ; rewrite SF_sup_bound => // ;
  apply SF_sup_ge_f_0 => //.
Qed.

Lemma SF_inf_le_f_0 (f : R -> R) (a b : R) (n : nat) : 
  forall x, (a <= x < b) -> Rbar_le (SF_fun (SF_inf f a b n) (Finite 0) x) (Finite (f x)).
Proof.
  move => x Hx.
  case: (RInt_part_nat_0 a b n x Hx) => i [Hi Hin].
  rewrite (SF_fun_incr _ _ _ i).
  have: ((nth (Finite 0) (SF_ly (SF_inf f a b n)) i) =
    snd (SF_nth (0, Finite 0) (SF_inf_P f (RInt_part a b n) 0) i)) ; 
    [by [] | move => -> ] ;
  rewrite nth_SF_inf_P /snd.
  have H : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)).
    apply Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => s Hs /= ; apply Hs ; 
  exists x ; rewrite /Rmin /Rmax ; case : (Rle_dec (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i))) ; intuition.
  rewrite size_mkseq ; apply lt_n_S, Hin.
  apply SF_inf_sorted_0, Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  rewrite SF_size_inf ; apply Hin.
  by rewrite SF_inf_P_lx.
Qed.
Lemma SF_inf_le_f_1 (f : R -> R) (a b : R) (n : nat) : 
  forall x, (b <= x < a) -> Rbar_le (SF_fun (SF_rev (SF_inf f a b n)) (Finite 0) x) (Finite (f x)).
Proof.
  move => Hn ; rewrite SF_inf_bound => // ;
  apply SF_inf_le_f_0 => //.
Qed.

Lemma SF_sup_finite (f : R -> R) (a b : R) (n : nat) (M : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> f x <= M) ->
  (SF_sup f a b n) = SF_map Finite (real_SF_sup f a b n).
Proof.
  wlog : a b / (a <= b).
  move => H ; case: (Rle_lt_dec a b) => Hab.
  by apply H.
  rewrite Rmin_comm Rmax_comm -SF_sup_bound SF_ly_rev => Hm ; 
  case: (H _ _ (Rlt_le _ _ Hab) Hm) => l Hl ; exists (rev l).
  by rewrite Hl map_rev.
  rewrite /Rmin /Rmax ; case: (Rle_dec a b) => // Hab _ Hm.

  exists (map real (SF_ly (SF_sup f a b n))).
  apply eq_from_nth with (x0 := Finite 0).
  by rewrite ?size_map.
  move => i Hi ; apply SSR_leq in Hi ; rewrite SF_size_ly SF_size_sup in Hi.
  rewrite (nth_map 0) ?size_map ; 
  [ | apply SSR_leq ; 
  have : (size (SF_t (SF_sup f a b n)) = SF_size (SF_sup f a b n)) ; 
  [by []| move => ->] ; by rewrite SF_size_sup ].
  rewrite (nth_map (Finite 0)) ; [ 
  | apply SSR_leq ; by rewrite SF_size_ly SF_size_sup].
  rewrite SF_sup_P_ly nth_behead (nth_pairmap 0) ; 
  [ | apply SSR_leq ; rewrite size_mkseq ; intuition].
  have: (nth 0 (0 :: RInt_part a b n) (S i) = nth 0 (RInt_part a b n) i) ; 
  [by [] | move => ->] ; rewrite ?nth_mkseq ; 
  [| apply SSR_leq ; intuition | apply SSR_leq ; intuition].
  have Hord : ((a + INR i * (b - a) / 2 ^ n) <= (a + INR (S i) * (b - a) / 2 ^ n)).
    rewrite -(Rplus_0_r (a + INR i * (b - a) / 2 ^ n)) ;
    have : (a + INR (S i) * (b - a) / 2 ^ n = a + INR i * (b - a) / 2 ^ n + (b-a)/2^n) ;
    [| move => ->].
    rewrite S_INR ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
    apply Rplus_le_compat_l, Rdiv_le_pos ; 
    [by apply (Rminus_le_0 a b) | apply pow_lt, Rlt_R0_R2 ].
    
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ;
  case => [x | | ] ; rewrite /Rmin /Rmax ; case (Rle_dec _ _) => H1 [ub lub] //= {H1}.
(* sup <> p_infty *)
  have : (Rbar_le p_infty (Finite M)) ; [ | by case].
  apply lub => {ub} _ [x [-> H]].
  apply Rbar_finite_le, Hm ; split ;
  [apply Rle_trans with (2 := proj1 H) | apply Rle_trans with (1 := proj2 H)].
  rewrite -{1}(Rplus_0_r a) ; apply Rplus_le_compat_l, Rdiv_le_pos ; 
  [apply Rmult_le_pos|] ; intuition ; by apply (Rminus_le_0 a b).
  have : (b = a + INR (pow2 n) * (b - a) / 2 ^ n) ; 
  [rewrite pow2_INR ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2 | move => {2}-> ].
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
  apply Rmult_le_compat_r.
  by apply (Rminus_le_0 a b).
  by apply le_INR.
(* sup <> m_infty *)
  have: (Rbar_le (Finite (f (a + INR i * (b - a) / 2 ^ n))) m_infty) ; [| by case].
  apply ub => {lub}.
  exists (a + INR i * (b - a) / 2 ^ n) ; intuition.
Qed.

Definition RInt_Sum_s f a b n := 
  Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup f a b (S n)))) (mkposreal _ (lt_0_INR _ (lt_O_Sn n))).
Definition RInt_Sum_i f a b n := 
  Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf f a b (S n)))) (mkposreal _ (lt_0_INR _ (lt_O_Sn n))).

Lemma RInt_Sum_s_bound f a b n :
  RInt_Sum_s f a b n = RInt_Sum_s f b a n.
Proof.
  have H : (forall i, (i < size (SF_ly (SF_sup f a b (S n))))%nat -> 
    Rbar_lt m_infty (nth (Finite 0) (SF_ly (SF_sup f a b (S n))) i)).
    rewrite SF_size_ly => i Hi ; apply lt_n_S in Hi ; rewrite -SF_size_lx SF_seq_bij_lx in Hi ;
    rewrite ?SF_seq_bij_ly nth_SF_sup_P => //.
    rewrite size_mkseq in Hi ;
    rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; 
    case => // ; simpl projT1 ; rewrite ?nth_mkseq ; try apply SSR_leq => // ;
    set a0 := (a + INR i * (b - a) / INR (S n)) ;
    set b0 := (a + INR (S i) * (b - a) / INR (S n)).
    case => ub _ ; case: (ub (f a0)) => //= ;
    exists a0 ; split => // ; by apply Rmin_Rmax_l.
    by apply lt_le_weak.
  apply Rbar_div_pos_eq ; move: H ; rewrite ?SF_seq_bij_ly ;
  rewrite (RInt_part_bound b a) ?SF_sup_P_bound ; try by apply lt_O_Sn.
  have: (Rbar_lt m_infty (Finite 0)) => //.
  move: (SF_sup_P f (RInt_part a b (S n))) (Finite 0) => {f a b n} s x0.
  rewrite (fold_comm _ _ (rev s)) ?revK ; try by apply Rbar_plus_comm.
  case: s x0 => // t s ; elim: s t => [| t0 s IH] t x0 Hx0 Hlt /=.
  apply Rbar_plus_comm.
  have Rw: (forall a b c, Rbar_lt m_infty a -> Rbar_lt m_infty b -> Rbar_lt m_infty c -> 
    Rbar_plus a (Rbar_plus b c) = Rbar_plus (Rbar_plus a b) c).
    case => [a | | ] ; 
    case => [b | | ] ;
    case => [c | | ] Ha Hb Hc //= {Ha Hb Hc}.
    apply Rbar_finite_eq ; ring.
  move : (Hlt O (lt_O_Sn _)) (Hlt _ (lt_n_S _ _ (lt_O_Sn _))) => H0 H1.
  rewrite -(Rw x0) ?(Rw t) => //.
  simpl in IH ; rewrite -(IH (Rbar_plus t t0) x0) => //.
  case => //= [_ | n Hn].
  case: t {Hlt} t0 H0 H1 => [t | | ] ; case => [t0 | | ] //.
  by apply (Hlt (S (S n))), lt_n_S.
  elim: {IH Rw} s H0 H1 Hlt => // t1 s IH H0 H1 Hlt /=.
  case: (t1) (Hlt _ (lt_n_S _ _ (lt_n_S _ _ (lt_O_Sn _)))) => // [t2 | ] _ ;
  case: (foldr Rbar_plus x0 s) IH => // IH.
  have: (Rbar_lt m_infty m_infty) => //.
  apply IH => // ; case => // ; case => // n Hn.
  by apply (Hlt (S (S (S n)))), lt_n_S.
Qed.
Lemma RInt_Sum_i_bound f a b n :
  RInt_Sum_i f a b n = RInt_Sum_i f b a n.
Proof.
  have H : (forall i, (i < size (SF_ly (SF_inf f a b (S n))))%nat -> 
    Rbar_lt (nth (Finite 0) (SF_ly (SF_inf f a b (S n))) i) p_infty).
    rewrite SF_size_ly => i Hi ; apply lt_n_S in Hi ; rewrite -SF_size_lx SF_seq_bij_lx in Hi ;
    rewrite ?SF_seq_bij_ly nth_SF_inf_P => //.
    rewrite size_mkseq in Hi ;
    rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) ; 
    case => // ; simpl projT1 ; rewrite ?nth_mkseq ; try apply SSR_leq => // ;
    set a0 := (a + INR i * (b - a) / INR (S n)) ;
    set b0 := (a + INR (S i) * (b - a) / INR (S n)).
    case => ub _ ; case: (ub (f a0)) => //= ;
    exists a0 ; split => // ; by apply Rmin_Rmax_l.
    by apply lt_le_weak.
  apply Rbar_div_pos_eq ; move: H ; rewrite ?SF_seq_bij_ly ;
  rewrite (RInt_part_bound b a) ?SF_inf_P_bound ; try by apply lt_O_Sn.
  have: (Rbar_lt (Finite 0) p_infty) => //.
  move: (SF_inf_P f (RInt_part a b (S n))) (Finite 0) => {f a b n} s x0.
  rewrite (fold_comm _ _ (rev s)) ?revK ; try by apply Rbar_plus_comm.
  case: s x0 => // t s ; elim: s t => [| t0 s IH] t x0 Hx0 Hlt /=.
  apply Rbar_plus_comm.
  have Rw: (forall a b c, Rbar_lt a p_infty -> Rbar_lt b p_infty -> Rbar_lt c p_infty -> 
    Rbar_plus a (Rbar_plus b c) = Rbar_plus (Rbar_plus a b) c).
    case => [a | | ] ; 
    case => [b | | ] ;
    case => [c | | ] Ha Hb Hc //= {Ha Hb Hc}.
    apply Rbar_finite_eq ; ring.
  move : (Hlt O (lt_O_Sn _)) (Hlt _ (lt_n_S _ _ (lt_O_Sn _))) => H0 H1.
  rewrite -(Rw x0) ?(Rw t) => //.
  simpl in IH ; rewrite -(IH (Rbar_plus t t0) x0) => //.
  case => //= [_ | n Hn].
  case: t {Hlt} t0 H0 H1 => [t | | ] ; case => [t0 | | ] //.
  by apply (Hlt (S (S n))), lt_n_S.
  elim: {IH Rw} s H0 H1 Hlt => // t1 s IH H0 H1 Hlt /=.
  case: (t1) (Hlt _ (lt_n_S _ _ (lt_n_S _ _ (lt_O_Sn _)))) => // [t2 | ] _ ;
  case: (foldr Rbar_plus x0 s) IH => // IH.
  have: (Rbar_lt p_infty p_infty) => //.
  apply IH => // ; case => // ; case => // n Hn.
  by apply (Hlt (S (S (S n)))), lt_n_S.
Qed.

(** * A new Riemann_integrable in Prop *)

Definition is_RInt (f : R -> R) (a b : R) :=
  Rbar_inf_seq (RInt_Sum_s f a b) = Rbar_sup_seq (RInt_Sum_i f a b)
  /\ Finite (real (Rbar_inf_seq (RInt_Sum_s f a b))) = Rbar_inf_seq (RInt_Sum_s f a b).

Lemma is_RInt_bound (f : R -> R) (a b : R) :
  is_RInt f a b -> is_RInt f b a.
Proof.
  rewrite /is_RInt ; case => H H0 ;
  rewrite (Rbar_inf_seq_rw _ _ (RInt_Sum_s_bound _ _ _)) ;
  rewrite (Rbar_sup_seq_rw _ _ (RInt_Sum_i_bound _ _ _)) ; by split.
Qed.

Lemma is_RInt_correct_0 (f : R -> R) (a b : R) :
  is_RInt f a b -> Riemann_integrable f a b.
Proof.
  wlog : a b / (a <= b).
  move => Hgen ; case: (Rle_lt_dec a b) => Hab H.
  by apply Hgen.
  apply Rlt_le in Hab ;
  apply RiemannInt_P1, Hgen => // ; by apply is_RInt_bound.
  move => Hab ; case => Heq Hfin eps.
  
  set phi := fun n => SF_compat_le _ ()
Qed.