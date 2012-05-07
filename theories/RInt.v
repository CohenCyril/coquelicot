Require Import Reals seq.
Require Import Arithmetique Floor Total_sup Sup_seq.
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
Lemma foldr_rev {T T0 : Type} : forall (f : T0 -> T -> T) x0 s, 
  foldr f x0 (rev s) = foldl (fun x y => f y x) x0 s.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0.
  rewrite rev_cons foldr_rcons ; apply IH.
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

Record SF_seq (T : Type) := mkSF_seq {SF_h : R ; SF_t : seq (R * T)}.
Implicit Arguments SF_h [T].
Implicit Arguments SF_t [T].
Implicit Arguments mkSF_seq [T].
Definition SF_lx {T : Type} (s : SF_seq T) : seq R := (SF_h s)::(unzip1 (SF_t s)).
Definition SF_ly {T : Type} (s : SF_seq T) : seq T := unzip2 (SF_t s).
Definition SF_make {T : Type} (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_seq T :=
  mkSF_seq (head 0 lx) (zip (behead lx) ly).

Lemma SF_size_lx_ly {T : Type} (s : SF_seq T) : size (SF_lx s) = S (size (SF_ly s)).
Proof.
  case: s => sh st ;
  rewrite /SF_lx /SF_ly /= ;
  elim: st => //= t s -> //.
Qed.

Lemma SF_seq_bij {T : Type} (s : SF_seq T) :
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

Definition SF_nil {T : Type} (x0 : R) : SF_seq T := mkSF_seq x0 [::].
Definition SF_cons {T : Type} (h : R*T) (s : SF_seq T) :=
  mkSF_seq (fst h) ((SF_h s,snd h)::(SF_t s)).
Lemma SF_cons_dec {T : Type} (P : SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P (SF_cons h s)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; case: st => [| h sf].
  apply Hnil.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf)) => {Hcons} ; 
  rewrite /SF_cons -surjective_pairing //=.
Qed.
Lemma SF_cons_ind {T : Type} (P : SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P s -> P (SF_cons h s)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; elim: st sh => [sh |h sf IHst sh].
  apply Hnil.
  move: (IHst (fst h)) => {IHst} IHst.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf) IHst) => {Hcons} ; 
  rewrite /SF_cons -surjective_pairing //=.
Qed.
Definition SF_rcons {T : Type} (s : SF_seq T) (t : R*T) :=
  mkSF_seq (SF_h s) (rcons (SF_t s) t).
Lemma SF_rcons_dec {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P (SF_rcons s t)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st ; apply rcons_dec => [| st t].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t).
Qed.
Lemma SF_rcons_ind {T : Type} (P : SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P s -> P (SF_rcons s t)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st sh ;
  apply (rcons_ind (fun st => forall sh, P {| SF_h := sh; SF_t := st |})) => [sh | st t IHst sh].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t) => //.
Qed.

Lemma SF_lx_cons {T : Type} (h : R*T) (s : SF_seq T) :
  SF_lx (SF_cons h s) = (fst h) :: (SF_lx s).
Proof.
  by [].
Qed.
Lemma SF_ly_cons {T : Type} (h : R*T) (s : SF_seq T) :
  SF_ly (SF_cons h s) = (snd h) :: (SF_ly s).
Proof.
  by [].
Qed.
Lemma SF_lx_rcons {T : Type} (s : SF_seq T) (h : R*T) :
  SF_lx (SF_rcons s h) = rcons (SF_lx s) (fst h).
Proof.
  case: s => sh st ; rewrite /SF_lx /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.
Lemma SF_ly_rcons {T : Type} (s : SF_seq T) (h : R*T) :
  SF_ly (SF_rcons s h) = rcons (SF_ly s) (snd h).
Proof.
  case: s => sh st ; rewrite /SF_ly /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.

Definition SF_rev {T : Type} (s : SF_seq T) :=
  mkSF_seq (head 0 (rev (SF_lx s))) (zip (behead (rev (SF_lx s))) (rev (SF_ly s))).
Lemma SF_rev_invol {T : Type} (s : SF_seq T) :
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
Lemma SF_rev_cons {T : Type} (h : R*T) (s : SF_seq T) :
  SF_rev (SF_cons h s) = SF_rcons (SF_rev s) h.
Proof.
  case: s => sh st ;
  rewrite /SF_rev /SF_cons /SF_rcons /SF_lx /SF_ly /=.
  rewrite !rev_cons ?head_rcons ?(behead_rcons _ _ (size_rcons_pos _ _)).
  rewrite zip_rcons.
  by rewrite -surjective_pairing.
  rewrite size_behead size_rcons ?size_rev size_unzip1 size_unzip2 => //.
Qed.
Lemma SF_rev_rcons {T : Type} (s : SF_seq T) (t : R*T) :
  SF_rev (SF_rcons s t) = SF_cons t (SF_rev s).
Proof.
  rewrite -{1}(SF_rev_invol s) -SF_rev_cons SF_rev_invol => //.
Qed.

Lemma SF_lx_rev {T : Type} (s : SF_seq T) : SF_lx (SF_rev s) = rev (SF_lx s).
Proof.
  apply SF_cons_ind with (s := s) => {s} // h s IHs ;
  by rewrite SF_rev_cons SF_lx_cons SF_lx_rcons IHs -rev_cons.
Qed.
Lemma SF_ly_rev {T : Type} (s : SF_seq T) : SF_ly (SF_rev s) = rev (SF_ly s).
Proof.
  apply SF_cons_ind with (s := s) => {s} // h s IHs ;
  by rewrite SF_rev_cons SF_ly_cons SF_ly_rcons IHs -rev_cons.
Qed.

(** ** SF_size *)

Definition SF_size {T : Type} (s : SF_seq T) := size (SF_t s).

Lemma SF_size_cons {T : Type} (h : R*T) (s : SF_seq T) : SF_size (SF_cons h s) = S (SF_size s).
Proof.
  rewrite /SF_cons /SF_size //=.
Qed.

Lemma SF_size_rcons {T : Type} (s : SF_seq T) (t : R*T) : SF_size (SF_rcons s t) = S (SF_size s).
Proof.
  rewrite /SF_rcons /SF_size size_rcons //=.
Qed.

Lemma SF_size_lx {T : Type} (s : SF_seq T) : size (SF_lx s) = S (SF_size s).
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.
Lemma SF_size_ly {T : Type} (s : SF_seq T) : size (SF_ly s) = SF_size s.
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.

Lemma SF_size_rev {T : Type} (s : SF_seq T) : SF_size (SF_rev s) = SF_size s.
Proof.
  apply SF_cons_ind with (s := s) => {s} // h s IHs ;
  by rewrite SF_rev_cons SF_size_rcons SF_size_cons IHs.
Qed.

(** ** Order *)

Definition SF_sorted {T : Type} (Ord : R -> R -> Prop) (s : SF_seq T) :=
  sorted Ord (SF_lx s).

Lemma SF_sorted_rev_0 {T : Type} (s : SF_seq T) :
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
Lemma SF_sorted_rev_1 {T : Type} (s : SF_seq T) :
  SF_sorted Rge s <-> SF_sorted Rle (SF_rev s).
Proof.
  rewrite -{1}(SF_rev_invol s) ; split ;
  apply SF_sorted_rev_0.
Qed.

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
Definition SF_fun {T : Type} (s : SF_seq T) (x0 : T) (x : R) :=
  SF_fun_aux ((SF_h s,x0)::SF_t s) x0 x.

Lemma SF_fun_incr {T : Type} (s : SF_seq T) (x0 : T) (x : R) (i : nat) :
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

Lemma SF_fun_decr {T : Type} (s : SF_seq T) (x0 : T) (x : R) (i : nat) :
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

(** ** (seq R) and Rlist *)

Fixpoint mkRlist (s : seq R) :=
  match s with
    | [::] => RList.nil
    | h::t => RList.cons h (mkRlist t)
  end.

Lemma size_compat (s : seq R) :
  Rlength (mkRlist s) = size s.
Proof.
  elim: s => // t s IHs /= ; by rewrite IHs.
Qed.

Lemma nth_compat (s : seq R) (n : nat) :
  pos_Rl (mkRlist s) n = nth 0 s n.
Proof.
  elim: s n => [n|t s IHs n] /= ;
  case: n => //=.
Qed.

Lemma sorted_compat (s : seq R) :
  sorted Rle s <-> ordered_Rlist (mkRlist s).
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

Lemma SF_sorted_compat {T : Type} (s : SF_seq T) :
  SF_sorted Rle s <-> ordered_Rlist (mkRlist (SF_lx s)).
Proof.
  split => H ; apply sorted_compat => //.
Qed.

Lemma ad_SF_compat_le (s : SF_seq R) (pr : SF_sorted Rle s) : 
  adapted_couple (SF_fun s 0) (head 0 (SF_lx s)) (last 0 (SF_lx s))
    (mkRlist (SF_lx s)) (mkRlist (SF_ly s)).
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

Lemma is_SF_compat_le (s : SF_seq R) (pr : SF_sorted Rle s) : 
  IsStepFun (SF_fun s 0) (head 0 (SF_lx s)) (last 0 (SF_lx s)).
Proof.
  exists (mkRlist (SF_lx s)) ; exists (mkRlist (SF_ly s)).
  apply ad_SF_compat_le, pr.
Qed.

Definition SF_compat_le (s : SF_seq R) (pr : SF_sorted Rle s) : 
  StepFun (head 0 (SF_lx s)) (last 0 (SF_lx s)) := 
  mkStepFun (is_SF_compat_le s pr).

(** * Build sequences *)
(** ** sequence ly : partition of [a,b] *)

Definition RInt_part (a b : R) (n : nat) : seq R := 
  mkseq (fun i => a + (INR i) * (b - a) / (INR n)) (S n).

Lemma RInt_part_bound (a b : R) (n : nat) : (0 < n)%nat ->
  RInt_part a b n = rev (RInt_part b a n).
Proof.
  case: n a b.
(* n = 0 *)
  move => a b H ; contradict H ; apply lt_irrefl.
(* n > 0 *)
  move => n a b _.
  apply (@eq_from_nth R 0) ; rewrite ?size_rev ?size_mkseq => // ;
  move => i Hi ; apply SSR_leq in Hi.
  rewrite nth_rev ?SSR_leq ?SSR_minus ?size_mkseq => //.
  rewrite ?nth_mkseq ?SSR_leq => //.
  rewrite minus_INR ?S_INR => // ; field.
  rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
  apply INR_le ; rewrite ?S_INR minus_INR ?S_INR => //.
  ring_simplify ;
  apply Rplus_le_compat_r ; rewrite -{2}(Rplus_0_r (INR n)) ;
  apply Rplus_le_compat_l, Ropp_le_cancel ; rewrite Ropp_0 Ropp_involutive ;
  apply pos_INR.
Qed.

Lemma RInt_part_nat_0 (a b : R) (n : nat) (x : R) : (0 < n)%nat -> (a <= x < b)
  -> { i : nat | nth 0 (RInt_part a b n) i <= x < nth 0 (RInt_part a b n) (S i) /\ (i < n)%nat}.
Proof.
  case: n => [Hn | n _ Hx].
  contradict Hn ; apply lt_irrefl.
  have Hab : (a < b).
  apply Rle_lt_trans with (r2 := x) ; intuition.
(* a <= x < b *)
  case: Hx => Hx Hx'.
  case: (nfloor_ex (INR (S n)/(b - a) * (x - a))) => [| i Hi].
  apply Rmult_le_pos ; [apply Rdiv_le_pos ; 
  [apply pos_INR|by apply Rlt_Rminus]|apply (Rminus_le_0 a x)] ;
  apply Hx.
  exists i ; rewrite ?nth_mkseq ; try apply SSR_leq.
  split.
  have : (x = a + (INR (S n)/(b - a) * (x - a)) * (b-a)/INR (S n)).
  field ; split.
  by apply Rgt_not_eq, Rlt_Rminus.
  apply not_0_INR, sym_not_eq, O_S.
  move => -> ; split.
  apply Rplus_le_compat_l, Rmult_le_compat_r ;
  [rewrite S_INR ; apply Rlt_le, RinvN_pos |
  apply Rmult_le_compat_r ; intuition ;
  by apply Rlt_le, Rlt_Rminus]. 
  apply Rplus_lt_compat_l, Rmult_lt_compat_r ;
  [ rewrite S_INR ; apply RinvN_pos | 
  apply Rmult_lt_compat_r ; [by apply Rlt_Rminus|
  rewrite (S_INR i) ; intuition]].
  apply INR_lt, (Rle_mult_Rlt (/(b-a)*(x-a))).
  apply lt_0_INR, lt_0_Sn.
  rewrite (Rinv_l_sym (b-a)).
  apply Rmult_lt_compat_l.
  by apply Rinv_0_lt_compat, Rlt_Rminus.
  by apply Rplus_lt_compat_r.
  by apply Rgt_not_eq, Rlt_Rminus.
  rewrite -Rmult_assoc ; intuition.
  apply le_n_S, lt_le_S, INR_lt, (Rle_mult_Rlt (/(b-a)*(x-a))).
  apply lt_0_INR, lt_0_Sn.
  rewrite (Rinv_l_sym (b-a)).
  apply Rmult_lt_compat_l.
  by apply Rinv_0_lt_compat, Rlt_Rminus.
  by apply Rplus_lt_compat_r.
  by apply Rgt_not_eq, Rlt_Rminus.
  rewrite -Rmult_assoc ; intuition.
  apply le_n_S, INR_le, Rlt_le, (Rle_mult_Rlt (/(b-a)*(x-a))).
  apply lt_0_INR, lt_0_Sn.
  rewrite (Rinv_l_sym (b-a)).
  apply Rmult_lt_compat_l.
  by apply Rinv_0_lt_compat, Rlt_Rminus.
  by apply Rplus_lt_compat_r.
  by apply Rgt_not_eq, Rlt_Rminus.
  rewrite -Rmult_assoc ; intuition.
Qed.

Lemma RInt_part_nat_1 (a b : R) (n : nat) (x : R) : (0 < n)%nat -> (b <= x < a)
  -> { i : nat | nth 0 (RInt_part a b n) (S i) <= x <= nth 0 (RInt_part a b n) i /\ (i < n)%nat }.
Proof.
  move => Hn Hx ;
  case: (RInt_part_nat_0 _ _ n x Hn Hx) => i [Hi Hin].
  rewrite RInt_part_bound in Hi => //.
  rewrite nth_rev size_mkseq ?SSR_minus in Hi ; [ | by apply SSR_leq, le_n_S, lt_le_weak].
  rewrite nth_rev size_mkseq ?ssrnat.subSS ?SSR_minus in Hi ; 
  [ | by apply SSR_leq, lt_le_S, lt_n_S].
  rewrite -minus_Sn_m in Hi ; [ | by apply lt_le_S].
  exists (n - S i)%nat ; intuition.
Qed.

Lemma RInt_part_sorted_0 (a b : R) (n : nat) : (a <= b) -> sorted Rle (RInt_part a b n).
Proof.
  move => Hab ; apply sorted_compat => i ; 
  rewrite ?nth_compat size_compat size_mkseq => Hi ; simpl in Hi.
  case: n Hi => [|n] Hi.
  contradict Hi ; apply lt_n_O.
  rewrite ?nth_mkseq ?SSR_leq.
  rewrite -(Rplus_0_r (a + INR i * (b - a) / INR (S n))) ;
  have: (a + INR (S i) * (b - a) / INR (S n) = 
    (a + INR i * (b - a) / INR (S n) + (b-a)/INR (S n))).
    rewrite S_INR ; field ;
    apply Rgt_not_eq, lt_0_INR, lt_0_Sn.
  move => -> ; apply Rplus_le_compat_l, Rmult_le_pos.
  by apply (Rminus_le_0 a b).
  rewrite S_INR ; apply Rlt_le, RinvN_pos.
  by apply le_n_S, lt_le_S.
  by apply le_n_S, lt_le_weak.
Qed.
Lemma RInt_part_sorted_1 (a b : R) (n : nat) : (b <= a) -> sorted Rge (RInt_part a b n).
Proof.
  move => Hab ; case: n => // n ;
  rewrite (RInt_part_bound _ _ _ (lt_O_Sn _)) ;
  by apply sorted_le_rev, RInt_part_sorted_0.
Qed.

(** ** sequences lx *)

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

(** *** Sequences of local sup and inf *)

Fixpoint Seq_s_P (f : R -> R) (P : seq R) : seq Rbar :=
  match P with
    | [::] | [:: _] => [::]
    | h0 :: (h1 :: t) as P' => (Sup_fct f h0 h1) :: Seq_s_P f P'
  end.
Fixpoint Seq_i_P (f : R -> R) (P : seq R) : seq Rbar :=
  match P with
    | [::] | [:: _] => [::]
    | h0 :: (h1 :: t) as P' => (Inf_fct f h0 h1) :: Seq_i_P f P'
  end.

Lemma rcons_Seq_s_P (f : R -> R) (P : seq R) (t1 t0 : R) : 
  Seq_s_P f (rcons (rcons P t1) t0) = rcons (Seq_s_P f (rcons P t1)) (Sup_fct f t1 t0).
Proof.
  elim: P t1 t0 => // t P IHP t1 t0.
  rewrite rcons_cons ; simpl Seq_s_P at 1 ; rewrite IHP.
  have : ({t' : R & {P' | t' :: P' = (rcons P t1)}}).
  case: (P).
  exists t1 ; exists [::] => //.
  move => t2 s ; exists t2 ; exists ((rcons s t1)) ; by rewrite ?rcons_cons.
  case => t' [P' HP'] ; rewrite -HP' //=.
Qed.
Lemma rcons_Seq_i_P (f : R -> R) (P : seq R) (t1 t0 : R) : 
  Seq_i_P f (rcons (rcons P t1) t0) = rcons (Seq_i_P f (rcons P t1)) (Inf_fct f t1 t0).
Proof.
  elim: P t1 t0 => // t P IHP t1 t0.
  rewrite rcons_cons ; simpl Seq_i_P at 1 ; rewrite IHP.
  have : ({t' : R & {P' | t' :: P' = (rcons P t1)}}).
  case: (P).
  exists t1 ; exists [::] => //.
  move => t2 s ; exists t2 ; exists ((rcons s t1)) ; by rewrite ?rcons_cons.
  case => t' [P' HP'] ; rewrite -HP' //=.
Qed.

Lemma nth_Seq_s_P (f : R -> R) (P : seq R) (i : nat) : (S i < size P)%nat ->
  nth (Finite 0) (Seq_s_P f P) i = Sup_fct f (nth 0 P i) (nth 0 P (S i)).
Proof.
  case: P i => [i Hi | h P].
  by apply lt_n_O in Hi.
  elim: P h => [h i Hi | h P IH h' i Hi].
  by apply lt_S_n, lt_n_O in Hi.
  case: i Hi => // i Hi.
  apply (IH h i), lt_S_n, Hi.
Qed.
Lemma nth_Seq_i_P (f : R -> R) (P : seq R) (i : nat) : (S i < size P)%nat ->
  nth (Finite 0) (Seq_i_P f P) i = Inf_fct f (nth 0 P i) (nth 0 P (S i)).
Proof.
  case: P i => [i Hi | h P].
  by apply lt_n_O in Hi.
  elim: P h => [h i Hi | h P IH h' i Hi].
  by apply lt_S_n, lt_n_O in Hi.
  case: i Hi => // i Hi.
  apply (IH h i), lt_S_n, Hi.
Qed.

Lemma Seq_s_P_bound (f : R -> R) (P : seq R) :
  Seq_s_P f (rev P) = rev (Seq_s_P f P).
Proof.
  apply (rcons_dec (fun P => Seq_s_P f (rev P) = rev (Seq_s_P f P))) => // {P} P.
  apply (rcons_ind (fun P => forall t : R, 
    Seq_s_P f (rev (rcons P t)) = rev (Seq_s_P f (rcons P t)))) => // {P} P t IHP t0.
  rewrite rcons_Seq_s_P ?rev_rcons -IHP rev_rcons Sup_fct_bound => //=.
Qed.
Lemma Seq_i_P_bound (f : R -> R) (P : seq R) :
  Seq_i_P f (rev P) = rev (Seq_i_P f P).
Proof.
  apply (rcons_dec (fun P => Seq_i_P f (rev P) = rev (Seq_i_P f P))) => // {P} P.
  apply (rcons_ind (fun P => forall t : R, 
    Seq_i_P f (rev (rcons P t)) = rev (Seq_i_P f (rcons P t)))) => // {P} P t IHP t0.
  rewrite rcons_Seq_i_P ?rev_rcons -IHP rev_rcons Inf_fct_bound => //=.
Qed.

Lemma SF_sup_aux (f : R -> R) (a b : R) (n : nat) : 
  size (RInt_part a b n) = S (size (Seq_s_P f (RInt_part a b n))).
Proof.
  have Hs : (size (RInt_part a b n) = S n).
    by rewrite size_mkseq.
  elim: n (RInt_part a b n) Hs => {a b} [s Hs | n IHn s Hs].
    case: s Hs => // t ; by case.
  case: s Hs => // t s Hs /= ; rewrite (IHn s) ; case: s Hs => //= _ s ;
  apply eq_add_S.
Qed.
Definition SF_sup (f : R -> R) (a b : R) (n : nat) : SF_seq Rbar :=
  SF_make (RInt_part a b n) (Seq_s_P f (RInt_part a b n)) (SF_sup_aux f a b n).

Lemma SF_inf_aux (f : R -> R) (a b : R) (n : nat) : 
  size (RInt_part a b n) = S (size (Seq_i_P f (RInt_part a b n))).
Proof.
  have Hs : (size (RInt_part a b n) = S n).
    by rewrite size_mkseq.
  elim: n (RInt_part a b n) Hs => {a b} [s Hs | n IHn s Hs].
    case: s Hs => // t ; by case.
  case: s Hs => // t s Hs /= ; rewrite (IHn s) ; case: s Hs => //= _ s ;
  apply eq_add_S.
Qed.
Definition SF_inf (f : R -> R) (a b : R) (n : nat) : SF_seq Rbar :=
  SF_make (RInt_part a b n) (Seq_i_P f (RInt_part a b n)) (SF_inf_aux f a b n).

Lemma SF_sup_sorted_0 (f : R -> R) (a b : R) (n : nat) : (a <= b) ->
  SF_sorted Rle (SF_sup f a b n).
Proof.
  move => H ; rewrite /SF_sorted /SF_sup SF_seq_bij_lx ;
  by apply RInt_part_sorted_0.
Qed.
Lemma SF_sup_sorted_1 (f : R -> R) (a b : R) (n : nat) : (b <= a) ->
  SF_sorted Rge (SF_sup f a b n).
Proof.
  move => H ; rewrite /SF_sorted /SF_sup SF_seq_bij_lx ;
  by apply RInt_part_sorted_1.
Qed.
Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) : (0 < n)%nat ->
  SF_rev (SF_sup f a b n) = SF_sup f b a n.
Proof.
  move => Hn ;
  rewrite {2}/SF_sup /SF_make (RInt_part_bound b a) => // ;
  rewrite /SF_rev SF_seq_bij_lx SF_seq_bij_ly Seq_s_P_bound => //.
Qed.
Lemma SF_inf_sorted_0 (f : R -> R) (a b : R) (n : nat) : (a <= b) ->
  SF_sorted Rle (SF_inf f a b n).
Proof.
  move => H ; rewrite /SF_sorted /SF_inf SF_seq_bij_lx ;
  by apply RInt_part_sorted_0.
Qed.
Lemma SF_inf_sorted_1 (f : R -> R) (a b : R) (n : nat) : (b <= a) ->
  SF_sorted Rge (SF_inf f a b n).
Proof.
  move => H ; rewrite /SF_sorted /SF_sup SF_seq_bij_lx ;
  by apply RInt_part_sorted_1.
Qed.
Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) : (0 < n)%nat ->
  SF_rev (SF_inf f a b n) = SF_inf f b a n.
Proof.
  move => Hn ;
  rewrite {2}/SF_inf /SF_make (RInt_part_bound b a) => // ;
  rewrite /SF_rev SF_seq_bij_lx SF_seq_bij_ly Seq_i_P_bound => //.
Qed.

Lemma SF_sup_ge_f_0 (f : R -> R) (a b : R) (n : nat) : (0 < n)%nat ->
  forall x, (a <= x < b) -> Rbar_le (Finite (f x)) (SF_fun (SF_sup f a b n) (Finite 0) x).
Proof.
  move => Hn x Hx.
  case: n Hn => [Hn |n Hn].
  contradict Hn ; apply lt_n_O.
  case: (RInt_part_nat_0 _ _ _ _ Hn Hx) => {Hn} i [Hi Hin].
  rewrite (SF_fun_incr _ _ _ i).
  rewrite SF_seq_bij_ly nth_Seq_s_P.
  have H : (nth 0 (RInt_part a b (S n)) i <= nth 0 (RInt_part a b (S n)) (S i)).
    apply Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => s Hs /= ; apply Hs ; 
  exists x ; rewrite /Rmin /Rmax ; case : (Rle_dec (nth 0 (RInt_part a b (S n)) i)
    (nth 0 (RInt_part a b (S n)) (S i))) ; intuition.
  rewrite size_mkseq ; apply lt_n_S, Hin.
  apply SF_sup_sorted_0, Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  apply lt_S_n ; rewrite -SF_size_lx SF_seq_bij_lx size_mkseq ; 
  apply lt_n_S, Hin.
  by rewrite SF_seq_bij_lx.
Qed.
Lemma SF_sup_ge_f_1 (f : R -> R) (a b : R) (n : nat) : (0 < n)%nat ->
  forall x, (b <= x < a) -> Rbar_le (Finite (f x)) (SF_fun (SF_rev (SF_sup f a b n)) (Finite 0) x).
Proof.
  move => Hn ; rewrite SF_sup_bound => // ;
  apply SF_sup_ge_f_0 => //.
Qed.

Lemma SF_inf_le_f_0 (f : R -> R) (a b : R) (n : nat) : (0 < n)%nat ->
  forall x, (a <= x < b) -> Rbar_le (SF_fun (SF_inf f a b n) (Finite 0) x) (Finite (f x)).
Proof.
  move => Hn x Hx.
  case: n Hn => [Hn |n Hn].
  contradict Hn ; apply lt_n_O.
  case: (RInt_part_nat_0 _ _ _ _ Hn Hx) => {Hn} i [Hi Hin].
  rewrite (SF_fun_incr _ _ _ i).
  rewrite SF_seq_bij_ly nth_Seq_i_P.
  have H : (nth 0 (RInt_part a b (S n)) i <= nth 0 (RInt_part a b (S n)) (S i)).
    apply Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => s Hs /= ; apply Hs ; 
  exists x ; rewrite /Rmin /Rmax ; case : (Rle_dec (nth 0 (RInt_part a b (S n)) i)
    (nth 0 (RInt_part a b (S n)) (S i))) ; intuition.
  rewrite size_mkseq ; apply lt_n_S, Hin.
  apply SF_inf_sorted_0, Rlt_le, Rle_lt_trans with (r2 := x) ; intuition.
  apply lt_S_n ; rewrite -SF_size_lx SF_seq_bij_lx size_mkseq ; 
  apply lt_n_S, Hin.
  by rewrite SF_seq_bij_lx.
Qed.
Lemma SF_inf_le_f_1 (f : R -> R) (a b : R) (n : nat) : (0 < n)%nat ->
  forall x, (b <= x < a) -> Rbar_le (SF_fun (SF_rev (SF_inf f a b n)) (Finite 0) x) (Finite (f x)).
Proof.
  move => Hn ; rewrite SF_inf_bound => // ;
  apply SF_inf_le_f_0 => //.
Qed.

Lemma SF_sup_finite (f : R -> R) (a b : R) (pr : Riemann_integrable f a b) (n : nat) :
  exists l : seq R, size l = n /\ SF_ly (SF_sup f a b n) = map Finite l.
Proof.
  case: n => [| n].
  by exists [::].
  case : (Riemann_integrable_bound f a b pr) => {pr} s pr ;
  exists (map real (SF_ly (SF_sup f a b (S n)))) ; split.
  rewrite size_map SF_size_ly (eq_add_S (SF_size (SF_sup f a b (S n))) (S n)) => // ;
  rewrite -SF_size_lx SF_seq_bij_lx size_mkseq => //.
  rewrite SF_seq_bij_ly.
  apply (@eq_from_nth _ (Finite 0)).
  by rewrite ?size_map.
  move => i Hi ;
  rewrite (@nth_map R 0 Rbar (Finite 0) Finite i) ?size_map => // ;
  rewrite (@nth_map Rbar (Finite 0) R 0 real i _ Hi) nth_Seq_s_P ?nth_mkseq ; 
  apply SSR_leq, lt_n_S in Hi ; rewrite -SF_sup_aux size_mkseq in Hi ; 
  [ | by apply SSR_leq | by apply SSR_leq, lt_le_weak | by rewrite size_mkseq ].
  
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; case => [l| | ] [ub lub] //=.
  suff H : (Rbar_le p_infty (Finite s)).
    apply Rbar_le_not_lt in H ; by rewrite /= in H.
  apply: lub => {ub} _ [x [-> lub]] ;
  apply Rbar_finite_le, pr ; split ; [apply Rle_trans with (2 := proj1 lub)
  | apply Rle_trans with (1 := proj2 lub)] ; rewrite /Rmin /Rmax.
  case: (Rle_dec a b) => Hab.
  have Hi' : (i < Peano.pred (size (RInt_part a b (S n))))%nat.
    rewrite size_mkseq /= ; by apply lt_S_n.
  move : (proj1 (sorted_nth Rle _ ) (RInt_part_sorted_0 _ _ (S n) Hab) i Hi' 0) ;
  rewrite ?nth_mkseq => // [H | | ].
  case (Rle_dec (a + INR i * (b - a) / INR (S n))
      (a + INR (S i) * (b - a) / INR (S n))) => {H} // _.
Admitted.

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
    rewrite ?SF_seq_bij_ly nth_Seq_s_P => //.
    rewrite size_mkseq in Hi ;
    rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; 
    case => // ; simpl projT1 ; rewrite ?nth_mkseq ; try apply SSR_leq => // ;
    set a0 := (a + INR i * (b - a) / INR (S n)) ;
    set b0 := (a + INR (S i) * (b - a) / INR (S n)).
    case => ub _ ; case: (ub (f a0)) => //= ;
    exists a0 ; split => // ; by apply Rmin_Rmax_l.
    by apply lt_le_weak.
  apply Rbar_div_pos_eq ; move: H ; rewrite ?SF_seq_bij_ly.
  rewrite (RInt_part_bound b a) ?Seq_s_P_bound ; try by apply lt_O_Sn.
  rewrite !foldr_rev.
  case: (Seq_s_P f (RInt_part a b (S n))) => // t s ; elim: s t => //= t s IH t0 Hnth ;
  rewrite (IH t).
  have: (Rbar_plus t (Rbar_plus t0 (Finite 0)) = (Rbar_plus t0 (Rbar_plus t (Finite 0)))).
    case: (t) => [x | | ] ; case: (t0) => [y | | ] //=.
    apply Rbar_finite_eq ; ring.
  move => -> /=.
 set x := (foldl (fun x y : Rbar => Rbar_plus y x) (Rbar_plus t (Finite 0)) s).
Qed.
Lemma RInt_Sum_i_bound f a b n :
  RInt_Sum_i f a b n = - RInt_Sum_i f b a n.
Proof.
  rewrite /RInt_Sum_i -(Ropp_minus_distr' b a) /Rdiv ?Ropp_mult_distr_l_reverse.
  apply Ropp_eq_compat, Rmult_eq_compat_l.
  case: n => // n.
  rewrite -SF_inf_bound ; [|apply lt_O_Sn].
  rewrite SF_ly_rev SF_seq_bij_ly map_rev.
  move : (map real (Seq_i_P f (RInt_part b a (S n)))) => //= {f a b n} s.
  rewrite foldr_rev ; case: s (0) => //= t s ; elim: s t => //= t s IH t0 x0.
  by rewrite -?Rplus_assoc -IH (Rplus_comm t).
Qed.

(** * A new Riemann_integrable in Prop *)

Definition is_RInt (f : R -> R) (a b : R) :=
  Inf_seq (RInt_Sum_s f a b) = Sup_seq (RInt_Sum_i f a b).

Lemma is_RInt_bound (f : R -> R) (a b : R) :
  is_RInt f a b -> is_RInt f b a.
Proof.
  rewrite /is_RInt => H.
  
Qed.

Lemma is_RInt_correct_0 (f : R -> R) (a b : R) :
  is_RInt f a b -> (exists M, forall x, Rmin a b <= x <= Rmax a b -> Rabs (f x) <= M) 
    -> Riemann_integrable f a b.
Proof.
  
Qed.