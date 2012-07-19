Require Import Reals Div2 ConstructiveEpsilon.
Require Import ssreflect ssrbool eqtype seq.
Require Import Markov Rcomplements Floor Total_sup Sup_seq Lim_seq Derive SF_seq.


(*
(** * Compatibility with ssreflect *)

(** ** seq *)
Lemma size_belast {T : Type} (s : seq T) : size (belast s) = Peano.pred (size s).
Proof.
  case: s => // t s ; elim: s t => // t s /= IHs t0 ; by rewrite IHs.
Qed.


(** ** Order *)

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


(** ** SF_seq definition *)




(** ** SF_size *)


(** ** Order *)

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


(** ** SF_fun definition *)


Lemma SF_fun_map {T T0 : Type} (f : T -> T0) (s : SF_seq) x0 :
  forall x, SF_fun (SF_map f s) (f x0) x = f (SF_fun s x0 x).
Proof.
  apply SF_cons_dec with (s := s) => {s} [x1|h s] x ; rewrite /SF_fun /=.
  case: Rle_dec => //.
  case: Rlt_dec => // _.
  move: h ; apply SF_cons_ind with (s := s) => {s} [x1 | h s IH] h0 /=.
  case: Rle_dec => //.
  case: Rlt_dec => //.
Qed.

(** ** (seq R) and Rlist *)

Lemma SF_sorted_compat {T : Type} (s : @SF_seq T) :
  SF_sorted Rle s <-> ordered_Rlist (seq2Rlist (SF_lx s)).
Proof.
  split => H ; apply sorted_compat => //.
Qed.
*)

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

Lemma pow2_pos (n : nat) : (0 < pow2 n)%nat.
Proof.
  apply INR_lt ; rewrite pow2_INR ; intuition.
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

Lemma RInt_part_sort (a b : R) (n : nat) : a <= b -> sorted Rle (RInt_part a b n).
Proof.
  move => Hab ; apply sorted_nth => i Hi x0 ; 
  rewrite ?size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ;
  [ |apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
  apply Rminus_le_0 ; field_simplify ; 
  [| apply Rgt_not_eq ; intuition] ; rewrite -?Rdiv_1 ;
  apply Rdiv_le_pos ; intuition.
  rewrite Rplus_comm ; by apply (proj1 (Rminus_le_0 _ _)).
Qed.

Lemma RInt_part_nat (a b : R) (n : nat) (x : R) : (a <= x <= b) -> 
  {i : nat |
  nth 0 (RInt_part a b n) i <= x < nth 0 (RInt_part a b n) (S i) /\
  (S (S i) < size (RInt_part a b n))%nat} +
  {nth 0 (RInt_part a b n) (pow2 n - 1) <= x <=
   nth 0 (RInt_part a b n) (pow2 n)}.
Proof.
  move: (sorted_dec (RInt_part a b n) 0 x) => Hdec Hx.
  have Hs : sorted Rle (RInt_part a b n) ;
    [ apply RInt_part_sort, Rle_trans with (r2 := x) ; intuition 
    | move: (Hdec Hs) => {Hdec Hs} Hdec].
  have Hx' : (head 0 (RInt_part a b n) <= x <= last 0 (RInt_part a b n)).
    rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR.
    have: a + 0 * (b - a) / 2 ^ n = a ; 
    [ field ; apply Rgt_not_eq ; intuition | move => ->] ;
    have: a + 2^n * (b - a) / 2 ^ n = b ; 
    [ field ; apply Rgt_not_eq ; intuition | move => ->] ; by [].
  case: (Hdec Hx') => {Hdec Hx'} [[i Hi]|Hi].
  left ; by exists i.
  right ; rewrite size_mkseq /= in Hi ; intuition.
  by rewrite -minus_n_O in H2.
Qed.

(** ** sequences lx *)

(** *** Values *)

Definition SF_val_ly (f : R -> R) (a b : R) (n : nat) : seq R :=
  behead (pairmap (fun x y => f ((x+y)/2)) 0 (RInt_part a b n)).
Definition SF_val_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (fun x y => f ((x+y)/2)) (RInt_part a b n) 0.
Definition SF_val_fun (f : R -> R) (a b : R) (n : nat) (x : R) : R :=
  SF_fun_f2 (fun x y => f ((x+y)/2)) (RInt_part a b n) (0,0) x.

Lemma SF_val_ly_bound (f : R -> R) (a b : R) (n : nat) :
  SF_val_ly f a b n = rev (SF_val_ly f b a n).
Proof.
  rewrite /SF_val_ly (RInt_part_bound b a).
  case: (RInt_part a b n) => [| h s] // ; elim: s h => [| h0 s IH] h //=.
  rewrite ?rev_cons.
  replace (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rcons (rev s) h0) h))
    with (rcons (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rev s) h0)) (f ((h0+h)/2))).
  rewrite behead_rcons.
  rewrite rev_rcons Rplus_comm -rev_cons -IH //.
  rewrite size_pairmap size_rcons ; apply lt_O_Sn.
  move: (0) h h0 {IH} ; apply rcons_ind with (s := s) => {s} [| s h1 IH] x0 h h0 //.
  rewrite ?rev_rcons /= IH //.
Qed.

Lemma ad_SF_val_fun (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (SF_val_fun f a b n) a b 
      (seq2Rlist (RInt_part a b n)) (seq2Rlist (SF_val_ly f a b n)))
  /\ (~(a <= b) -> adapted_couple (SF_val_fun f b a n) a b 
      (seq2Rlist (RInt_part b a n)) (seq2Rlist (SF_val_ly f b a n))).
Proof.
  wlog : a b / (a <= b) => Hw.
    split ; case: (Rle_dec a b) => // Hab _.
    by apply Hw.
    apply StepFun_P2 ; apply Hw ; by apply Rlt_le, Rnot_le_lt.
  split ; case: (Rle_dec a b) => // {Hw} Hab _.
  have : (a = head 0 (SF_lx (SF_val_seq f a b n))) ; 
  [rewrite SF_lx_f2 /= ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have : (b = last 0 (SF_lx (SF_val_seq f a b n))) ; 
  [rewrite SF_lx_f2 ;
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) 
    with (RInt_part a b n) by intuition ;
    rewrite -nth_last size_mkseq nth_mkseq => //= ; rewrite pow2_INR ;
    field ; apply Rgt_not_eq ; intuition | move => {3} ->].
  replace (RInt_part a b n) 
    with (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) by intuition ;
  rewrite -(SF_lx_f2 (fun x y => f ((x+y)/2))).
  rewrite /SF_val_ly -SF_ly_f2.
  apply (ad_SF_compat (SF_val_seq f a b n)).
  by apply SF_sorted_f2, RInt_part_sort.
Qed.

Definition sf_SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  case : (Rle_dec a b) => Hab.
  exists (SF_val_fun f a b n) ;
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
  exists (SF_val_fun f b a n) ;
  exists (seq2Rlist (RInt_part b a n)) ;
  exists (seq2Rlist (SF_val_ly f b a n)) ; by apply ad_SF_val_fun.
Defined.
Lemma SF_val_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (sf_SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /sf_SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_val_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (sf_SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (SF_val_ly f a b n)
    | right _ => seq2Rlist (SF_val_ly f b a n)
  end.
Proof.
  rewrite /sf_SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_val_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_val_fun f a b n x = 
    match (RInt_part_nat a b n x Hx) with
      | inleft H => f (a + (2*INR (projT1 H) + 1) * (b-a) / 2^(S n))
      | inright _ => f (a + (2^(S n) - 1) * (b-a) / 2^(S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  case: RInt_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] /=.
(* i < 2^n - 1 *)
  rewrite /SF_val_fun /SF_fun_f2.
  replace (a + (2 * INR i + 1) * (b - a) / (2 * 2 ^ n)) 
    with ((nth 0 (RInt_part a b n) i + nth 0 (RInt_part a b n) (S i)) / 2) ;
    [ | rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ; 
    [field ; apply Rgt_not_eq | apply SSR_leq | apply SSR_leq ] ; intuition].
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = 2^n - 1 *)
  replace (a + (2 * 2^n - 1) * (b - a) / (2 * 2 ^ n)) 
    with ((nth 0 (RInt_part a b n) (pow2 n - 1) + nth 0 (RInt_part a b n) (pow2 n)) / 2) ;
    [ | rewrite ?nth_mkseq ?minus_INR ?pow2_INR /= ; 
    [field ; apply Rgt_not_eq | apply pow2_pos | 
    apply SSR_leq | apply SSR_leq ] ; intuition].
  move: (pow2_pos n) x Hx ; have: (pow2 n = size (RInt_part a b n) - 1)%nat ;
    [ rewrite size_mkseq ; intuition | move => ->].
  rewrite /SF_val_fun /SF_fun_f2.
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  rewrite -minus_n_O in Hi |- * ; case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_n_O in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
Qed.

Definition RInt_val (f : R -> R) (a b : R) (n : nat) :=
  ((b-a)/2^n) * foldr Rplus 0 (SF_val_ly f a b n).

Lemma RInt_val_correct (f : R -> R) (a b : R) (n : nat) :
  RInt_val f a b n = RiemannInt_SF (sf_SF_val_fun f a b n).
Proof.
have H : (forall a b i, (S i < size (RInt_part a b n))%nat -> 
  nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/2^n).
  move => {a b} a b i Hi ; rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR.
  field ; apply Rgt_not_eq ; intuition.
  apply SSR_leq ; intuition.
  apply SSR_leq ; intuition.
rewrite /RInt_val /RiemannInt_SF SF_val_subdiv SF_val_subdiv_val ;
case: Rle_dec => Hab.
(* a <= b *)
  rewrite /SF_val_ly ; case: (RInt_part a b n) (H a b) => [| h s] /=.
  move => _ ; field ; apply Rgt_not_eq ; intuition.
  elim: s h => [|h0 s IH] h Hs /=.
  field ; apply Rgt_not_eq ; intuition.
  rewrite Rmult_plus_distr_l (IH) ; move: (Hs O (lt_n_S _ _ (lt_O_Sn _))) => /= Hs'.
  rewrite Hs' ; field ; apply Rgt_not_eq ; intuition.
  move => i Hi ; apply (Hs (S i)), lt_n_S, Hi.
(* ~ a <= b *)
  rewrite (SF_val_ly_bound f a b n) /SF_val_ly.
  case: (RInt_part b a n) (H b a) => [| h s] /=.
  move => _ ; field ; apply Rgt_not_eq ; intuition.
  rewrite -Rminus_0_l -{4}(Rmult_0_l ((b-a)/2^n)) ;
  elim: s {3 4}(0) h => [|h0 s IH] x0 h Hs /=.
  field ; apply Rgt_not_eq ; intuition.
  rewrite rev_cons foldr_rcons (IH) ; move: (Hs O (lt_n_S _ _ (lt_O_Sn _))) => /= Hs'.
  rewrite Hs' ; field ; apply Rgt_not_eq ; intuition.
  move => i Hi ; apply (Hs (S i)), lt_n_S, Hi.
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

Lemma Sup_fct_maj (f : R -> R) (a b : R) (M : R) : 
  (forall x, Rmin a b <= x <= Rmax a b -> f x <= M) ->
  Finite (real (Sup_fct f a b)) = Sup_fct f a b.
Proof.
  rewrite /Sup_fct /Lub_Rbar_ne => H ; 
  case: (ex_lub_Rbar_ne _ _) ; case => //= [ [_ lub] | [ub _] ].
  absurd (Rbar_le p_infty (Finite M)).
    by apply Rbar_lt_not_le.
  apply: lub => _ [x [-> lub]].
  by apply Rbar_finite_le, H.
  absurd (Rbar_le (Finite (f a)) m_infty).
    by apply Rbar_lt_not_le.
  apply: ub ; exists a ; split => // ; apply Rmin_Rmax_l.
Qed.
Lemma Inf_fct_min (f : R -> R) (a b : R) (M : R) : 
  (forall x, Rmin a b <= x <= Rmax a b -> M <= f x) ->
  Finite (real (Inf_fct f a b)) = Inf_fct f a b.
Proof.
  rewrite /Inf_fct /Glb_Rbar_ne => H ; 
  case: (ex_glb_Rbar_ne _ _) ; case => //= [ [lb _] | [_ glb] ].
  absurd (Rbar_le p_infty (Finite (f a))).
    by apply Rbar_lt_not_le.
  apply: lb ; exists a ; split => // ; apply Rmin_Rmax_l.
  absurd (Rbar_le (Finite M) m_infty).
    by apply Rbar_lt_not_le.
  apply: glb => _ [x [-> glb]].
  by apply Rbar_finite_le, H.
Qed.

(** *** SF_seq of local sup *)
(*
Definition _P (f : R -> R) (P : seq R) x0 : SF_seq :=
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
*)
(** *** SF_sup and SF_inf *)

Definition SF_sup_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Sup_fct f) (RInt_part a b n) 0.
Lemma SF_sup_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_sup_seq f a b n) = RInt_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_sup_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_sup_seq f a b n) = behead (pairmap (Sup_fct f) 0 (RInt_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Definition SF_inf_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Inf_fct f) (RInt_part a b n) 0.
Lemma SF_inf_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_inf_seq f a b n) = RInt_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_inf_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_inf_seq f a b n) = behead (pairmap (Inf_fct f) 0 (RInt_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_sup_seq f a b n) = SF_sup_seq f b a n.
Proof.
  rewrite /SF_sup_seq RInt_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Sup_fct_bound.
Qed.
Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) : 
  SF_rev (SF_inf_seq f a b n) = SF_inf_seq f b a n.
Proof.
  rewrite /SF_inf_seq RInt_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Inf_fct_bound.
Qed.

Lemma SF_sup_infty (f : R -> R) (a b : R) (n : nat) :
  (forall i, Rbar_lt m_infty (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i)).
Proof.
  move => i ; case: (le_dec (S (S i)) (size (RInt_part a b n))) => Hi.
  rewrite SF_ly_f2 nth_behead (nth_pairmap 0) ; [|by apply SSR_leq].
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; 
  case => [l | | ] [ub lub] //=.
  absurd (Rbar_le (Finite (f (nth 0 (0 :: RInt_part a b n) (S i)))) m_infty).
  by apply Rbar_lt_not_le.
  apply ub ; exists (nth 0 (0 :: RInt_part a b n) (S i)) ; split => // ; 
  apply Rmin_Rmax_l.
  rewrite nth_default => // ; apply SSR_leq ; apply not_le in Hi ; 
  rewrite SF_ly_f2 size_behead size_pairmap ; rewrite size_mkseq /= in Hi |- * ; 
  intuition.
Qed.
Lemma SF_inf_infty (f : R -> R) (a b : R) (n : nat) :
  (forall i, Rbar_lt (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i) p_infty).
Proof.
  move => i ; case: (le_dec (S (S i)) (size (RInt_part a b n))) => Hi.
  rewrite SF_ly_f2 nth_behead (nth_pairmap 0) ; [|by apply SSR_leq].
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) ; 
  case => [l | | ] [ub lub] //=.
  absurd (Rbar_le p_infty (Finite (f (nth 0 (0 :: RInt_part a b n) (S i))))).
  by apply Rbar_lt_not_le.
  apply ub ; exists (nth 0 (0 :: RInt_part a b n) (S i)) ; split => // ; 
  apply Rmin_Rmax_l.
  rewrite nth_default => // ; apply SSR_leq ; apply not_le in Hi ; 
  rewrite SF_ly_f2 size_behead size_pairmap ; rewrite size_mkseq /= in Hi |- * ; 
  intuition.
Qed.

Lemma SF_sup_real_0 (f : R -> R) (a b : R) (n : nat) :
  SF_map (fun x => Finite (real x)) (SF_sup_seq f a b n) = SF_sup_seq f a b n 
    -> {M : R | forall x, Rmin a b <= x <= Rmax a b -> f x <= M}.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    move => H ; rewrite Rmin_comm Rmax_comm ; apply Hw.
    apply Rlt_le, Rnot_le_lt, Hab.
    apply SF_rev_inj ; by rewrite SF_map_rev SF_sup_bound.
    
  rewrite SF_map_f2 => H.
  have: behead (pairmap (fun x y : R => Finite (real (Sup_fct f x y))) 0 (RInt_part a b n))
    = behead (pairmap (Sup_fct f) 0 (RInt_part a b n)) => [| {H} H].
    by rewrite -SF_ly_f2 -SF_sup_ly H.
  set M := foldr Rmax 0 (behead
      (pairmap (fun x y : R => (real (Sup_fct f x y))) 0
         (RInt_part a b n))).
  exists M => x ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ Hx.
  case: (RInt_part_nat _ _ n _ Hx) => {Hx} [ [i [Hx Hi]] | Hx].
(* S (S i) < size (RInt_part a b n) *)
  apply Rle_trans with 
    (r2 := real (Sup_fct f (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i)))).
  apply Rbar_finite_le ;
  replace (Finite (real (Sup_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i))))) 
    with (Sup_fct f (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i))).
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l [ub _] /= ; 
  apply: ub ; exists x ; split => //.
  have H0 : nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx | 
    rewrite /Rmin /Rmax ; case: Rle_dec => // _ {H0}] ; intuition.
  replace (nth 0 (RInt_part a b n) i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition.
  rewrite -(nth_pairmap _ (Finite 0)) ; [| apply SSR_leq ; intuition].
  rewrite -(nth_behead (Finite 0)) -{1}H.
  rewrite ?nth_behead ?(nth_pairmap 0) // ; try apply SSR_leq ; intuition.
  replace (nth 0 (RInt_part a b n) i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition.
  rewrite /M -(nth_pairmap _ 0 (fun x y => real (Sup_fct f x y))) ; 
    [| apply SSR_leq ; intuition].
  rewrite -(size_pairmap (fun x y => real (Sup_fct f x y)) 0) in Hi.
  case: (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (RInt_part a b n)) i Hi {x Hx M H} 
    => [|h s] //= i Hi.
    by apply lt_n_O in Hi.
  apply lt_S_n in Hi ; elim: s i Hi => {h} [| h s IH] //= i Hi.
  by apply lt_n_O in Hi.
  apply lt_S_n in Hi ; case: i Hi => //= [| i] Hi.
  apply RmaxLess1.
  by apply Rle_trans with (2 := RmaxLess2 _ _), IH .
(* i = 2^n - 1 *)
  apply Rle_trans with 
    (r2 := real (Sup_fct f (nth 0 (RInt_part a b n) (pow2 n - 1)) (nth 0 (RInt_part a b n) (pow2 n)))).
  apply Rbar_finite_le ;
  replace (Finite (real (Sup_fct f (nth 0 (RInt_part a b n) _)
    (nth 0 (RInt_part a b n) _)))) 
    with (Sup_fct f (nth 0 (RInt_part a b n) (pow2 n - 1)) (nth 0 (RInt_part a b n) (pow2 n))).
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l [ub _] /= ; 
  apply: ub ; exists x ; split => //.
  have H0 : nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (pow2 n) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx | 
    rewrite /Rmin /Rmax ; case: Rle_dec => // _ {H0}] ; intuition.
  replace (nth 0 (RInt_part a b n) (pow2 n - 1)) with (nth 0 (0::RInt_part a b n) (S (pow2 n - 1))) by intuition.
  replace (nth 0 (RInt_part a b n) (pow2 n)) with (nth 0 (RInt_part a b n) (S (pow2 n - 1))).
  rewrite -(nth_pairmap _ (Finite 0)) ; [| apply SSR_leq ; 
    rewrite size_mkseq -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
    apply INR_lt ; rewrite pow2_INR ; intuition].
  rewrite -(nth_behead (Finite 0)) -{1}H.
  rewrite ?nth_behead ?(nth_pairmap 0) // ; try apply SSR_leq ; 
  rewrite size_mkseq -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
  apply INR_lt ; rewrite pow2_INR ; intuition.
  rewrite -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
  apply INR_lt ; rewrite pow2_INR ; intuition.
  
  replace (nth 0 (RInt_part a b n) (pow2 n - 1)) with (nth 0 (0::RInt_part a b n) (S (pow2 n - 1))) by intuition.
  replace (nth 0 (RInt_part a b n) (pow2 n)) with (nth 0 (RInt_part a b n) (S (pow2 n - 1))).
  rewrite /M -(nth_pairmap _ 0 (fun x y => real (Sup_fct f x y))) ; [| apply SSR_leq ; 
    rewrite size_mkseq -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
    apply INR_lt ; rewrite pow2_INR ; intuition].
  rewrite -pred_of_minus -(S_pred (pow2 n) 0) ; intuition.
  have : (0 < pow2 n)%nat.
    apply INR_lt ; rewrite pow2_INR ; intuition.
  replace (pow2 n) with 
    (Peano.pred (size (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (RInt_part a b n)))).
  
  case: (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (RInt_part a b n)) {x H0 H1 M H}
    => [|h s] //= H.
    by apply Rle_refl.
  case: s H => [H |h0 s _] /=.
    by apply lt_n_O in H.
  elim: s h0 => {h} [|h0 s IH] //= h.
  apply RmaxLess1.
  apply Rle_trans with (2 := RmaxLess2 _ _), IH .
  rewrite size_pairmap size_mkseq //.
  apply INR_lt ; rewrite pow2_INR ; intuition.
  rewrite -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
    apply INR_lt ; rewrite pow2_INR ; intuition.
Qed.
Lemma SF_sup_real_1 (f : R -> R) (a b : R) (n : nat) M :
  (forall x, Rmin a b <= x <= Rmax a b -> f x <= M) ->
   SF_map (fun x => Finite (real x)) (SF_sup_seq f a b n) = SF_sup_seq f a b n.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm => H ; apply SF_rev_inj ;
    rewrite SF_map_rev SF_sup_bound ; apply Hw => //.
    apply Rlt_le, Rnot_le_lt, Hab.
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ H ; apply SF_lx_ly_inj.
  by rewrite SF_map_lx.
  rewrite SF_map_ly.
  apply eq_from_nth with (x0 := Finite 0).
  by rewrite size_map.
  move => i Hi ; rewrite size_map in Hi ; rewrite (nth_map (Finite 0)) //.
  move: (SF_sup_infty f a b n i) => Hm.
  have: Rbar_le (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i) (Finite M).
    rewrite SF_size_ly -ssrnat.ltnS -SF_size_lx SF_lx_f2 in Hi.
    move: Hm ; rewrite SF_ly_f2 nth_behead (nth_pairmap 0) //.
  have Hx : forall x i , (ssrnat.leq (S (S i)) (size(RInt_part a b n))) -> 
    Rmin (nth 0 (0 :: RInt_part a b n) (S i))
    (nth 0 (RInt_part a b n) (S i)) <= x <=
    Rmax (nth 0 (0 :: RInt_part a b n) (S i))
    (nth 0 (RInt_part a b n) (S i)) -> a <= x <= b.
    move => x {i Hi} i Hi lub ; split.
    (* * a <= x *)
    apply Rle_trans with (2 := proj1 lub) ; apply Rmin_case.
    pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with (nth 0 (RInt_part a b n) i) by intuition ; 
    apply sorted_head.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    simpl ; field ; apply Rgt_not_eq ; intuition.
    pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
    apply sorted_head.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    simpl ; field ; apply Rgt_not_eq ; intuition.
    (* * x <= b *)
    apply Rle_trans with (1 := proj2 lub) ; apply Rmax_lub.
    pattern b at 2 ; replace b with (last 0 (RInt_part a b n)).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with (nth 0 (RInt_part a b n) i) by intuition ; 
    apply sorted_last.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; field ; apply Rgt_not_eq ; intuition.
    pattern b at 2 ; replace b with (last 0 (RInt_part a b n)).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with (nth 0 (RInt_part a b n) i) by intuition ; 
    apply sorted_last.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; field ; apply Rgt_not_eq ; intuition.

  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; 
  case => [l | | ] [ub lub] //= _ ;
  apply: lub => _ [x [-> lub]] ;
  apply Rbar_finite_le, H, (Hx x i) => //.

  case: (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i) Hm => //= _ ; case => //.
Qed.

Lemma SF_inf_real_0 (f : R -> R) (a b : R) (n : nat) :
  SF_map (fun x => Finite (real x)) (SF_inf_seq f a b n) = SF_inf_seq f a b n 
    -> {M : R | forall x, Rmin a b <= x <= Rmax a b -> M <= f x}.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    move => H ; rewrite Rmin_comm Rmax_comm ; apply Hw.
    apply Rlt_le, Rnot_le_lt, Hab.
    apply SF_rev_inj ; by rewrite SF_map_rev SF_inf_bound.
    
  rewrite SF_map_f2 => H.
  have: behead (pairmap (fun x y : R => Finite (real (Inf_fct f x y))) 0 (RInt_part a b n))
    = behead (pairmap (Inf_fct f) 0 (RInt_part a b n)) => [| {H} H].
    by rewrite -SF_ly_f2 -SF_inf_ly H.
  set M := foldr Rmin 0 (behead
      (pairmap (fun x y : R => (real (Inf_fct f x y))) 0
         (RInt_part a b n))).
  exists M => x ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ Hx.
  case: (RInt_part_nat _ _ n _ Hx) => {Hx} [ [i [Hx Hi]] | Hx].
(* S (S i) < size (RInt_part a b n) *)
  apply Rle_trans with 
    (r2 := real (Inf_fct f (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i)))).

  replace (nth 0 (RInt_part a b n) i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition.
  rewrite /M -(nth_pairmap _ 0 (fun x y => real (Inf_fct f x y))) ; 
    [| apply SSR_leq ; intuition].
  rewrite -(size_pairmap (fun x y => real (Inf_fct f x y)) 0) in Hi.
  case: (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (RInt_part a b n)) i Hi {x Hx M H} 
    => [|h s] //= i Hi.
    by apply lt_n_O in Hi.
  apply lt_S_n in Hi ; elim: s i Hi => {h} [| h s IH] //= i Hi.
  by apply lt_n_O in Hi.
  apply lt_S_n in Hi ; case: i Hi => //= [| i] Hi.
  apply Rmin_l.
  by apply Rle_trans with (1 := Rmin_r _ _), IH .

  apply Rbar_finite_le ;
  replace (Finite (real (Inf_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i))))) 
    with (Inf_fct f (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i))).
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => l [ub _] /= ; 
  apply: ub ; exists x ; split => //.
  have H0 : nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx | 
    rewrite /Rmin /Rmax ; case: Rle_dec => // _ {H0}] ; intuition.
  replace (nth 0 (RInt_part a b n) i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition.
  rewrite -(nth_pairmap _ (Finite 0)) ; [| apply SSR_leq ; intuition].
  rewrite -(nth_behead (Finite 0)) -{1}H.
  rewrite ?nth_behead ?(nth_pairmap 0) // ; try apply SSR_leq ; intuition.

(* i = 2^n - 1 *)
  apply Rle_trans with 
    (r2 := real (Inf_fct f (nth 0 (RInt_part a b n) (pow2 n - 1)) (nth 0 (RInt_part a b n) (pow2 n)))).

  replace (nth 0 (RInt_part a b n) (pow2 n - 1)) with (nth 0 (0::RInt_part a b n) (S (pow2 n - 1))) by intuition.
  replace (nth 0 (RInt_part a b n) (pow2 n)) with (nth 0 (RInt_part a b n) (S (pow2 n - 1))).
  rewrite /M -(nth_pairmap _ 0 (fun x y => real (Inf_fct f x y))) ; [| apply SSR_leq ; 
    rewrite size_mkseq -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
    apply INR_lt ; rewrite pow2_INR ; intuition].
  rewrite -pred_of_minus -(S_pred (pow2 n) 0) ; intuition.
  have : (0 < pow2 n)%nat.
    apply INR_lt ; rewrite pow2_INR ; intuition.
  replace (pow2 n) with 
    (Peano.pred (size (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (RInt_part a b n)))).
  case: (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (RInt_part a b n)) {x H0 H1 M H}
    => [|h s] //= H.
    by apply Rle_refl.
  case: s H => [H |h0 s _] /=.
    by apply lt_n_O in H.
  elim: s h0 => {h} [|h0 s IH] //= h.
  apply Rmin_l.
  apply Rle_trans with (1 := Rmin_r _ _), IH .
  rewrite size_pairmap size_mkseq //.
  apply INR_lt ; rewrite pow2_INR ; intuition.
  rewrite -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
    apply INR_lt ; rewrite pow2_INR ; intuition.

  apply Rbar_finite_le ;
  replace (Finite (real (Inf_fct f (nth 0 (RInt_part a b n) _)
    (nth 0 (RInt_part a b n) _)))) 
    with (Inf_fct f (nth 0 (RInt_part a b n) (pow2 n - 1)) (nth 0 (RInt_part a b n) (pow2 n))).
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => l [ub _] /= ; 
  apply: ub ; exists x ; split => //.
  have H0 : nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (pow2 n) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx | 
    rewrite /Rmin /Rmax ; case: Rle_dec => // _ {H0}] ; intuition.
  replace (nth 0 (RInt_part a b n) (pow2 n - 1)) with (nth 0 (0::RInt_part a b n) (S (pow2 n - 1))) by intuition.
  replace (nth 0 (RInt_part a b n) (pow2 n)) with (nth 0 (RInt_part a b n) (S (pow2 n - 1))).
  rewrite -(nth_pairmap _ (Finite 0)) ; [| apply SSR_leq ; 
    rewrite size_mkseq -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
    apply INR_lt ; rewrite pow2_INR ; intuition].
  rewrite -(nth_behead (Finite 0)) -{1}H.
  rewrite ?nth_behead ?(nth_pairmap 0) // ; try apply SSR_leq ; 
  rewrite size_mkseq -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
  apply INR_lt ; rewrite pow2_INR ; intuition.
  rewrite -pred_of_minus -(S_pred (pow2 n) 0) ; intuition ;
  apply INR_lt ; rewrite pow2_INR ; intuition.
Qed.
Lemma SF_inf_real_1 (f : R -> R) (a b : R) (n : nat) M :
  (forall x, Rmin a b <= x <= Rmax a b -> M <= f x) ->
   SF_map (fun x => Finite (real x)) (SF_inf_seq f a b n) = SF_inf_seq f a b n.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm => H ; apply SF_rev_inj ;
    rewrite SF_map_rev SF_inf_bound ; apply Hw => //.
    apply Rlt_le, Rnot_le_lt, Hab.
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ H ; apply SF_lx_ly_inj.
  by rewrite SF_map_lx.
  rewrite SF_map_ly.
  apply eq_from_nth with (x0 := Finite 0).
  by rewrite size_map.
  move => i Hi ; rewrite size_map in Hi ; rewrite (nth_map (Finite 0)) //.
  move: (SF_inf_infty f a b n i) => Hm.
  have: Rbar_le (Finite M) (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i).
    rewrite SF_size_ly -ssrnat.ltnS -SF_size_lx SF_lx_f2 in Hi.
    move: Hm ; rewrite SF_ly_f2 nth_behead (nth_pairmap 0) //.
  have Hx : forall x i , (ssrnat.leq (S (S i)) (size(RInt_part a b n))) -> 
    Rmin (nth 0 (0 :: RInt_part a b n) (S i))
    (nth 0 (RInt_part a b n) (S i)) <= x <=
    Rmax (nth 0 (0 :: RInt_part a b n) (S i))
    (nth 0 (RInt_part a b n) (S i)) -> a <= x <= b.
    move => x {i Hi} i Hi lub ; split.
    (* * a <= x *)
    apply Rle_trans with (2 := proj1 lub) ; apply Rmin_case.
    pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with (nth 0 (RInt_part a b n) i) by intuition ; 
    apply sorted_head.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    simpl ; field ; apply Rgt_not_eq ; intuition.
    pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
    apply sorted_head.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    simpl ; field ; apply Rgt_not_eq ; intuition.
    (* * x <= b *)
    apply Rle_trans with (1 := proj2 lub) ; apply Rmax_lub.
    pattern b at 2 ; replace b with (last 0 (RInt_part a b n)).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with (nth 0 (RInt_part a b n) i) by intuition ; 
    apply sorted_last.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; field ; apply Rgt_not_eq ; intuition.
    pattern b at 2 ; replace b with (last 0 (RInt_part a b n)).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with (nth 0 (RInt_part a b n) i) by intuition ; 
    apply sorted_last.
    apply RInt_part_sort => //.
    apply SSR_leq in Hi ; rewrite size_mkseq in Hi |- * ; intuition.
    rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; field ; apply Rgt_not_eq ; intuition.

  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) ; 
  case => [l | | ] [ub lub] //= _ ;
  apply: lub => _ [x [-> lub]] ;
  apply Rbar_finite_le, H, (Hx x i) => //.

  case: (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i) Hm => //= _ ; case => //.
Qed.

Definition SF_sup_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_sup_seq f a b n) (Finite 0) x
    | right _ => SF_fun (SF_sup_seq f b a n) (Finite 0) x
  end.
Definition SF_inf_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_inf_seq f a b n) (Finite 0) x
    | right _ => SF_fun (SF_inf_seq f b a n) (Finite 0) x
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

Lemma SF_sup_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_sup_fun f a b n x = 
    match (RInt_part_nat a b n x Hx) with
      | inleft H => Sup_fct f (nth 0 (RInt_part a b n) (projT1 H)) 
          (nth 0 (RInt_part a b n) (S (projT1 H)))
      | inright _ => Sup_fct f (nth 0 (RInt_part a b n) (pow2 n - 1)) 
          (nth 0 (RInt_part a b n) (pow2 n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_sup_fun /SF_sup_seq ; case: Rle_dec => // _.
  case: RInt_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl projT1.
(* i < 2^n - 1 *)
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = 2^n - 1 *)
  move: (pow2_pos n) x Hx ; have: (pow2 n = size (RInt_part a b n) - 1)%nat ;
    [ rewrite size_mkseq ; intuition | move => ->].
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  rewrite -minus_n_O in Hi |- * ; case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_n_O in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
Qed.

Lemma SF_inf_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_inf_fun f a b n x = 
    match (RInt_part_nat a b n x Hx) with
      | inleft H => Inf_fct f (nth 0 (RInt_part a b n) (projT1 H)) 
          (nth 0 (RInt_part a b n) (S (projT1 H)))
      | inright _ => Inf_fct f (nth 0 (RInt_part a b n) (pow2 n - 1)) 
          (nth 0 (RInt_part a b n) (pow2 n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_inf_fun /SF_inf_seq ; case: Rle_dec => // _.
  case: RInt_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl projT1.
(* i < 2^n - 1 *)
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = 2^n - 1 *)
  move: (pow2_pos n) x Hx ; have: (pow2 n = size (RInt_part a b n) - 1)%nat ;
    [ rewrite size_mkseq ; intuition | move => ->].
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  rewrite -minus_n_O in Hi |- * ; case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_n_O in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
Qed.

Lemma SF_sup_ge_f (f : R -> R) (a b : R) (n : nat) (x : R) :
  (Rmin a b <= x <= Rmax a b) -> Rbar_le (Finite (f x)) (SF_sup_fun f a b n x).
Proof.
  wlog : a b / (a <= b) => [Hw|].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm SF_sup_fun_bound ; 
    by apply Hw, Rlt_le, Rnot_le_lt.
  rewrite /Rmin /Rmax ; case: (Rle_dec a b) => // _ Hab Hx ;
  rewrite (SF_sup_fun_rw f a b n x Hx) ;
  case: (RInt_part_nat a b n x Hx) => // {Hx} [ [i [Hx Hi]] | Hx ] ; simpl projT1 ;
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l [ub _] /= ;
  apply: ub ; exists x ; split => //.
  have : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx |] ;
  rewrite /Rmin /Rmax ; case: (Rle_dec _ _) ; intuition.
  have : (nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (pow2 n)) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx |] ;
  rewrite /Rmin /Rmax ; case: (Rle_dec _ _) ; intuition.
Qed.

Lemma SF_inf_le_f (f : R -> R) (a b : R) (n : nat) (x : R) :
  (Rmin a b <= x <= Rmax a b) -> Rbar_le (SF_inf_fun f a b n x) (Finite (f x)).
Proof.
  wlog : a b / (a <= b) => [Hw|].
    case: (Rle_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm SF_inf_fun_bound ; 
    by apply Hw, Rlt_le, Rnot_le_lt.
  rewrite /Rmin /Rmax ; case: (Rle_dec a b) => // _ Hab Hx ;
  rewrite (SF_inf_fun_rw f a b n x Hx) ;
  case: (RInt_part_nat a b n x Hx) => // {Hx} [ [i [Hx Hi]] | Hx ] ; simpl projT1 ;
  rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => l [ub _] /= ;
  apply: ub ; exists x ; split => //.
  have : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx |] ;
  rewrite /Rmin /Rmax ; case: (Rle_dec _ _) ; intuition.
  have : (nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (pow2 n)) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx |] ;
  rewrite /Rmin /Rmax ; case: (Rle_dec _ _) ; intuition.
Qed.

Lemma SF_inf_le_sup (f : R -> R) (a b : R) (n : nat) (x : R) :
  (Rmin a b <= x <= Rmax a b) -> Rbar_le (SF_inf_fun f a b n x) (SF_sup_fun f a b n x).
Proof.
  move => Hx ; apply Rbar_le_trans with (2 := SF_sup_ge_f f a b n x Hx), 
  SF_inf_le_f => //.
Qed.

(* Lemma SF_sup_decr (f : R -> R) (a b : R) (n : nat) (x : R) :
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
    [by [] | move => ->].
    rewrite -nth_last size_mkseq /= nth_mkseq //= pow2_INR ; contradict Hxb ;
    apply Rlt_le_trans with (1 := Hxb), Req_le ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
    rewrite ?H0 ; by right.
  case: (RInt_part_nat_0 a b (S n) x Hx) => {Hx} i [Hx Hi].
  have : (sum {j : nat | i = (2*j)%nat} {j : nat | i = S (2*j)}).
    elim: (i) => {i Hx Hi} [|i].
      left ; exists 0%nat ; intuition.
        case ; case => j Hj ; [right ; exists j | left ; exists (S j)] ; intuition.
    case ; case => j Hj ; rewrite Hj in Hx, Hi |- * => {i Hj}.
(* *)
  rewrite ?nth_mkseq in Hx ; [| apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
  rewrite (SF_sup_fun_val f a b (S n) (2*j)) ?nth_mkseq => // ;
    [ | apply SSR_leq ; intuition | apply SSR_leq ; intuition | apply SSR_leq ; intuition 
    | apply SSR_leq ; intuition ].
  have H : (j < pow2 n)%nat.
    move: Hi => /= ; elim: (j) (pow2 n) ; intuition.
  have Hx' : a + INR j * (b - a) / 2 ^ n <= x < a + INR (S j) * (b - a) / 2 ^ n.
    rewrite ?S_INR ?mult_INR -?tech_pow_Rmult in Hx |-* ; split.
    apply Rle_trans with (2 := proj1 Hx), Req_le => /= ; field ; 
    apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
    apply Rlt_le_trans with (1 := proj2 Hx) ;
    rewrite -(Rplus_0_r (a + (INR 2 * INR j + 1) * (b - a) / (2 * 2 ^ n))) ;
    have: (a + (INR j + 1) * (b - a) / 2 ^ n = 
      a + (INR 2 * INR j + 1) * (b - a) / (2 * 2 ^ n) + (b-a)/(2*2^n)) ; 
      [simpl ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
    apply Rplus_le_compat_l, Rdiv_le_pos ; [apply (Rminus_le_0 a b), Hab 
    | apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2].
      
  rewrite (SF_sup_fun_val f a b n j) ?nth_mkseq => // ;
    [ | apply SSR_leq ; intuition | apply SSR_leq ; intuition | apply SSR_leq ; intuition 
    | apply SSR_leq ; intuition ].
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) => l1 [ub1 lub1] ;
  case: (ex_lub_Rbar_ne _ _) => l0 [ub0 lub0] /= ;
  apply: lub1 => {ub1} _ [x' [-> H1]] ; apply: ub0 => {lub0} ; exists x' ; 
  split ; auto.
  move : H1 ; have: ((a + INR (2 * j) * (b - a) / 2 ^ S n) <=
    (a + INR (S (2 * j)) * (b - a) / 2 ^ S n)) ; 
    [apply Rlt_le, Rle_lt_trans with (r2 := x) ; by case: Hx|] ;
    have: ((a + INR j * (b - a) / 2 ^ n) <= (a + INR (S j) * (b - a) / 2 ^ n)) ;
    [apply Rlt_le, Rle_lt_trans with (r2 := x) ; by case: Hx'|] ;
    rewrite /Rmin /Rmax ; case: Rle_dec => // ; case: Rle_dec => {Hx Hx'} // H2 H3 _ _ Hx.
    rewrite ?S_INR ?mult_INR -?tech_pow_Rmult in Hx |-* ; split.
    apply Rle_trans with (2 := proj1 Hx), Req_le => /= ; field ; 
    apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
    apply Rle_trans with (1 := proj2 Hx) ;
    rewrite -(Rplus_0_r (a + (INR 2 * INR j + 1) * (b - a) / (2 * 2 ^ n))) ;
    have: (a + (INR j + 1) * (b - a) / 2 ^ n = 
      a + (INR 2 * INR j + 1) * (b - a) / (2 * 2 ^ n) + (b-a)/(2*2^n)) ; 
      [simpl ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
    apply Rplus_le_compat_l, Rdiv_le_pos ; [apply (Rminus_le_0 a b), Hab 
    | apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2].
(* *)
  rewrite ?nth_mkseq in Hx ; [| apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
  rewrite (SF_sup_fun_val f a b (S n) (S (2*j))) ?nth_mkseq => // ;
    [ | apply SSR_leq ; intuition | apply SSR_leq ; intuition | apply SSR_leq ; intuition 
    | apply SSR_leq ; intuition ].
  have H : (j < pow2 n)%nat.
    move: Hi => /= ; elim: (j) (pow2 n) ; intuition.
  have Hx' : a + INR j * (b - a) / 2 ^ n <= x < a + INR (S j) * (b - a) / 2 ^ n.
    rewrite ?S_INR ?mult_INR -?tech_pow_Rmult in Hx |-* ; split.
    apply Rle_trans with (2 := proj1 Hx).
    rewrite -(Rplus_0_r (a + INR j * (b - a) / 2 ^ n)) ;
    have: (a + (INR 2 * INR j + 1) * (b - a) / (2 * 2 ^ n) =
      a + INR j * (b - a) / 2 ^ n + (b-a)/(2*2^n)) ; 
      [simpl ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
    apply Rplus_le_compat_l, Rdiv_le_pos ; [apply (Rminus_le_0 a b), Hab 
    | apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2].
    apply Rlt_le_trans with (1 := proj2 Hx), Req_le => /= ; field ; 
    apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
      
  rewrite (SF_sup_fun_val f a b n j) ?nth_mkseq => // ;
    [ | apply SSR_leq ; intuition | apply SSR_leq ; intuition | apply SSR_leq ; intuition 
    | apply SSR_leq ; intuition ].
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l1 [ub1 lub1] ;
  case: (ex_lub_Rbar_ne _ _) => l0 [ub0 lub0] /= ;
  apply: lub1 => {ub1} _ [x' [-> H1]] ; apply: ub0 => {lub0} ; exists x' ; 
  split ; auto.
  move : H1 ; have: ((a + INR (S (2 * j)) * (b - a) / 2 ^ S n) <=
    (a + INR (S (S (2 * j))) * (b - a) / 2 ^ S n)) ; 
    [apply Rlt_le, Rle_lt_trans with (r2 := x) ; by case: Hx|] ;
    have: ((a + INR j * (b - a) / 2 ^ n) <= (a + INR (S j) * (b - a) / 2 ^ n)) ;
    [apply Rlt_le, Rle_lt_trans with (r2 := x) ; by case: Hx'|] ;
    rewrite /Rmin /Rmax ; case: Rle_dec => // ; case: Rle_dec => {Hx Hx'} // H2 H3 _ _ Hx.
    rewrite ?S_INR ?mult_INR -?tech_pow_Rmult in Hx |-* ; split.
    apply Rle_trans with (2 := proj1 Hx) ;
    rewrite -(Rplus_0_r (a + INR j * (b - a) / 2 ^ n)) ;
    have: (a + (INR 2 * INR j + 1) * (b - a) / (2 * 2 ^ n)= 
       a + (INR j) * (b - a) / 2 ^ n + (b-a)/(2*2^n)) ; 
      [simpl ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2| move => ->] ;
    apply Rplus_le_compat_l, Rdiv_le_pos ; [apply (Rminus_le_0 a b), Hab 
    | apply Rmult_lt_0_compat ; [| apply pow_lt] ; apply Rlt_R0_R2].
    apply Rle_trans with (1 := proj2 Hx), Req_le => /= ; field ; 
    apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
Qed.

Lemma SF_inf_incr (f : R -> R) (a b : R) (n : nat) (x : R) :
  Rbar_le (SF_inf_fun f a b n x) (SF_inf_fun f a b (S n) x).
Admitted. (** Admitted. *) 

(** * StepFun of SF_sup and SF_inf *)

(** ** SF_sorted *)

Lemma SF_sup_sorted_0 (f : R -> R) (a b : R) (n : nat) : (a <= b) ->
  SF_sorted Rle (SF_sup f a b n).
Proof.
  move => Hab ; rewrite /SF_sorted /SF_sup SF_sup_P_lx.
  have: ((head 0 (RInt_part a b n) :: behead (RInt_part a b n)) = RInt_part a b n) ;
    [by [] | move => -> ].
  by apply RInt_part_sorted_0.
Qed.
Lemma SF_sup_sorted_1 (f : R -> R) (a b : R) (n : nat) : (b <= a) ->
  SF_sorted Rge (SF_sup f a b n).
Proof.
  move => Hab ; rewrite /SF_sorted /SF_sup SF_sup_P_lx.
  have: ((head 0 (RInt_part a b n) :: behead (RInt_part a b n)) = RInt_part a b n) ;
    [by [] | move => -> ].
  by apply RInt_part_sorted_1.
Qed.
Lemma SF_inf_sorted_0 (f : R -> R) (a b : R) (n : nat) : (a <= b) ->
  SF_sorted Rle (SF_inf f a b n).
Proof.
  move => Hab ; rewrite /SF_sorted /SF_inf SF_inf_P_lx.
  have: ((head 0 (RInt_part a b n) :: behead (RInt_part a b n)) = RInt_part a b n) ;
    [by [] | move => -> ].
  by apply RInt_part_sorted_0.
Qed.
Lemma SF_inf_sorted_1 (f : R -> R) (a b : R) (n : nat) : (b <= a) ->
  SF_sorted Rge (SF_inf f a b n).
Proof.
  move => Hab ; rewrite /SF_sorted /SF_inf SF_inf_P_lx.
  have: ((head 0 (RInt_part a b n) :: behead (RInt_part a b n)) = RInt_part a b n) ;
    [by [] | move => -> ].
  by apply RInt_part_sorted_1.
Qed. *)

(** ** SF_sup_real is a StepFun *)

Lemma ad_SF_sup_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b 
      (seq2Rlist (RInt_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b 
      (seq2Rlist (RInt_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part b a n))))).
Proof.
  wlog : a b / (a <= b) => [Hw|Hab].
  case: (Rle_dec a b) => // Hab ; split => // _.
    by apply (Hw a b).
    apply Rnot_le_lt, Rlt_le in Hab ;
    case : (Hw b a Hab) => {Hw} Hw _ ;
    move: (Hw Hab) => {Hw} Hw ; 
    rewrite /adapted_couple in Hw |-* ; rewrite Rmin_comm Rmax_comm ; 
    intuition => x Hx ; rewrite SF_sup_fun_bound ; by apply H4.
  split ; case: (Rle_dec a b)=> // _ _.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => // _.
  have Hs : (SF_sorted Rle (SF_map real (SF_sup_seq f a b n))).
    rewrite /SF_sorted SF_map_lx SF_lx_f2.
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) 
    with (RInt_part a b n) by intuition.
    by apply RInt_part_sort.
  have: a = head 0 (RInt_part a b n) ; 
  [ simpl ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have: b = last 0 (RInt_part a b n) ; 
  [ rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; 
  field ; apply Rgt_not_eq ; intuition | move => {3}->].
  replace (behead
    (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (RInt_part a b n)))
    with (SF_ly (SF_map real (SF_sup_seq f a b n))).
  replace (RInt_part a b n) 
  with (SF_lx (SF_map real (SF_sup_seq f a b n))).
  move: (ad_SF_compat (SF_map real (SF_sup_seq f a b n)) Hs) ;
  rewrite /adapted_couple => Had ; intuition.
  move: (H4 i H3) => {H4 H3} H3 x H4.
  move: (H3 x H4) => {H3 H4} <-.
  by rewrite -(SF_fun_map real).
  by rewrite SF_map_lx SF_lx_f2.
  rewrite SF_map_ly SF_ly_f2.
  by rewrite -behead_map map_pairmap.
Qed.

Definition SF_sup_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => real (SF_sup_fun f a b n x)) ;
  case : (Rle_dec a b) => Hab.
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part a b n)))) ;
  by apply ad_SF_sup_r.
  exists (seq2Rlist ((RInt_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part b a n)))) ;
  by apply ad_SF_sup_r.
Defined.
Lemma SF_sup_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_sup_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_sup_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_sup_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part b a n))))
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_sup_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_sup_r f a b n x = SF_sup_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_sup_fun_bound.
Qed.

(** ** SF_inf_real is a StepFun *)

Lemma ad_SF_inf_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b 
      (seq2Rlist (RInt_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b 
      (seq2Rlist (RInt_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part b a n))))).
Proof.
  wlog : a b / (a <= b) => [Hw|Hab].
  case: (Rle_dec a b) => // Hab ; split => // _.
    by apply (Hw a b).
    apply Rnot_le_lt, Rlt_le in Hab ;
    case : (Hw b a Hab) => {Hw} Hw _ ;
    move: (Hw Hab) => {Hw} Hw ; 
    rewrite /adapted_couple in Hw |-* ; rewrite Rmin_comm Rmax_comm ; 
    intuition => x Hx ; rewrite SF_inf_fun_bound ; by apply H4.
  split ; case: (Rle_dec a b)=> // _ _.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => // _.
  have Hs : (SF_sorted Rle (SF_map real (SF_inf_seq f a b n))).
    rewrite /SF_sorted SF_map_lx SF_lx_f2.
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) 
    with (RInt_part a b n) by intuition.
    by apply RInt_part_sort.
  have: a = head 0 (RInt_part a b n) ; 
  [ simpl ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have: b = last 0 (RInt_part a b n) ; 
  [ rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; 
  field ; apply Rgt_not_eq ; intuition | move => {3}->].
  replace (behead
    (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (RInt_part a b n)))
    with (SF_ly (SF_map real (SF_inf_seq f a b n))).
  replace (RInt_part a b n) 
  with (SF_lx (SF_map real (SF_inf_seq f a b n))).
  move: (ad_SF_compat (SF_map real (SF_inf_seq f a b n)) Hs) ;
  rewrite /adapted_couple => Had ; intuition.
  move: (H4 i H3) => {H4 H3} H3 x H4.
  move: (H3 x H4) => {H3 H4} <-.
  by rewrite -(SF_fun_map real).
  by rewrite SF_map_lx SF_lx_f2.
  rewrite SF_map_ly SF_ly_f2.
  by rewrite -behead_map map_pairmap.
Qed.

Definition SF_inf_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => real (SF_inf_fun f a b n x)) ;
  case : (Rle_dec a b) => Hab.
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part a b n)))) ;
  by apply ad_SF_inf_r.
  exists (seq2Rlist ((RInt_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part b a n)))) ;
  by apply ad_SF_inf_r.
Defined.
Lemma SF_inf_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_inf_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part b a n))))
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_inf_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_inf_r f a b n x = SF_inf_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_inf_fun_bound.
Qed.

(** ** SF_sup_r - SF_inf_r *)

Lemma ad_SF_psi_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => SF_sup_r f a b n x - SF_inf_r f a b n x) a b 
      (seq2Rlist (RInt_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => SF_sup_r f a b n x - SF_inf_r f a b n x) a b 
      (seq2Rlist (RInt_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part b a n))))).
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    split ; case: (Rle_dec a b) => // Hab _.
    by apply Hw.
    apply StepFun_P2 ; apply Rnot_le_lt, Rlt_le in Hab.
    move: (proj1 (Hw _ _ Hab) Hab) ; rewrite /adapted_couple ; intuition => x Hx.
    rewrite -(H4 i H3 x Hx).
    by rewrite SF_sup_r_bound SF_inf_r_bound.
  split ; case: (Rle_dec a b) => // _ _.
  move: (proj1 (ad_SF_sup_r f a b n) Hab) (proj1 (ad_SF_inf_r f a b n) Hab) ;
  rewrite /adapted_couple ; intuition.
  by rewrite ?size_compat size_behead size_pairmap.
  move => x Hx ; simpl.
  rewrite (H8 i H7 x Hx) (H9 i H7 x Hx) !nth_compat !nth_behead !(nth_pairmap 0) //=.
  rewrite size_compat size_mkseq /= in H7 ;
  apply SSR_leq ; rewrite size_map size_iota ; intuition.
  rewrite size_compat size_mkseq /= in H7 ;
  apply SSR_leq ; rewrite size_map size_iota ; intuition.
  rewrite size_compat size_mkseq /= in H7 ;
  apply SSR_leq ; rewrite size_map size_iota ; intuition.
Qed.

Definition SF_psi_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => SF_sup_r f a b n x - SF_inf_r f a b n x) ; 
  case: (Rle_dec a b) => Hab.
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part a b n)))) ;
  by apply ad_SF_psi_r.
  exists (seq2Rlist (RInt_part b a n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part b a n)))) ;
  by apply ad_SF_psi_r.
Defined.
Lemma SF_psi_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_psi_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /SF_psi_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_psi_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_psi_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part b a n))))
  end.
Proof.
  rewrite /SF_psi_r ; case: (Rle_dec a b) => Hab //.
Qed.

Definition RInt_sup f a b n := 
  Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n))) (mkposreal (2^n) (pow_lt 2 n Rlt_R0_R2)).
Definition RInt_inf f a b n := 
  Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n))) (mkposreal (2^n) (pow_lt 2 n Rlt_R0_R2)).

Lemma RInt_sup_bound f a b n :
  RInt_sup f a b n = RInt_sup f b a n.
Proof.
  rewrite /RInt_sup -SF_sup_bound SF_ly_rev ; apply Rbar_div_pos_eq.
  have: (forall i, Rbar_lt m_infty (nth (Finite 0) (SF_ly (SF_sup_seq f b a n)) i)).
    move => i ; case: (le_dec (S (S i)) (size (RInt_part b a n))) => Hi.
    rewrite SF_ly_f2 nth_behead (nth_pairmap 0) ; [| by apply SSR_leq].
    rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; 
    case => [l | | ] [ub lub] //=.
    absurd (Rbar_le (Finite (f (nth 0 (0 :: RInt_part b a n) (S i)))) m_infty).
    by apply Rbar_lt_not_le.
    apply ub ; exists (nth 0 (0 :: RInt_part b a n) (S i)) ; split => // ; 
    apply Rmin_Rmax_l.
    rewrite nth_default => // ; apply SSR_leq ; apply not_le in Hi ; 
    rewrite SF_ly_f2 size_behead size_pairmap ; rewrite size_mkseq /= in Hi |- * ; 
    intuition.
  have H : forall s , (forall i, Rbar_lt m_infty (nth (Finite 0) s i)) ->
    Rbar_lt m_infty (foldr Rbar_plus (Finite 0) s).
    elim => [|h s IH] Hlt // ;
    have : (forall i : nat, Rbar_lt m_infty (nth (Finite 0) s i)) ;
      [move => i ; apply (Hlt (S i)) | ] ;
    move : (Hlt O) ; replace (nth (Finite 0) _ O) with h by auto ; 
    move => {Hlt} Hlt0 Hlt.
    replace (foldr Rbar_plus _ (_ :: s)) with 
      (Rbar_plus h (foldr Rbar_plus (Finite 0) s)) by auto.
    case: h Hlt0 => [h | | ] // _ ;
    case: (foldr Rbar_plus (Finite 0) s) (IH Hlt) => [h0 | | ] // _.
  have: (Rbar_lt m_infty (Finite 0)) ; [by [] | ] ;
  replace (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f b a n))) 
    with (Rbar_plus (Finite 0) (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f b a n)))) ;
    [ | case:(foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f b a n))) => //= ; intuition ].
  elim: (SF_ly (SF_sup_seq f b a n)) {1 3 4}(Finite 0) => [| h s IH] x0 Hx0 Hlt.
  case: x0 Hx0 ; simpl ; intuition.
  rewrite rev_cons foldr_rcons IH.
  replace (foldr Rbar_plus (Finite 0) (h :: s)) with
    (Rbar_plus h (foldr Rbar_plus (Finite 0) s)) by auto.
  case : (foldr Rbar_plus (Finite 0) s) (H s (fun i => Hlt (S i))) 
    => [h0 | | ] // _ ;
  case : (h) (Hlt O) => [h' | | ] // _ ;
  case: x0 Hx0 => [x0 | | ] //= _ ; apply Rbar_finite_eq ; ring.
  case : (h) (Hlt O) => [h' | | ] // _ ;
  case: x0 Hx0 => [x0 | | ] //= _.
  move => i ; apply (Hlt (S i)).
Qed.
Lemma RInt_inf_bound f a b n :
  RInt_inf f a b n = RInt_inf f b a n.
Proof.
  rewrite /RInt_inf -SF_inf_bound SF_ly_rev ; apply Rbar_div_pos_eq.
  have: (forall i, Rbar_lt (nth (Finite 0) (SF_ly (SF_inf_seq f b a n)) i) p_infty).
    move => i ; case: (le_dec (S (S i)) (size (RInt_part b a n))) => Hi.
    rewrite SF_ly_f2 nth_behead (nth_pairmap 0) ; [| by apply SSR_leq].
    rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) ; 
    case => [l | | ] [ub lub] //=.
    absurd (Rbar_le p_infty (Finite (f (nth 0 (0 :: RInt_part b a n) (S i))))).
    by apply Rbar_lt_not_le.
    apply ub ; exists (nth 0 (0 :: RInt_part b a n) (S i)) ; split => // ; 
    apply Rmin_Rmax_l.
    rewrite nth_default => // ; apply SSR_leq ; apply not_le in Hi ; 
    rewrite SF_ly_f2 size_behead size_pairmap ; rewrite size_mkseq /= in Hi |- * ; 
    intuition.
  have H : forall s , (forall i, Rbar_lt (nth (Finite 0) s i) p_infty) ->
    Rbar_lt (foldr Rbar_plus (Finite 0) s) p_infty.
    elim => [|h s IH] Hlt // ;
    have : (forall i : nat, Rbar_lt (nth (Finite 0) s i) p_infty) ;
      [move => i ; apply (Hlt (S i)) | ] ;
    move : (Hlt O) ; replace (nth (Finite 0) _ O) with h by auto ; 
    move => {Hlt} Hlt0 Hlt.
    replace (foldr Rbar_plus _ (_ :: s)) with 
      (Rbar_plus h (foldr Rbar_plus (Finite 0) s)) by auto.
    case: h Hlt0 => [h | | ] // _ ;
    case: (foldr Rbar_plus (Finite 0) s) (IH Hlt) => [h0 | | ] // _.
  have: (Rbar_lt (Finite 0) p_infty) ; [by [] | ] ;
  replace (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f b a n))) 
    with (Rbar_plus (Finite 0) (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f b a n)))) ;
    [ | case:(foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f b a n))) => //= ; intuition ].
  elim: (SF_ly (SF_inf_seq f b a n)) {1 3 4}(Finite 0) => [| h s IH] x0 Hx0 Hlt.
  case: x0 Hx0 ; simpl ; intuition.
  rewrite rev_cons foldr_rcons IH.
  replace (foldr Rbar_plus (Finite 0) (h :: s)) with
    (Rbar_plus h (foldr Rbar_plus (Finite 0) s)) by auto.
  case : (foldr Rbar_plus (Finite 0) s) (H s (fun i => Hlt (S i))) 
    => [h0 | | ] // _ ;
  case : (h) (Hlt O) => [h' | | ] // _ ;
  case: x0 Hx0 => [x0 | | ] //= _ ; apply Rbar_finite_eq ; ring.
  case : (h) (Hlt O) => [h' | | ] // _ ;
  case: x0 Hx0 => [x0 | | ] //= _.
  move => i ; apply (Hlt (S i)).
Qed.

Lemma RInt_sup_infty (f : R -> R) (a b : R) (n : nat) :
  Rbar_lt m_infty (RInt_sup f a b n).
Proof.
  rewrite /RInt_sup.
  suff : Rbar_lt m_infty (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n))).
    by case: (foldr _ _ _).
  elim: (SF_ly (SF_sup_seq f a b n)) (SF_sup_infty f a b n) => [| h s IH] Hlt //.
  move: h Hlt (Hlt O) => /= ; case => [h | | ] Hlt Hlt0 // ;
  move: (foldr _ _ _) (IH (fun i => Hlt (S i))) => /= ; case => //.
Qed.
Lemma RInt_inf_infty (f : R -> R) (a b : R) (n : nat) :
  Rbar_lt (RInt_inf f a b n) p_infty.
Proof.
  rewrite /RInt_inf.
  suff : Rbar_lt (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n))) p_infty.
    by case: (foldr _ _ _).
  elim: (SF_ly (SF_inf_seq f a b n)) (SF_inf_infty f a b n) => [| h s IH] Hlt //.
  move: h Hlt (Hlt O) => /= ; case => [h | | ] Hlt Hlt0 // ;
  move: (foldr _ _ _) (IH (fun i => Hlt (S i))) => /= ; case => //.
Qed.

Lemma RInt_sup_real_0 (f : R -> R) (a b : R) (n : nat) :
  Finite (real (RInt_sup f a b n)) = RInt_sup f a b n
    -> {M : R | forall x, Rmin a b <= x <= Rmax a b -> f x <= M}.
Proof.
  move => Hfin ; apply SF_sup_real_0 with (n := n) ; rewrite /RInt_sup in Hfin.
  have : Finite (real (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n)))) =
    (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n))) => [| {Hfin} Hfin].
    case: (foldr Rbar_plus _ _) Hfin => [x | | ] Hfin //.
  apply SF_lx_ly_inj.
  by rewrite SF_map_lx.
  rewrite SF_map_ly.
  have Hlt : (forall i, Rbar_lt m_infty (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i)).
    move => i ; case: (le_dec (S (S i)) (size (RInt_part a b n))) => Hi.
    rewrite SF_ly_f2 nth_behead (nth_pairmap 0) ; [|by apply SSR_leq].
    rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) ; 
    case => [l | | ] [ub lub] //=.
    absurd (Rbar_le (Finite (f (nth 0 (0 :: RInt_part a b n) (S i)))) m_infty).
    by apply Rbar_lt_not_le.
    apply ub ; exists (nth 0 (0 :: RInt_part a b n) (S i)) ; split => // ; 
    apply Rmin_Rmax_l.
    rewrite nth_default => // ; apply SSR_leq ; apply not_le in Hi ; 
    rewrite SF_ly_f2 size_behead size_pairmap ; rewrite size_mkseq /= in Hi |- * ; 
    intuition.
  elim: (SF_ly (SF_sup_seq f a b n)) Hlt Hfin => {f a b n} [|h s IH] Hlt //= Hfin.
  have : (Rbar_lt m_infty (foldr Rbar_plus (Finite 0) s)) => [| Hlt'].
    elim: s h Hlt {IH Hfin} => [|h0 s IH] // h Hlt.
    move: (Hlt 1%nat) => /= ; case h0 => // ;
    move: (IH h0 (fun i => Hlt (S i))) ; case: (foldr _ _ _) => //.
  case: (h) (Hlt O) Hfin => [x | | ] // _ Hfin ;
  rewrite (IH (fun i => Hlt (S i))) ;
  case: (foldr _ _ _) Hlt' Hfin => [y | | ] //.
Qed.

Lemma RInt_sup_real_1 (f : R -> R) (a b : R) (n : nat) M :
  (forall x, Rmin a b <= x <= Rmax a b -> f x <= M) ->
    Finite (real (RInt_sup f a b n)) = RInt_sup f a b n.
Proof.
  move => Hfin ; apply SF_sup_real_1 with (n := n) in Hfin ; rewrite /RInt_sup.
  suff : Finite (real (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n)))) =
    (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n))) => [{Hfin} Hfin|].
    case: (foldr Rbar_plus _ _) Hfin => [x | | ] Hfin //.
  apply SF_ly_surj in Hfin ; rewrite SF_map_ly in Hfin.
  elim: (SF_ly (SF_sup_seq f a b n)) Hfin => {f a b n} [|h s IH] //= Hfin.
  case: (h) Hfin => [x | | ] // Hfin ;
  rewrite -IH => //.
  pattern s at 2 ; replace s with (behead (Finite x :: s)) by auto.
  by rewrite -Hfin.
Qed.

Lemma RInt_inf_real_0 (f : R -> R) (a b : R) (n : nat) :
  Finite (real (RInt_inf f a b n)) = RInt_inf f a b n
    -> {M : R | forall x, Rmin a b <= x <= Rmax a b -> M <= f x}.
Proof.
  move => Hfin ; apply SF_inf_real_0 with (n := n) ; rewrite /RInt_inf in Hfin.
  have : Finite (real (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n)))) =
    (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n))) => [| {Hfin} Hfin].
    case: (foldr Rbar_plus _ _) Hfin => [x | | ] Hfin //.
  apply SF_lx_ly_inj.
  by rewrite SF_map_lx.
  rewrite SF_map_ly.
  have Hlt : (forall i, Rbar_lt (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i) p_infty).
    move => i ; case: (le_dec (S (S i)) (size (RInt_part a b n))) => Hi.
    rewrite SF_ly_f2 nth_behead (nth_pairmap 0) ; [|by apply SSR_leq].
    rewrite /Inf_fct /Glb_Rbar_ne ; case: (ex_glb_Rbar_ne _ _) ; 
    case => [l | | ] [ub lub] //=.
    absurd (Rbar_le p_infty (Finite (f (nth 0 (0 :: RInt_part a b n) (S i))))).
    by apply Rbar_lt_not_le.
    apply ub ; exists (nth 0 (0 :: RInt_part a b n) (S i)) ; split => // ; 
    apply Rmin_Rmax_l.
    rewrite nth_default => // ; apply SSR_leq ; apply not_le in Hi ; 
    rewrite SF_ly_f2 size_behead size_pairmap ; rewrite size_mkseq /= in Hi |- * ; 
    intuition.
  elim: (SF_ly (SF_inf_seq f a b n)) Hlt Hfin => {f a b n} [|h s IH] Hlt //= Hfin.
  have : (Rbar_lt (foldr Rbar_plus (Finite 0) s) p_infty) => [| Hlt'].
    elim: s h Hlt {IH Hfin} => [|h0 s IH] // h Hlt.
    move: (Hlt 1%nat) => /= ; case h0 => // ;
    move: (IH h0 (fun i => Hlt (S i))) ; case: (foldr _ _ _) => //.
  case: (h) (Hlt O) Hfin => [x | | ] // _ Hfin ;
  rewrite (IH (fun i => Hlt (S i))) ;
  case: (foldr _ _ _) Hlt' Hfin => [y | | ] //.
Qed.

Lemma RInt_inf_real_1 (f : R -> R) (a b : R) (n : nat) M :
  (forall x, Rmin a b <= x <= Rmax a b -> M <= f x) ->
    Finite (real (RInt_inf f a b n)) = RInt_inf f a b n.
Proof.
  move => Hfin ; apply SF_inf_real_1 with (n := n) in Hfin ; rewrite /RInt_inf.
  suff : Finite (real (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n)))) =
    (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n))) => [{Hfin} Hfin|].
    case: (foldr Rbar_plus _ _) Hfin => [x | | ] Hfin //.
  apply SF_ly_surj in Hfin ; rewrite SF_map_ly in Hfin.
  elim: (SF_ly (SF_inf_seq f a b n)) Hfin => {f a b n} [|h s IH] //= Hfin.
  case: (h) Hfin => [x | | ] // Hfin ;
  rewrite -IH => //.
  pattern s at 2 ; replace s with (behead (Finite x :: s)) by auto.
  by rewrite -Hfin.
Qed.

Lemma RInt_sup_decr_0 (f : R -> R) (a b : R) (n : nat) :
  Rbar_le (RInt_sup f a b (S n)) (RInt_sup f a b n).
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    rewrite ?(RInt_sup_bound _ a b).
    apply Hw, Rlt_le, Hab.
  rewrite /RInt_sup.
  suff: Rbar_le
  (Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b (S n))))
     {| pos := 2; cond_pos := Rlt_R0_R2 |})
     (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n))).
     case: (foldr _ _ _) => [r | | ] ; 
     case: (foldr _ _ _) => [r0 | | ] //= H ; try by case: H ; try by left.
     apply Rbar_finite_le.
     replace (r /_) with ((r/2)/2^n).
     apply Rmult_le_compat_r.
     apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
     apply Rbar_finite_le, H.
     field ; apply Rgt_not_eq ; intuition.
   have: size (SF_ly (SF_sup_seq f a b (S n))) = (2 * size (SF_ly (SF_sup_seq f a b n)))%nat.
     rewrite ?SF_sup_ly ?size_behead ?size_pairmap ?size_mkseq //=.
   have: (forall i, Rbar_le 
     (Rbar_div_pos (Rbar_plus (nth (Finite 0) (SF_ly (SF_sup_seq f a b (S n))) (2*i))
       (nth (Finite 0) (SF_ly (SF_sup_seq f a b (S n))) (2*i+1)%nat))
       {| pos := 2; cond_pos := Rlt_R0_R2 |})
     (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i)).
     move => i ; rewrite !SF_sup_ly !nth_behead. 
     case: (le_lt_dec (S i) (pow2 n)) => Hi.
     rewrite !(nth_pairmap 0) ?size_mkseq ; try apply SSR_leq => /= ; intuition.
     replace (nth 0 (0 :: RInt_part a b (S n)) (S (2 * i)))
       with (nth 0 (RInt_part a b (S n)) (2 * i)) by auto ;
     replace (nth 0 (0 :: RInt_part a b (S n)) (S (2 * i+1)))
       with (nth 0 (RInt_part a b (S n)) (2 * i+1)) by auto ;
     replace (nth 0 (0 :: RInt_part a b n) (S i))
       with (nth 0 (RInt_part a b n) i) by auto.
     rewrite /Sup_fct /Lub_Rbar_ne ; 
     case: (ex_lub_Rbar_ne _ _) => l10 lub10 ;
     case: (ex_lub_Rbar_ne _ _) => l01 lub01 ;
     case: (ex_lub_Rbar_ne _ _) => l lub ; simpl projT1.
     replace l with (Rbar_div_pos (Rbar_plus l l) {| pos := 2; cond_pos := Rlt_R0_R2 |}).
     apply Rbar_div_pos_le, Rbar_plus_le_compat.
     apply lub10 => {lub10} _ [x [-> lub10]] ; apply lub => {lub} ; exists x ; split => //.
     move: lub10.
     have: ((nth 0 (RInt_part a b (S n)) (2 * i)) <= (nth 0 (RInt_part a b (S n)) (S (2 * i)))).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b (S n)).
     have: (nth 0 (RInt_part a b n) i) <= (nth 0 (RInt_part a b n) (S i)).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b n).
     rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec => // _ _ _ _.
     rewrite ?nth_mkseq ?S_INR ?(plus_INR _ 1%nat) ?mult_INR /= ; 
     try apply SSR_leq => /= ; intuition.
     apply Rle_trans with (2 := H), Req_le ; field ; apply Rgt_not_eq ; intuition.
     apply Rle_trans with (1 := H0).
     apply Rminus_le_0 ; field_simplify ; try apply Rgt_not_eq ; intuition.
     rewrite -Rdiv_1 ; apply Rdiv_le_pos.
     rewrite Rplus_comm ; by apply (Rminus_le_0 a b).
     apply Rmult_lt_0_compat ; intuition.
     apply lub01 => {lub01} _ [x [-> lub01]] ; apply lub => {lub} ; exists x ; split => //.
     move: lub01.
     have: ((nth 0 (RInt_part a b (S n)) (2 * i+1)) <= (nth 0 (RInt_part a b (S n)) (S (2 * i+1)))).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b (S n)).
     have: (nth 0 (RInt_part a b n) i) <= (nth 0 (RInt_part a b n) (S i)).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b n).
     rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec => // _ _ _ _.
     rewrite ?nth_mkseq ?S_INR ?(plus_INR _ 1%nat) ?mult_INR /= ; 
     try apply SSR_leq => /= ; intuition.
     apply Rle_trans with (2 := H).
     apply Rminus_le_0 ; field_simplify ; try apply Rgt_not_eq ; intuition.
     rewrite -Rdiv_1 ; apply Rdiv_le_pos.
     rewrite Rplus_comm ; by apply (Rminus_le_0 a b).
     apply Rmult_lt_0_compat ; intuition.
     apply Rle_trans with (1 := H0), Req_le ; field ; apply Rgt_not_eq ; intuition.
     case: (l) => //= r ; apply Rbar_finite_eq ; field.
   rewrite ?nth_default ?size_pairmap ?size_mkseq /= ; try apply SSR_leq ; intuition.
   apply Rbar_finite_le, Req_le ; field.
   move: (SF_sup_infty f a b n) (SF_sup_infty f a b (S n)).
   elim: (SF_ly (SF_sup_seq f a b n)) (SF_ly (SF_sup_seq f a b (S n))) 
     => [|h s IH] //.
     case => // H H0 H1 H2 /=.
     apply Rbar_finite_le, Req_le ; field.
   case => // h' ; case => [|h'0 s'] Hs Hs' Hle Hsize.
     simpl in Hsize ; apply eq_add_S in Hsize ; rewrite -plus_n_Sm in Hsize => //.
   simpl.
   replace (Rbar_div_pos
     (Rbar_plus h' (Rbar_plus h'0 (foldr Rbar_plus (Finite 0) s')))
     {| pos := 2; cond_pos := Rlt_R0_R2 |}) 
     with (Rbar_plus (Rbar_div_pos (Rbar_plus h' h'0) (mkposreal _ Rlt_R0_R2)) 
       (Rbar_div_pos (foldr Rbar_plus (Finite 0) s') (mkposreal _ Rlt_R0_R2))).
   apply Rbar_plus_le_compat.
   apply (Hle O).
   apply (IH s' (fun i => Hs (S i)) (fun i => Hs' (S (S i)))) => {IH Hs Hs'}.
     move => i ; move: (Hle (S i)) => {Hle} /= ; rewrite -?plus_n_Sm //=.
   simpl in Hsize ; intuition.
   have: Rbar_lt m_infty (foldr Rbar_plus (Finite 0) s').
     elim: (s') (h') (h'0) Hs' => {s' h' h'0 Hle Hsize IH} [| h'1 s' IH] h' h'0 Hs' //.
     move: (Hs' 2%nat) (IH h'0 h'1 (fun i => (Hs' (S i)))) => {Hs'} /= ;
     case: h'1 ; case: (foldr _ _ _) => //=.
   move: (Hs' O) (Hs' 1%nat).
   case: h' {Hs' Hle Hsize} ; case: h'0 ; case: (foldr _ _ _) => //=.
   intros ; apply Rbar_finite_eq ; field.
Qed.
Lemma RInt_sup_decr (f : R -> R) (a b : R) (n m : nat) : (n <= m)%nat ->
  Rbar_le (RInt_sup f a b m) (RInt_sup f a b n).
Proof.
  elim: m n => [| m IH] n Hnm.
  apply le_n_0_eq in Hnm ; rewrite -Hnm ; by right.
  apply le_lt_eq_dec in Hnm ; case: Hnm => Hnm.
  apply Rbar_le_trans with (1 := RInt_sup_decr_0 f a b m), IH ; intuition.
  rewrite Hnm ; by right.
Qed.
Lemma RInt_inf_incr_0 (f : R -> R) (a b : R) (n : nat) :
  Rbar_le (RInt_inf f a b n) (RInt_inf f a b (S n)).
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    rewrite ?(RInt_inf_bound _ a b).
    apply Hw, Rlt_le, Hab.
  rewrite /RInt_inf.
  suff: Rbar_le (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n)))
    (Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b (S n))))
    {| pos := 2; cond_pos := Rlt_R0_R2 |}).
     case: (foldr _ _ _) => [r | | ] ; 
     case: (foldr _ _ _) => [r0 | | ] //= H ; try by case: H ; try by left.
     apply Rbar_finite_le.
     replace (r0 /_) with ((r0/2)/2^n).
     apply Rmult_le_compat_r.
     apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
     apply Rbar_finite_le, H.
     field ; apply Rgt_not_eq ; intuition.
   have: size (SF_ly (SF_inf_seq f a b (S n))) = (2 * size (SF_ly (SF_inf_seq f a b n)))%nat.
     rewrite ?SF_inf_ly ?size_behead ?size_pairmap ?size_mkseq //=.
   have: (forall i, Rbar_le (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i)
     (Rbar_div_pos (Rbar_plus (nth (Finite 0) (SF_ly (SF_inf_seq f a b (S n))) (2*i))
       (nth (Finite 0) (SF_ly (SF_inf_seq f a b (S n))) (2*i+1)%nat))
       {| pos := 2; cond_pos := Rlt_R0_R2 |})).
     move => i ; rewrite !SF_inf_ly !nth_behead. 
     case: (le_lt_dec (S i) (pow2 n)) => Hi.
     rewrite !(nth_pairmap 0) ?size_mkseq ; try apply SSR_leq => /= ; intuition.
     replace (nth 0 (0 :: RInt_part a b (S n)) (S (2 * i)))
       with (nth 0 (RInt_part a b (S n)) (2 * i)) by auto ;
     replace (nth 0 (0 :: RInt_part a b (S n)) (S (2 * i+1)))
       with (nth 0 (RInt_part a b (S n)) (2 * i+1)) by auto ;
     replace (nth 0 (0 :: RInt_part a b n) (S i))
       with (nth 0 (RInt_part a b n) i) by auto.
     rewrite /Inf_fct /Glb_Rbar_ne ; 
     case: (ex_glb_Rbar_ne _ _) => l lub ;
     case: (ex_glb_Rbar_ne _ _) => l10 lub10 ;
     case: (ex_glb_Rbar_ne _ _) => l01 lub01 ; simpl projT1.
     replace l with (Rbar_div_pos (Rbar_plus l l) {| pos := 2; cond_pos := Rlt_R0_R2 |}).
     apply Rbar_div_pos_le, Rbar_plus_le_compat.
     apply lub10 => {lub10} _ [x [-> lub10]] ; apply lub => {lub} ; exists x ; split => //.
     move: lub10.
     have: ((nth 0 (RInt_part a b (S n)) (2 * i)) <= (nth 0 (RInt_part a b (S n)) (S (2 * i)))).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b (S n)).
     have: (nth 0 (RInt_part a b n) i) <= (nth 0 (RInt_part a b n) (S i)).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b n).
     rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec => // _ _ _ _.
     rewrite ?nth_mkseq ?S_INR ?(plus_INR _ 1%nat) ?mult_INR /= ; 
     try apply SSR_leq => /= ; intuition.
     apply Rle_trans with (2 := H), Req_le ; field ; apply Rgt_not_eq ; intuition.
     apply Rle_trans with (1 := H0).
     apply Rminus_le_0 ; field_simplify ; try apply Rgt_not_eq ; intuition.
     rewrite -Rdiv_1 ; apply Rdiv_le_pos.
     rewrite Rplus_comm ; by apply (Rminus_le_0 a b).
     apply Rmult_lt_0_compat ; intuition.
     apply lub01 => {lub01} _ [x [-> lub01]] ; apply lub => {lub} ; exists x ; split => //.
     move: lub01.
     have: ((nth 0 (RInt_part a b (S n)) (2 * i+1)) <= (nth 0 (RInt_part a b (S n)) (S (2 * i+1)))).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b (S n)).
     have: (nth 0 (RInt_part a b n) i) <= (nth 0 (RInt_part a b n) (S i)).
       apply (sorted_nth Rle) ; rewrite ?size_mkseq ; simpl Peano.pred ; intuition ; 
       by apply (RInt_part_sort a b n).
     rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec => // _ _ _ _.
     rewrite ?nth_mkseq ?S_INR ?(plus_INR _ 1%nat) ?mult_INR /= ; 
     try apply SSR_leq => /= ; intuition.
     apply Rle_trans with (2 := H).
     apply Rminus_le_0 ; field_simplify ; try apply Rgt_not_eq ; intuition.
     rewrite -Rdiv_1 ; apply Rdiv_le_pos.
     rewrite Rplus_comm ; by apply (Rminus_le_0 a b).
     apply Rmult_lt_0_compat ; intuition.
     apply Rle_trans with (1 := H0), Req_le ; field ; apply Rgt_not_eq ; intuition.
     case: (l) => //= r ; apply Rbar_finite_eq ; field.
   rewrite ?nth_default ?size_pairmap ?size_mkseq /= ; try apply SSR_leq ; intuition.
   apply Rbar_finite_le, Req_le ; field.
   move: (SF_inf_infty f a b n) (SF_inf_infty f a b (S n)).
   elim: (SF_ly (SF_inf_seq f a b n)) (SF_ly (SF_inf_seq f a b (S n))) 
     => [|h s IH] //.
     case => // H H0 H1 H2 /=.
     apply Rbar_finite_le, Req_le ; field.
   case => // h' ; case => [|h'0 s'] Hs Hs' Hle Hsize.
     simpl in Hsize ; apply eq_add_S in Hsize ; rewrite -plus_n_Sm in Hsize => //.
   simpl.
   replace (Rbar_div_pos
     (Rbar_plus h' (Rbar_plus h'0 (foldr Rbar_plus (Finite 0) s')))
     {| pos := 2; cond_pos := Rlt_R0_R2 |}) 
     with (Rbar_plus (Rbar_div_pos (Rbar_plus h' h'0) (mkposreal _ Rlt_R0_R2)) 
       (Rbar_div_pos (foldr Rbar_plus (Finite 0) s') (mkposreal _ Rlt_R0_R2))).
   apply Rbar_plus_le_compat.
   apply (Hle O).
   apply (IH s' (fun i => Hs (S i)) (fun i => Hs' (S (S i)))) => {IH Hs Hs'}.
     move => i ; move: (Hle (S i)) => {Hle} /= ; rewrite -?plus_n_Sm //=.
   simpl in Hsize ; intuition.
   have: Rbar_lt (foldr Rbar_plus (Finite 0) s') p_infty.
     elim: (s') (h') (h'0) Hs' => {s' h' h'0 Hle Hsize IH} [| h'1 s' IH] h' h'0 Hs' //.
     move: (Hs' 2%nat) (IH h'0 h'1 (fun i => (Hs' (S i)))) => {Hs'} /= ;
     case: h'1 ; case: (foldr _ _ _) => //=.
   move: (Hs' O) (Hs' 1%nat).
   case: h' {Hs' Hle Hsize} ; case: h'0 ; case: (foldr _ _ _) => //=.
   intros ; apply Rbar_finite_eq ; field.
Qed.
Lemma RInt_inf_incr (f : R -> R) (a b : R) (n m : nat) : (n <= m)%nat ->
  Rbar_le (RInt_inf f a b n) (RInt_inf f a b m).
Proof.
  elim: m n => [| m IH] n Hnm.
  apply le_n_0_eq in Hnm ; rewrite -Hnm ; by right.
  apply le_lt_eq_dec in Hnm ; case: Hnm => Hnm.
  apply Rbar_le_trans with (2 := RInt_inf_incr_0 f a b m), IH ; intuition.
  rewrite Hnm ; by right.
Qed.

Lemma RInt_inf_le_sup (f : R -> R) (a b : R) (n : nat) :
  Rbar_le (RInt_inf f a b n) (RInt_sup f a b n).
Proof.
  wlog: a b / (a <= b) => [Hw|Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    move: (Hw _ _ (Rlt_le _ _ Hab)) => {Hw Hab}.
    by rewrite RInt_inf_bound RInt_sup_bound.

  rewrite /RInt_inf /RInt_sup.
  apply Rbar_div_pos_le.
  have: forall i, Rbar_le (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i)
    (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i).
    move => i ; case: (le_lt_dec (S (S i)) (size (RInt_part a b n))) => Hi.
    rewrite SF_inf_ly SF_sup_ly ?nth_behead ?(nth_pairmap 0) ; try by apply SSR_leq.
    replace (nth 0 (0 :: RInt_part a b n) (S i)) 
      with (nth 0 (RInt_part a b n) i) by auto.
    apply Rbar_le_trans with (Finite (f (nth 0 (RInt_part a b n) i))).
    rewrite /Inf_fct /Glb_Rbar_ne ; case: ex_glb_Rbar_ne => li glb /= ;
    apply glb ; exists (nth 0 (RInt_part a b n) i) ; split => // ;
    apply Rmin_Rmax_l.
    rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => ls lub /= ;
    apply lub ; exists (nth 0 (RInt_part a b n) i) ; split => // ;
    apply Rmin_Rmax_l.
    rewrite ?nth_default ; try apply SSR_leq ; 
    rewrite ?SF_sup_ly ?SF_inf_ly ?size_behead ?size_pairmap ;
    rewrite ?size_mkseq /= in Hi |- * ; intuition ; by right.
  have: size (SF_ly (SF_inf_seq f a b n)) = size (SF_ly (SF_sup_seq f a b n)).
    rewrite SF_inf_ly SF_sup_ly ?size_behead ?size_pairmap //.
  elim: (SF_ly (SF_inf_seq f a b n)) (SF_ly (SF_sup_seq f a b n)) => [|h s IH] ;
    case => [ | h0 s0] Hsize Hle //=.
  by right.
  apply Rbar_plus_le_compat.
  by apply (Hle O).
  by apply (IH s0 (eq_add_S _ _ Hsize) (fun i => Hle (S i))).
Qed.

Lemma RInt_sup_compat f a b n M :
  (forall t, Rmin a b <= t <= Rmax a b -> f t <= M) ->
  RiemannInt_SF (SF_sup_r f a b n) = (b-a) * real (RInt_sup f a b n).
Proof.
  wlog : a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab .
    by apply Hw.
    rewrite Rmin_comm Rmax_comm => H ; 
    rewrite RInt_sup_bound -Ropp_minus_distr' Ropp_mult_distr_l_reverse 
    -(Hw _ _ (Rlt_le _ _ Hab)) => //.
    move: (Rlt_le _ _ Hab) (Rlt_not_le _ _ Hab).
    rewrite /RiemannInt_SF /subdivision /subdivision_val /SF_sup_r ;
    case: Rle_dec ; case: Rle_dec => //.

  rewrite /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val /RInt_sup SF_sup_ly /Rmin /Rmax ; 
  case: Rle_dec => // _ H.
  have : (forall i, (S i < size (RInt_part a b n))%nat ->
    nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a) / 2^n).
    move => i ; rewrite size_mkseq => Hi ; rewrite ?nth_mkseq ?S_INR ; 
    try apply SSR_leq ; intuition ; field ; apply Rgt_not_eq ; intuition.
  have : (forall i, (i < size (RInt_part a b n))%nat -> 
    a <= nth 0 (RInt_part a b n) i <= b).
    move => i Hi ; split.
    apply Rle_trans with (2 :=sorted_head (RInt_part a b n) i (RInt_part_sort a b n Hab) Hi 0).
    apply Req_le => /= ; field ; apply Rgt_not_eq ; intuition.
    apply Rle_trans with (1 :=sorted_last (RInt_part a b n) i (RInt_part_sort a b n Hab) Hi 0).
    apply Req_le ; rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; 
    field ; apply Rgt_not_eq ; intuition.
  have : (1 < size (RInt_part a b n))%nat.
    rewrite size_mkseq /= ; apply lt_n_S, pow2_pos.
  case: (RInt_part a b n) => [/= Hs | x0].
    by apply lt_n_O in Hs.
  case => [/= Hs | x1 sx _ /=].
    by apply lt_irrefl in Hs.
  elim: sx x0 x1 => [ | x2 sx IH] /= x0 x1 H0 Hnth.
    move: (Hnth O (lt_n_S _ _ (lt_O_Sn _))) => /= -> ;
    rewrite -(Sup_fct_maj f x0 x1 M) /=.
    field ; apply Rgt_not_eq ; intuition.
    move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 O (lt_O_Sn _)) => //=.
    case: (H0 _ (lt_n_Sn _)) => //=.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 O (lt_O_Sn _)) => //=.
    case: (H0 _ (lt_n_Sn _)) => //=.
  rewrite (IH x1 x2) => {IH}.
  have: (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) x2 sx) =
    Finite (real (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) x2 sx)))).
    elim: sx x0 x1 x2 H0 {Hnth} => [| x3 s IH] x0 x1 x2 H0 //=.
    rewrite -(Sup_fct_maj f x2 x3 M).
    rewrite (IH x1 x2 x3) //=.
    move => i Hi ; apply (H0 (S i)) ; intuition.
    move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 2%nat) => //= ; intuition.
    case: (H0 3%nat) => //= ; intuition.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 2%nat) => //= ; intuition.
    case: (H0 3%nat) => //= ; intuition.
  move => ->.
  rewrite -(Sup_fct_maj f x0 x1 M).
  rewrite -(Sup_fct_maj f x1 x2 M) /=.
  rewrite (Hnth O) ; intuition ; field.
  apply Rgt_not_eq ; intuition.
  move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 1%nat) => //= ; intuition.
    case: (H0 2%nat) => //= ; intuition.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 1%nat) => //= ; intuition.
    case: (H0 2%nat) => //= ; intuition.
  move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 0%nat) => //= ; intuition.
    case: (H0 1%nat) => //= ; intuition.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 0%nat) => //= ; intuition.
    case: (H0 1%nat) => //= ; intuition.
  move => i Hi ; apply (H0 (S i)) ; intuition.
  move => i Hi ; apply (Hnth (S i)) ; intuition.
Qed.

Lemma RInt_inf_compat f a b n M :
  (forall t, Rmin a b <= t <= Rmax a b -> M <= f t) ->
  RiemannInt_SF (SF_inf_r f a b n) = (b-a) * real (RInt_inf f a b n).
Proof.
  wlog : a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab .
    by apply Hw.
    rewrite Rmin_comm Rmax_comm => H ; 
    rewrite RInt_inf_bound -Ropp_minus_distr' Ropp_mult_distr_l_reverse 
    -(Hw _ _ (Rlt_le _ _ Hab)) => //.
    move: (Rlt_le _ _ Hab) (Rlt_not_le _ _ Hab).
    rewrite /RiemannInt_SF /subdivision /subdivision_val /SF_inf_r ;
    case: Rle_dec ; case: Rle_dec => //.

  rewrite /RiemannInt_SF SF_inf_subdiv SF_inf_subdiv_val /RInt_inf SF_inf_ly /Rmin /Rmax ; 
  case: Rle_dec => // _ H.
  have : (forall i, (S i < size (RInt_part a b n))%nat ->
    nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a) / 2^n).
    move => i ; rewrite size_mkseq => Hi ; rewrite ?nth_mkseq ?S_INR ; 
    try apply SSR_leq ; intuition ; field ; apply Rgt_not_eq ; intuition.
  have : (forall i, (i < size (RInt_part a b n))%nat -> 
    a <= nth 0 (RInt_part a b n) i <= b).
    move => i Hi ; split.
    apply Rle_trans with (2 :=sorted_head (RInt_part a b n) i (RInt_part_sort a b n Hab) Hi 0).
    apply Req_le => /= ; field ; apply Rgt_not_eq ; intuition.
    apply Rle_trans with (1 :=sorted_last (RInt_part a b n) i (RInt_part_sort a b n Hab) Hi 0).
    apply Req_le ; rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ; 
    field ; apply Rgt_not_eq ; intuition.
  have : (1 < size (RInt_part a b n))%nat.
    rewrite size_mkseq /= ; apply lt_n_S, pow2_pos.
  case: (RInt_part a b n) => [/= Hs | x0].
    by apply lt_n_O in Hs.
  case => [/= Hs | x1 sx _ /=].
    by apply lt_irrefl in Hs.
  elim: sx x0 x1 => [ | x2 sx IH] /= x0 x1 H0 Hnth.
    move: (Hnth O (lt_n_S _ _ (lt_O_Sn _))) => /= -> ;
    rewrite -(Inf_fct_min f x0 x1 M) /=.
    field ; apply Rgt_not_eq ; intuition.
    move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 O (lt_O_Sn _)) => //=.
    case: (H0 _ (lt_n_Sn _)) => //=.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 O (lt_O_Sn _)) => //=.
    case: (H0 _ (lt_n_Sn _)) => //=.
  rewrite (IH x1 x2) => {IH}.
  have: (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) x2 sx) =
    Finite (real (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) x2 sx)))).
    elim: sx x0 x1 x2 H0 {Hnth} => [| x3 s IH] x0 x1 x2 H0 //=.
    rewrite -(Inf_fct_min f x2 x3 M).
    rewrite (IH x1 x2 x3) //=.
    move => i Hi ; apply (H0 (S i)) ; intuition.
    move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 2%nat) => //= ; intuition.
    case: (H0 3%nat) => //= ; intuition.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 2%nat) => //= ; intuition.
    case: (H0 3%nat) => //= ; intuition.
  move => ->.
  rewrite -(Inf_fct_min f x0 x1 M).
  rewrite -(Inf_fct_min f x1 x2 M) /=.
  rewrite (Hnth O) ; intuition ; field.
  apply Rgt_not_eq ; intuition.
  move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 1%nat) => //= ; intuition.
    case: (H0 2%nat) => //= ; intuition.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 1%nat) => //= ; intuition.
    case: (H0 2%nat) => //= ; intuition.
  move => x Hx ; apply: H ; split.
    apply Rle_trans with (2 := proj1 Hx), Rmin_case_strong => _ .
    case: (H0 0%nat) => //= ; intuition.
    case: (H0 1%nat) => //= ; intuition.
    apply Rle_trans with (1 := proj2 Hx), Rmax_case_strong => _ .
    case: (H0 0%nat) => //= ; intuition.
    case: (H0 1%nat) => //= ; intuition.
  move => i Hi ; apply (H0 (S i)) ; intuition.
  move => i Hi ; apply (Hnth (S i)) ; intuition.
Qed.


(** * A new Riemann_integrable in Prop *)

Definition ex_RInt (f : R -> R) (a b : R) :=
  Rbar_inf_seq (RInt_sup f a b) = Rbar_sup_seq (RInt_inf f a b)
  /\ (Finite (real (Rbar_inf_seq (RInt_sup f a b))) = Rbar_inf_seq (RInt_sup f a b)).

Lemma ex_RInt_bound (f : R -> R) (a b : R) :
  ex_RInt f a b -> ex_RInt f b a.
Proof.
  rewrite /ex_RInt ; case => H H0 ;
  rewrite (Rbar_inf_seq_rw _ _ (RInt_sup_bound _ _ _)) ;
  rewrite (Rbar_sup_seq_rw _ _ (RInt_inf_bound _ _ _)) ; by split.
Qed.

Lemma ex_RInt_sup (f : R -> R) (a b : R) :
  ex_RInt f a b -> forall n, 
    Finite (real (RInt_sup f a b n)) = RInt_sup f a b n.
Proof.
  case.
  rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq ; case => // ls Hls /= _ _.
  case: (Hls (mkposreal _ Rlt_0_1)) => ub [N lub].
  have H: Finite (real (RInt_sup f a b N)) = RInt_sup f a b N.
  move: (ub N) lub ; case: (RInt_sup f a b N) => //.
  apply RInt_sup_real_0 in H ; case: H => M H.
  move => n ; apply RInt_sup_real_1 with M => //.
Qed.
Lemma ex_RInt_inf (f : R -> R) (a b : R) :
  ex_RInt f a b -> forall n, 
    Finite (real (RInt_inf f a b n)) = RInt_inf f a b n.
Proof.
  case.
  rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq ; case => // ls _ /= ;
  rewrite /Rbar_sup_seq ; case: Rbar_ex_sup_seq ; case => // li Hli /= _ _.
  case: (Hli (mkposreal _ Rlt_0_1)) => ub [N lub].
  have H: Finite (real (RInt_inf f a b N)) = RInt_inf f a b N.
  move: (ub N) lub ; case: (RInt_inf f a b N) => //.
  apply RInt_inf_real_0 in H ; case: H => M H.
  move => n ; apply RInt_inf_real_1 with M => //.
Qed.

Lemma ex_RInt_nth_sup (f : R -> R) (a b : R) :
  ex_RInt f a b -> forall n i, 
    Finite (real (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i)) = 
      nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i.
Proof.
  move => Hfin n ; move: (ex_RInt_sup _ _ _ Hfin n) => {Hfin} Hfin.
  rewrite /RInt_sup in Hfin.
  have: Finite (real (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n)))) =
    (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup_seq f a b n))) ; [| move => {Hfin}].
    move: Hfin ; case: (foldr _ _ _) => //.
  elim: (SF_ly (SF_sup_seq f a b n)) (SF_sup_infty f a b n) => [| h s IH] H /= Hfin i.
  by case: i => [| i] //=.
  have: (Rbar_lt m_infty (foldr Rbar_plus (Finite 0) s)).
    elim: s h H {IH Hfin} => [|h0 s IH] h H //.
    move: (H 1%nat) (IH h0 (fun i => H (S i))) => /= ;
    case: h0 {H} ; case: (foldr _ _) => //.
  move: Hfin (H O) ; case: i => [| i] /=.
  case: h {H} ; case: (foldr _ _) => //.
  move => Hfin H0 Hi ; apply IH.
  move => i0 ; apply (H (S i0)).
  move: Hfin H0 Hi ; case: h {H} ; case: (foldr _ _) => //.
Qed.
Lemma ex_RInt_nth_inf (f : R -> R) (a b : R) :
  ex_RInt f a b -> forall n i, 
    Finite (real (nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i)) = 
      nth (Finite 0) (SF_ly (SF_inf_seq f a b n)) i.
Proof.
  move => Hfin n ; move: (ex_RInt_inf _ _ _ Hfin n) => {Hfin} Hfin.
  rewrite /RInt_inf in Hfin.
  have: Finite (real (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n)))) =
    (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf_seq f a b n))) ; [| move => {Hfin}].
    move: Hfin ; case: (foldr _ _ _) => //.
  elim: (SF_ly (SF_inf_seq f a b n)) (SF_inf_infty f a b n) => [| h s IH] H /= Hfin i.
  by case: i => [| i] //=.
  have: (Rbar_lt (foldr Rbar_plus (Finite 0) s) p_infty).
    elim: s h H {IH Hfin} => [|h0 s IH] h H //.
    move: (H 1%nat) (IH h0 (fun i => H (S i))) => /= ;
    case: h0 {H} ; case: (foldr _ _) => //.
  move: Hfin (H O) ; case: i => [| i] /=.
  case: h {H} ; case: (foldr _ _) => //.
  move => Hfin H0 Hi ; apply IH.
  move => i0 ; apply (H (S i0)).
  move: Hfin H0 Hi ; case: h {H} ; case: (foldr _ _) => //.
Qed.

Lemma ex_RInt_psi_sup_inf (f : R -> R) (a b : R) : ex_RInt f a b ->
  forall n, RiemannInt_SF (SF_psi_r f a b n) 
    = (b-a) * (real (RInt_sup f a b n) - real (RInt_inf f a b n)).
Proof.
  wlog: a b  /(a <= b) => [Hw | Hab] Hex n.
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    move: (Hw b a (Rlt_le _ _ Hab) (ex_RInt_bound f a b Hex) n).
    rewrite /RiemannInt_SF ?SF_psi_subdiv ?SF_psi_subdiv_val
    RInt_sup_bound RInt_inf_bound;
    move: (Rlt_le _ _ Hab) (Rlt_not_le _ _ Hab) ; 
    case: Rle_dec ; case: Rle_dec => // _ _ _ _ -> ; ring.
    
  rewrite /RiemannInt_SF ?SF_psi_subdiv ?SF_psi_subdiv_val ;
  case: Rle_dec => // _.
  rewrite /RInt_sup /RInt_inf.
  move: (ex_RInt_nth_sup f a b Hex n) (ex_RInt_nth_inf f a b Hex n).
  rewrite /SF_sup_seq /SF_inf_seq.
  have: (forall i, ((S i) < size (RInt_part a b n))%nat -> 
    nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/2^n).
    move => i Hi ; rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ;
    try apply SSR_leq ; intuition ; field ; apply Rgt_not_eq ; intuition.
  case: (RInt_part a b n) => [| h s] /=.
  move => _ _ _ ; ring.
  elim: s h => [| h0 s IH] h Hrw Hs Hi.
  simpl ; ring.
  rewrite ?SF_ly_f2 /= (IH h0) => {IH}.
  rewrite ?SF_ly_f2 (Hrw O) => {Hrw}.
  move: (Hs O) (Hi O) => /= ; case: (Sup_fct f h h0) => // sup _ ;
  case: (Inf_fct f h h0) => // inf _.
  rewrite ?SF_ly_f2 /= in Hi, Hs.
  have: (Finite (real (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s))))
    = (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s)).
    move: (fun i => Hs (S i)) => /=.
    elim: s h0 {Hi Hs} => {h} [|h0 s IH] h //= Hfin.
    move: (Hfin O) (IH h0 (fun i => Hfin (S i))) => /=.
    case: (Sup_fct f h h0) => // s0 _ ;
    case: (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s)) => // s1 _.
  have: (Finite (real (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s))))
    = (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s)).
    move: (fun i => Hi (S i)) => /=.
    elim: s h0 {Hi Hs} => {h} [|h0 s IH] h //= Hfin.
    move: (Hfin O) (IH h0 (fun i => Hfin (S i))) => /=.
    case: (Inf_fct f h h0) => // s0 _ ;
    case: (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s)) => // s1 _.
  case: (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s)) => // inf1 _.
  case: (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s)) => // sup1 _.
  simpl ; field ; apply Rgt_not_eq ; intuition.
  simpl ; apply lt_n_S, lt_O_Sn.
  move => i0 Hi0 ; apply (Hrw (S i0)) ; simpl ; intuition.
  move => i ; apply (Hs (S i)).
  move => i ; apply (Hi (S i)).
Qed.

(** * Gourdon's proof *)

Definition pointed_subdiv (ptd : @SF_seq R) :=
  forall i : nat, (i < SF_size ptd)%nat -> 
    nth 0 (SF_lx ptd) i <= nth 0 (SF_ly ptd) i <= nth 0 (SF_lx ptd) (S i).

Lemma ptd_cons h s : pointed_subdiv (SF_cons h s) -> pointed_subdiv s.
Proof.
  move => H i Hi ; apply (H (S i)) ; rewrite SF_size_cons ; intuition.
Qed.
Lemma ptd_sort ptd : 
  pointed_subdiv ptd -> SF_sorted Rle ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ;
  [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] => 
  Hptd ; try split => //=.
  apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
  apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
  apply IH, (ptd_cons (x0,y0)) => //.
Qed.
Lemma ptd_sort' ptd : 
  pointed_subdiv ptd -> sorted Rle (SF_ly ptd).
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ;
  [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] => 
  Hptd ; try split.
  apply Rle_trans with x1 ; [apply (Hptd O) | apply (Hptd 1%nat)] ; 
  rewrite ?SF_size_cons ; repeat apply lt_n_S ; apply lt_O_Sn.
  apply IH, (ptd_cons (x0,y0)) => //.
Qed.

Definition signe (x : R) :=
  match Rle_dec 0 x with
    | left H => match Rle_lt_or_eq_dec _ _ H with
        | left _ => 1
        | right _ => 0
      end
    | right _ => -1
  end.
Lemma Ropp_signe (x : R) : signe (-x) = - signe x.
Proof.
  rewrite /signe ; 
  case: Rle_dec => H ; case: Rle_dec => H0.
  have: ~ (0 < - x).
    apply Rle_not_lt, Ropp_le_cancel ; intuition.
  have: ~ (0 < x).
    apply Rle_not_lt, Ropp_le_cancel ; rewrite Ropp_0 ; intuition.
  case: Rle_lt_or_eq_dec => // ; case: Rle_lt_or_eq_dec => // ; intuition.
  have: ~ (0 = - x).
    contradict H0 ; apply Ropp_le_cancel ; rewrite -H0 ; intuition.
  case: Rle_lt_or_eq_dec => // ; intuition.
  have: ~ (0 = x).
    contradict H ; rewrite -H ; intuition.
  case: Rle_lt_or_eq_dec => // ; intuition.
  contradict H0 ; apply Ropp_le_cancel, Rlt_le, Rnot_le_lt ; intuition.
Qed.

Definition seq_step (s : seq R) := 
  foldr Rmax 0 (pairmap (fun x y => Rabs (Rminus y x)) (head 0 s) (behead s)).

Definition Riemann_sum (f : R -> R) (ptd : SF_seq) :=
  RInt_seq (SF_map f ptd) Rplus Rmult 0.

Lemma Riemann_sum_cons (f : R -> R) h0 ptd :
  Riemann_sum f (SF_cons h0 ptd) =
    f (snd h0) * (SF_h ptd - fst h0) + Riemann_sum f ptd.
Proof.
  rewrite /Riemann_sum /RInt_seq /=.
  case: h0 => x0 y0 ;
  apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd ] //=.
Qed. 

Lemma pointed_pty2 f ptd : SF_sorted Rle ptd ->
  SF_h ptd = last (SF_h ptd) (SF_lx ptd) -> Riemann_sum f ptd = 0.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd IH] //= Hs Hhl.
  rewrite Riemann_sum_cons IH /= => {IH}.
  replace x0 with (SF_h ptd) ; try ring.
  apply Rle_antisym.
  rewrite Hhl => {Hhl} /=.
  apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
  replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
  apply Hs.
  apply SF_cons_ind with (s := ptd) => {ptd Hs} [x1 | [x1 y1] ptd IH] //=.
  apply lt_O_Sn.
  apply Hs.
  apply Hs.
  apply Rle_antisym.
  apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
  replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
  apply Hs.
  apply SF_cons_ind with (s := ptd) => {ptd Hs Hhl} [x1 | [x1 y1] ptd IH] //=.
  apply lt_O_Sn.
  move: Hhl ; rewrite -?(last_map (@fst R R)) /= => <- ; apply Hs.
Qed.

Lemma Riemann_sum_plus (f g : R -> R) ptd :
  Riemann_sum (fun x => f x + g x) ptd =
    Riemann_sum f ptd + Riemann_sum g ptd.
Proof.
Admitted.
Lemma Riemann_sum_minus (f g : R -> R) ptd :
  Riemann_sum (fun x => f x - g x) ptd =
    Riemann_sum f ptd - Riemann_sum g ptd.
Proof.
Admitted.

Lemma Riemann_sum_abs (f g : R -> R) ptd :
  (forall t, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t) <= g t)
  -> Rabs (Riemann_sum f ptd) <= Riemann_sum g ptd.
Proof.
Admitted.

Definition SF_last {T : Type} x0 (s : SF_seq) : (R*T) :=
  last (SF_h s,x0) (SF_t s).
Definition SF_belast {T : Type} (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (belast (SF_t s) : seq (R*T)).


Definition SF_head {T : Type} (x0 : T) (s : @SF_seq T) := (SF_h s, head x0 (SF_ly s)).
Definition SF_behead {T : Type} (s : @SF_seq T) :=
  mkSF_seq (head (SF_h s) (unzip1 (SF_t s))) (behead (SF_t s)).

Lemma ex_RInt_correct_aux_1 (f : R -> R) (a b : R) :
  forall pr : Riemann_integrable f a b,
    forall eps : posreal, exists alpha : posreal, 
    forall (ptd : SF_seq) (H : pointed_subdiv ptd), 
    seq_step (SF_lx ptd) < alpha -> 
    SF_h ptd = Rmin a b -> last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
    Rabs (RiemannInt pr - signe (b-a) * Riemann_sum f ptd) <= eps.
Proof.
  wlog: a b / (a < b) => [Hw | Hab].
    case: (total_order_T a b) => [[Hab | <-] | Hab] pr eps.
    by apply Hw.
    exists (mkposreal 1 Rlt_0_1) => ptd H _ (*_*) H0 H1.
    replace (Riemann_sum _ _) with 0.
    rewrite RiemannInt_P9 Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
    apply sym_equal, pointed_pty2 ; [by apply ptd_sort | rewrite {1}H0].
    move: H1 (Rle_refl a) ; rewrite /Rmin /Rmax ; 
    case: Rle_dec => //= _ <- _.
    move: (RiemannInt_P1 pr) => pr'.
    case: (Hw _ _ Hab pr' eps) ; rewrite Rmin_comm Rmax_comm => {Hw} alpha Hw ; 
    exists alpha ; intros.
    rewrite (RiemannInt_P8 pr pr').
    rewrite -(Ropp_minus_distr' b a) Ropp_signe 
    {1}/Rminus -(Ropp_plus_distr _ (_*_)) Rabs_Ropp
    Ropp_mult_distr_l_reverse.
    apply Hw => //.

  rewrite /Rmin /Rmax ; move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  rewrite /signe ;
  move: (Rlt_Rminus _ _ Hab) => Hab' ; 
  move: (Rlt_le _ _ Hab') (Rlt_not_eq _ _ Hab') ;
  case: Rle_dec => // H _ ; case: Rle_lt_or_eq_dec => // _ _ {H Hab'}.

  suff H : forall (phi : StepFun a b) (eps : posreal),
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (unzip1 (SF_t ptd)) = b ->
    Rabs (RiemannInt_SF phi - 1 * Riemann_sum phi ptd) <= eps.
    
  rewrite /RiemannInt /= => pr eps ; case: RiemannInt_exists => If HIf.
  set eps2 := pos_div_2 eps.
  set eps4 := pos_div_2 eps2.
(* RInt (f-phi) < eps/4 *)
  case: (HIf _ (cond_pos eps4)) => {HIf} N HIf.
  case: (nfloor_ex (/eps4) (Rlt_le _ _ (Rinv_0_lt_compat _ (cond_pos eps4)))) => n Hn.
  move: (HIf (N+n)%nat (le_plus_l _ _)) => {HIf}.
  rewrite /phi_sequence /R_dist ; case: pr => phi [psi pr] ; 
  simpl RiemannInt_SF => HIf.
(* RInt psi < eps/4*)
  have H0 : Rabs (RiemannInt_SF psi) < eps4.
    apply Rlt_le_trans with (1 := proj2 pr).
    rewrite -(Rinv_involutive eps4 (Rgt_not_eq _ _ (cond_pos eps4))) /=.
    apply Rle_Rinv.
    apply Rinv_0_lt_compat, eps4.
    intuition.
    apply Rlt_le, Rlt_le_trans with (1 := proj2 Hn).
    apply Rplus_le_compat_r.
    apply le_INR, le_plus_r.
(* Rsum phi < eps/4 and Rsum psi < eps/4 *)
  case: (H phi eps4) => alpha0 Hphi.
  case: (H psi eps4) => {H} alpha1 Hpsi.
  have Halpha : (0 < Rmin alpha0 alpha1).
    apply Rmin_case_strong => _ ; [apply alpha0 | apply alpha1].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd H Hstep (*Hsort*) Ha Hb.
  rewrite (double_var eps) 1?(double_var (eps/2)) ?Rplus_assoc.
  replace (_-_) with (-(RiemannInt_SF phi - If) 
    + (RiemannInt_SF phi - Riemann_sum f ptd)) ; 
    [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  rewrite Rabs_Ropp ; apply Rlt_le, HIf.
  clear HIf ;
  replace (_-_) with ((RiemannInt_SF phi - 1* Riemann_sum phi ptd) 
    + (Riemann_sum phi ptd - Riemann_sum f ptd)) ;
    [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Hphi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_l.
  rewrite -Ropp_minus_distr' Rabs_Ropp -Riemann_sum_minus.
  have H1 : (forall t : R, 
    SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t - phi t) <= psi t).
    move => t Ht.
    apply pr ; move: (Rlt_le _ _ Hab) ; rewrite /Rmin /Rmax ; 
    case: Rle_dec => // _ _ ; rewrite -Ha -Hb //.
  apply Rle_trans with (1 := Riemann_sum_abs _ _ _ H1).
  apply Rle_trans with (1 := Rle_abs _).
  replace (Riemann_sum _ _) with 
    (-(RiemannInt_SF psi - 1* Riemann_sum psi ptd) 
    + RiemannInt_SF psi) ; [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  rewrite Rabs_Ropp ; apply Hpsi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_r.
  apply Rlt_le, H0.
  
(* forall StepFun *)

  case => phi [lx [ly Hphi]] eps /= ;
  rewrite /RiemannInt_SF /subdivision /subdivision_val ;
  move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  move: (Rlt_le _ _ Hab) Hphi => {Hab} ;
  elim: lx ly eps a b => [ | lx0 lx IH] ly eps a b Hab.
(* lx = [::] *)
  case ; intuition ; by [].
  case: lx IH ly => [ | lx1 lx] IH ;
  case => [ {IH} | ly0 ly] Had ; try by (case: Had ; intuition ; by []).
(* lx = [:: lx0] *)
  exists eps => ptd Hptd Hstep (*Hsort*) Ha Hb /=.
  rewrite pointed_pty2.
  rewrite Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
  by apply ptd_sort.
  rewrite /SF_lx /= Hb Ha ; case: Had => {Ha Hb} _ [Ha [Hb _]] ; move: Ha Hb ;
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ <- <- //.
(* lx = [:: lx0, lx1 & lx] *)
  set eps2 := pos_div_2 eps ; set eps4 := pos_div_2 eps2.
(* * alpha1 from IH *)
  case: (IH ly eps4 lx1 b) => {IH}.
  
  replace b with (last 0 (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx)))).
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1%nat)
  with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; apply lt_n_S, lt_O_Sn.
  case: Had => /= _ [_ [Hb _]] ; move: Hb ; rewrite /Rmax ; 
  case: Rle_dec => //= _ ;
  elim: (lx) lx1  => //= h s IH _ ; apply IH.
  apply (StepFun_P7 Hab Had).
  
  move => /= alpha1 IH.
(* * alpha2 from H *)  
  suff H : forall eps : posreal,
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (SF_lx ptd) = lx1 ->
    Rabs (ly0 * (lx1 - lx0) - Riemann_sum phi ptd) <= eps.

  case: (H eps4) => {H} alpha2 H.
(* * alpha3 from (fmax - fmin) *)
  set fmin1 := foldr Rmin 0 (ly0::Rlist2seq ly).
  set fmin2 := foldr Rmin 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmin := Rmin fmin1 fmin2.
  set fmax1 := foldr Rmax 0 (ly0::Rlist2seq ly).
  set fmax2 := foldr Rmax 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmax := Rmax fmax1 fmax2.
  
  have Ha3 : (0 < eps4 / (Rmax (fmax - fmin) 1)).
    apply Rdiv_lt_0_compat ; [ apply eps4 | ].
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha3 := mkposreal _ Ha3.  
(* * alpha = Rmin (Rmin alpha1 alpha2) alpha3 *)  
  have Halpha : (0 < Rmin (Rmin alpha1 alpha2) alpha3).
    apply Rmin_case_strong => _ ; [ | apply alpha3].
    apply Rmin_case_strong => _ ; [ apply alpha1 | apply alpha2].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd Hptd Hstep Ha Hb.

  suff Hff : forall x, a <= x <= b -> fmin <= phi x <= fmax.
  suff Hab1 : forall i, (i <= SF_size ptd)%nat -> a <= nth 0 (SF_lx ptd) i <= b.
  suff Hab0 : a <= lx1 <= b.

  rewrite /Riemann_sum (SF_Chasles (phi (SF_h ptd)) _ lx1) /=.
  replace (_-_) with 
    ((ly0 * (lx1 - lx0) - 1* RInt_seq (SF_cut_down (phi (SF_h ptd)) (SF_map phi ptd) lx1) Rplus Rmult 0)
    + (Int_SF ly (RList.cons lx1 lx) - 1* RInt_seq (SF_cut_up (phi (SF_h ptd)) (SF_map phi ptd) lx1) Rplus Rmult 0))
    ; [ | by ring_simplify].
  
  rewrite (double_var eps) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* partie [lx0;lx1] *)

  replace (SF_cut_down _ _ _: @SF_seq R) with 
  (SF_map phi (SF_cut_down (SF_h ptd) ptd lx1) : @SF_seq R).

  set ptd_r_last := (SF_last a (SF_cut_down a ptd lx1)).
  set ptd_r_belast := (SF_belast (SF_cut_down a ptd lx1)).
  set ptd_r := SF_rcons ptd_r_belast (lx1, (fst (SF_last a ptd_r_belast) + lx1)/2).

  move: (H ptd_r) => {H} H.

  replace (_-_) with ((ly0 * (lx1 - lx0) - Riemann_sum phi ptd_r) +
    (phi ((fst (SF_last 0 ptd_r_belast) + lx1)/2) - phi (snd ptd_r_last)) 
      * (lx1 - fst (SF_last 0 ptd_r_belast))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* * appliquer H *)
  apply: H => {IH}.
  
  Focus 3.
    rewrite -Ha /ptd_r /ptd_r_belast.
    move: (proj1 Hab0) ; rewrite -Ha.
    apply SF_cons_dec with (s := ptd) => [x0 | [x0 y0] s] //= Hx0 ;
    by case: Rle_dec.
  Focus 3.
    revert ptd_r_belast ptd_r ; move: (proj1 Hab0) ;
    rewrite -Ha ;
    apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] 
    //= Hx0 ; case: Rle_dec => //= _.
    by rewrite unzip1_rcons /= last_rcons.

(* ** ptd_r est une subdivision pointée *)

  revert ptd_r_belast ptd_r Hptd ;
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH ] Hptd.
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.

  case => /= [ _ | i Hi] .  
  case: Rle_dec => //= Hx0.
  pattern lx1 at 3 ; replace lx1 with ((lx1 + lx1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  split ; apply Req_le ; by field.
  contradict Hi ; apply le_not_lt.
  case: Rle_dec => //= Hx0 ; rewrite /SF_size /= ;
  apply le_n_S, le_O_n.
  
  move: (IH (ptd_cons _ _ Hptd)) => {IH} IH.
  case => [ _ | i Hi].
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: Rle_dec => //= Hx0.
  case: Rle_dec => //= Hx1.
  move: Hptd Hx1 ; apply SF_cons_dec with (s := s) 
    => {s IH} /= [x1 | [x1 y1] s] //= Hptd Hx1.
  by apply (Hptd O (lt_O_Sn _)).
  case: Rle_dec => //= Hx2.
  by apply (Hptd O (lt_O_Sn _)).
  by apply (Hptd O (lt_O_Sn _)).
  pattern lx1 at 3 ; replace lx1 with ((lx1 + lx1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  split ; apply Req_le ; by field.
  move: Hi (IH i) => {IH}.
  rewrite ?SF_size_rcons -?SF_size_lx ?SF_lx_rcons ?SF_ly_rcons.
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -?unzip1_fst.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: (Rle_dec x0 lx1) => //= Hx0.
  case: (Rle_dec (SF_h s) lx1) => //= Hx1.
  rewrite size_belast size_belast'.
  move: Hx1 ;
  apply SF_cons_dec with (s := s) => {s Hptd} /= [ x1 | [x1 y1] s] //= Hx1.
  move => Hi IH ; apply IH ; by apply lt_S_n.
  case: Rle_dec => //= Hx2.
  
  move => Hi IH ; apply IH ; by apply lt_S_n.
  
  move => Hi IH ; apply IH ; by apply lt_S_n.
  
  move => Hi ; by apply lt_S_n, lt_n_O in Hi.
  move => Hi ; by apply lt_S_n, lt_n_O in Hi.
  
  apply Rlt_le_trans with (2 := Rmin_r alpha1 alpha2) ;
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep) => {Hstep}.
  move: Hab0 ; rewrite -Ha -Hb ;
  revert ptd_r_belast ptd_r => {Hab1} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //= Hab0.
  rewrite /SF_lx /SF_rcons /SF_belast /SF_last /SF_cut_down /=.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) /seq_step /=.
  rewrite Rminus_eq0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  move: Hab0 (fun Hx1 => IH (conj Hx1 (proj2 Hab0))) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hab0 IH.
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: Rle_dec => //= Hx1.
  rewrite /seq_step /=.
  apply Rle_max_compat_l.
  rewrite (Rle_antisym _ _ Hx1 (proj2 Hab0)) Rminus_eq0 Rabs_R0.
  apply Rmax_case_strong ; by intuition.
  rewrite /seq_step /=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  apply Rplus_le_compat_r.
  by apply Rlt_le, Rnot_le_lt.
  apply Rle_ge ; rewrite -Rminus_le_0 ; by apply Hab0.
  move: IH ; rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: (Rle_dec x1 lx1) => //= Hx1 IH.
  move: (IH Hx1) => {IH}.
  case: (Rle_dec (SF_h s) lx1) => //= Hx2.
  rewrite /seq_step -?(last_map (@fst R R)) /= => IH ; 
  apply Rle_max_compat_l, IH.
  rewrite /seq_step /= ; apply Rle_max_compat_l.
  rewrite /seq_step /= ; apply Rmax_le_compat.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
  apply Rle_ge ; rewrite -Rminus_le_0 ; apply Hab0.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  apply SF_cons_ind with (s := s) => {s IH Hab0} /= [x2 | [x2 y2] s IH] //=.
  exact: Rle_refl.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  exact: IH.
(* ** transition 1 *) 
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (fst (SF_last 0 ptd_r_belast) + lx1) / 2 <= b.
  suff H1 : a <= snd ptd_r_last <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_r_last Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  replace a with ((a+a)/2) by field.
  replace b with ((b+b)/2) by field.
  split ; apply Rmult_le_compat_r, Rplus_le_compat ; try by intuition.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  
  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite Rabs_right.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_r_belast ptd_r Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /SF_cut_down /SF_belast /SF_last /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) ; apply Req_le ; by ring.
  move => Hptd Hab0 ; 
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  rewrite /SF_cut_down /SF_belast /SF_last /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx3.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
  
  apply Rle_ge ; rewrite -Rminus_le_0.
  revert ptd_r_belast ptd_r ; rewrite -Ha in Hab0 ; move: (proj1 Hab0) ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down /SF_belast /SF_last /=.
  by case: Rle_dec.
  move: IH ; rewrite /SF_cut_down /SF_belast /SF_last /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= Hx1 IH.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //=.
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] //= Hx2.
  case: (Rle_dec (SF_h s) _) => //=.
  
  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.
  
  clear H IH.
  rewrite Rplus_assoc -Ropp_minus_distr Rmult_1_l.
  apply (f_equal (Rminus (ly0 * (lx1 - lx0)))).
  revert ptd_r_last ptd_r_belast ptd_r ; move: (proj1 Hab0) ; 
  rewrite -Ha => {Hab0} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down /=.
  case: (Rle_dec x0 lx1) => //= _.
  rewrite /Riemann_sum /RInt_seq /=.
  by ring.
  case: (Rle_dec (SF_h s) lx1) => //= => Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} [x1 | [x1 y1] s] /= Hx1.
  rewrite /SF_cut_down /= ; 
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _.
  rewrite /Riemann_sum /RInt_seq /= => _.
  ring.
  rewrite /SF_cut_down /= ; 
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _ ;
  case: (Rle_dec (SF_h s) _) => //= Hx2.
  rewrite (SF_map_cons _ (x0,y0) (mkSF_seq x1 ([:: (SF_h s, y1) & seq_cut_down (SF_t s) lx1 y1])))
    RInt_seq_cons /=.
  move => <-.
  rewrite /SF_belast /SF_last /SF_rcons /=.
  rewrite /Riemann_sum.
  rewrite (SF_map_cons _ (x0,y0) (mkSF_seq x1 (rcons _ _))) RInt_seq_cons /=.
  rewrite -!(last_map (@fst R R)) -!unzip1_fst /=.
  ring.
  rewrite /Riemann_sum /RInt_seq /= => _ ; ring.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= _ ; case: Rle_dec => //= _.
  rewrite /Riemann_sum /RInt_seq /= ; ring.
  
  apply SF_cons_ind with (s := ptd) => {IH} /= [x0 | [x0 y0] s IH] /=.
  rewrite /SF_cut_down /= ; by case: Rle_dec.
  move: IH.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] /=.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= _ ; case: Rle_dec => //=.
  rewrite /SF_cut_down /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec x1 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= _.
  rewrite (SF_map_cons _ (x0,y0) (mkSF_seq x1 ((SF_h s, y1) :: seq_cut_down (SF_t s) lx1 y1))) /=.
  by move => -> /=.
(* partie [lx1 ; b] *)
  replace (SF_cut_up _ _ _: @SF_seq R) with 
  (SF_map phi (SF_cut_up (SF_h ptd) ptd lx1) : @SF_seq R).

  set ptd_l_head := (SF_head a (SF_cut_up a ptd lx1)).
  set ptd_l_behead := (SF_behead (SF_cut_up a ptd lx1)).
  set ptd_l := SF_cons (lx1, (lx1 + fst (SF_head a ptd_l_behead))/2) ptd_l_behead.

  move: (IH ptd_l) => {IH} IH.

  replace (_-_) with ((Int_SF ly (RList.cons lx1 lx) - 1 * Riemann_sum phi ptd_l) -
    (phi ((lx1 + fst (SF_head 0 ptd_l_behead))/2) - phi (snd ptd_l_head)) 
      * (lx1 - fst (SF_head 0 ptd_l_behead))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
(* * hypothèse d'induction *)
  apply: IH.
(* ** ptd_l est une subdivision pointée *)
  case.
  move => _ ; move: (proj1 Hab0) ; rewrite -Ha => /= Hx0 ;
  case: Rle_dec => //= _.
  rewrite seq_cut_up_head.
  move: Hx0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  split ; apply Req_le ; field.
  case: Rle_dec => //= Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: Rle_dec => //= Hx2.
  pattern (SF_h s) at 3 ; replace (SF_h s) with ((SF_h s+SF_h s)/2) by field.
  pattern lx1 at 1 ; replace lx1 with ((lx1+lx1)/2) by field.
  apply Rnot_le_lt, Rlt_le in Hx1 ; split ;
  apply Rmult_le_compat_r ; by intuition.
  rewrite /ptd_l SF_lx_cons SF_ly_cons SF_size_cons => i Hi ;
  move: i {Hi} (lt_S_n _ _ Hi).
  revert ptd_l_behead ptd_l Hptd ;
  apply SF_cons_ind with (s := ptd) 
    => /= [x0 | [x0 y0] s IH] /= Hptd.
  rewrite /SF_cut_up /=.
  case: Rle_dec => //=.
  rewrite /SF_size /SF_behead /= => _ i Hi ; by apply lt_n_O in Hi.
  move: (IH (ptd_cons _ _ Hptd)) => {IH}.
  rewrite /SF_cut_up /=.
  case: (Rle_dec x0 _) => //= Hx0.
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  rewrite !seq_cut_up_head.
  move: Hx1 ; apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //= Hx2.
(* * seq_step (SF_lx ptd_l) < alpha1 *)
  apply Rlt_le_trans with (2 := Rmin_l alpha1 alpha2).
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep).
  revert ptd_l_behead ptd_l ; move :(proj1 Hab0) ;
  rewrite -Ha ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] /= s IH] Hx0.
  rewrite /SF_cut_up /= ; case: (Rle_dec x0 _) => //= _.
  rewrite /seq_step /= Rminus_eq0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  rewrite /SF_cut_up /= ; case: (Rle_dec x0 _) => //= _.
  move: IH ; rewrite /SF_cut_up /= ; case: (Rle_dec (SF_h s) _) => //= Hx1 ;
  rewrite ?seq_cut_up_head => IH.
  move: Hx1 (IH Hx1) => {IH} ; 
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx1 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; 
  exact: RmaxLess2.
  move: IH ; case: (Rle_dec (SF_h s) _) => //= Hx2 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; 
  exact: RmaxLess2.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; 
  exact: RmaxLess2.
  clear IH ; rewrite /seq_step/=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_l, Ropp_le_contravar.
  by apply Rle_ge, (Rminus_le_0 lx1 _), Rlt_le, Rnot_le_lt.
  by rewrite /ptd_l /=.
  rewrite -Hb.
  move: (proj1 Hab0) ; rewrite -Ha /=;
  case: (Rle_dec (SF_h ptd) lx1) => //= _ _.
  rewrite seq_cut_up_head.
  move: Hab0 ; rewrite -Ha -Hb ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= [Hx0 Hlx1].
  by apply Rle_antisym.
  move: (fun Hx1 => IH (conj Hx1 Hlx1)) => {IH} ;
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  move => IH ; rewrite -(IH Hx1) => {IH}.
  move: Hx1 Hlx1 ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s ] Hx1 Hlx1.
  by [].
  case: (Rle_dec (SF_h s) _) => /= Hx2 ;
  by [].
(* ** transition 2 *) 
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_Ropp Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (lx1 + fst (SF_head 0 ptd_l_behead)) / 2 <= b.
  suff H1 : a <= snd ptd_l_head <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_l_head Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_up /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_up /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  replace a with ((a+a)/2) by field.
  replace b with ((b+b)/2) by field.
  split ; apply Rmult_le_compat_r, Rplus_le_compat ; try by intuition.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up /SF_head /= -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite ?seq_cut_up_head.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite !seq_cut_up_head.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  
  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite -Rabs_Ropp Rabs_right ?Ropp_minus_distr'.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_l_behead ptd_l Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  apply Req_le ; by ring.
  move => Hptd Hab0 ; 
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  rewrite !seq_cut_up_head in IH |-*.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar, Hab0.

  apply Rle_ge, (Rminus_le_0 lx1).
  revert ptd_l_behead ptd_l ; rewrite -Ha -Hb in Hab0 ; move: Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  case: Rle_dec => /= _.
  exact: Rle_refl.
  exact: (proj2 Hx0).
  move: (proj1 Hx0) ; case: Rle_dec => //= _ _.
  move: (fun Hx1 => IH (conj Hx1 (proj2 Hx0))) => {IH}.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  rewrite !seq_cut_up_head in IH |-* ; move: (IH Hx1) => {IH}.
  move: Hx0 Hx1 ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx0 Hx1 IH.
  exact: Rle_refl.
  move: IH ; case: (Rle_dec (SF_h s)) => /= Hx2.
  by [].
  by [].
  by apply Rlt_le, Rnot_le_lt, Hx1.
  
  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.
  
  clear H IH.
  rewrite !Rmult_1_l {1 2}/Rminus Rplus_assoc -Ropp_plus_distr.
  apply (f_equal (Rminus _)) => /=.
  rewrite /ptd_l /ptd_l_behead /ptd_l_head /= /SF_cut_up /= ; 
  move: Hab0 ; rewrite -Ha -Hb /= ; 
  case => [Hx0 Hlx1].
  case: (Rle_dec (SF_h ptd)) => //= _.
  rewrite ?seq_cut_up_head /SF_ly /= /Riemann_sum SF_map_cons RInt_seq_cons /=.
  move: Hx0 Hlx1 ; apply SF_cons_ind with (s := ptd) 
    => [x0 | [x0 y0] s /= IH] /= Hx0 Hlx1.
  rewrite /RInt_seq /= ; ring.
  case: (Rle_dec (SF_h s)) => //= Hx1.
  move: (IH Hx1 Hlx1) => /= {IH}.
  move: Hx1 Hlx1 ; apply SF_cons_dec with (s := s) 
    => {s} [x1 | [x1 y1] s /=] /= Hx1 Hlx1 IH.
  rewrite /RInt_seq /= ; ring.
  move: IH ; case: (Rle_dec (SF_h s)) => //= Hx2.
  move => <- ; apply Rminus_diag_uniq ; ring_simplify.
  move: Hx2 Hlx1 y1 ; apply SF_cons_ind with (s := s) 
    => {s} [x2 | [x2 y2] s /= IH] /= Hx2 Hlx1 y1.
  ring.
  case: (Rle_dec (SF_h s)) => //= Hx3.
  by apply IH.
  ring.
  ring_simplify.
  rewrite (SF_map_cons _ (lx1,y0) s) RInt_seq_cons /=.
  rewrite /SF_behead /= ; ring_simplify ; by case: (s).
  
  apply SF_cons_ind with (s := ptd) => {IH} /= [x0 | [x0 y0] s IH] /=.
  rewrite /SF_cut_up /= ; by case: Rle_dec.
  move: IH.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] /=.
  rewrite /SF_cut_up /= ; case: Rle_dec => //= _ ; case: Rle_dec => //=.
  rewrite /SF_cut_up /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec x1 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= _.
  by rewrite ?seq_cut_up_head.
  rewrite -Ha -Hb in Hab0 ; move: Hab0.
  rewrite -(last_map (@fst R R)) -unzip1_fst /=.
  replace (unzip1 (map (fun x : R * R => (fst x, phi (snd x))) (SF_t ptd)))
    with (unzip1 (SF_t ptd)).
  by [].
  elim: (SF_t ptd) => {IH} [ | [x0 y0] s IH] //=.
  by rewrite IH.
  
  replace lx1 with (pos_Rl (RList.cons lx0 (RList.cons lx1 lx)) 1) by reflexivity.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ; 
  case: Rle_dec => // _ <- <-.
  rewrite -(seq2Rlist_bij (RList.cons lx0 _)) !nth_compat size_compat.
  split.
  rewrite nth0.
  apply (sorted_head (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.
  simpl ; rewrite -last_nth.
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1) with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.
  
  rewrite -Ha -Hb /SF_lx /= => i Hi.
  apply le_lt_n_Sm in Hi ; rewrite -SF_size_lx /SF_lx in Hi.
  split.
  exact: (sorted_head (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).
  exact: (sorted_last (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).

  clear H IH.
  move => x Hx ; case: (sorted_dec ([:: lx0, lx1 & Rlist2seq lx]) 0 x).
  apply sorted_compat ; rewrite /= seq2Rlist_bij ; apply Had.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ; 
  case: Rle_dec => // _.
  rewrite -nth0 -nth_last /= => -> Hb'.
  split.
  by apply Hx.
  elim: (lx) (lx1) Hb' => /= [ | h1 s IH] h0 Hb'.
  rewrite Hb' ; by apply Hx.
  by apply IH.
  case => i ; case ; case ; case => {Hx} Hx Hx' Hi.
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (S i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ; 
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  have : (((size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat) < 
    size [:: lx0, lx1 & Rlist2seq lx])%nat.
    by [].
  replace (size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat with 
    (S (size [:: lx0, lx1 & Rlist2seq lx] - 2)) by (simpl ; intuition).
  move: (size [:: lx0, lx1 & Rlist2seq lx] - 2)%nat => i Hi.
  case ; case => {Hx} Hx ; [ case => Hx' | move => _ ].
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ; 
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite Hx'.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] (S i)) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: s IH Hi => /= [ | h1 s] IH Hi.
  by apply lt_S_n, lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; 
  [ apply Rle_trans with (1 := Rmin_r _ _) ; exact: Rmin_l 
  | apply Rle_trans with (2 := RmaxLess2 _ _) ; exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.

(* preuve de H *)  
  clear eps eps2 IH eps4 alpha1.
  move: (proj1 (proj2 Had)) => /= ; rewrite /Rmin ; 
    case: Rle_dec => //= _ <-.
  move: (proj1 Had O (lt_O_Sn _)) => /= Hl0l1.
  move: (proj2 (proj2 (proj2 (proj2 Had))) O (lt_O_Sn _)) => /= Hval.
  clear a b Hab Had lx ly.
  rename lx0 into a ; rename lx1 into b ; 
  rename ly0 into c ; rename Hl0l1 into Hab.
  
  set fmin := Rmin (Rmin (phi a) (phi b)) c.
  set fmax := Rmax (Rmax (phi a) (phi b)) c.
  
  move => eps ; set eps2 := pos_div_2 eps.
  have Halpha : 0 < eps2 / (Rmax (fmax - fmin) 1).
    apply Rdiv_lt_0_compat.
    apply eps2.
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd.
  apply SF_cons_ind with (s := ptd) 
    => {ptd} [x0 | [x0 y0] ptd IH] Hptd Hstep Ha Hb ; simpl in Ha, Hb.
  rewrite -Ha -Hb /Riemann_sum /RInt_seq /= ;
  rewrite Rminus_eq0 Rmult_0_r Rminus_0_r Rabs_R0.
  by apply Rlt_le, eps.
  move: (fun Ha => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep) Ha Hb)
    => {IH} IH.
  move: (proj1 (ptd_sort _ Hptd)) ; 
  rewrite Ha in Hptd, Hstep |- * => {x0 Ha} ; 
  case => /= Ha.
  rewrite /Riemann_sum SF_map_cons RInt_seq_cons /= => {IH}.
  replace (_-_) with ((c-phi y0) * (SF_h ptd - a) 
    + (c * (b - SF_h ptd) - RInt_seq (SF_map phi ptd) Rplus Rmult 0)) ;
    [ | by ring_simplify].
  rewrite (double_var eps) ; 
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ; 
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  rewrite -Hb ; 
  apply (sorted_last (SF_lx ptd) 0 (proj2 (ptd_sort _ Hptd)) (lt_O_Sn _)) 
    with (x0 := 0).
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ; 
  rewrite /seq_step /= ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.
  
  move: (ptd_cons _ _ Hptd) 
  (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep : seq_step (SF_lx ptd) < alpha) 
  Ha Hb => {Hptd Hstep y0} Hptd Hstep Ha Hb.
  suff : SF_h ptd <= b.
  case => Hx0.
  move: Hptd Hstep Ha Hb Hx0.
  apply SF_cons_ind with (s := ptd) => {ptd} 
    [x0 | [x0 y0] ptd IH] Hptd Hstep /= Ha Hb Hx0.
  contradict Hb ; apply Rlt_not_eq, Hx0.
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep)
    (Rlt_le_trans _ _ _ Ha (proj1 (ptd_sort _ Hptd))) Hb Hx1) => {IH} IH.
  rewrite SF_map_cons RInt_seq_cons /=.
  have : SF_h ptd <= b.
    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
    apply lt_O_Sn.
  case => Hx1.
  rewrite Hval.
  replace (_-_) with (c * (b - SF_h ptd) - RInt_seq (SF_map phi ptd) Rplus Rmult 0)
  by (ring_simplify ; auto).
  by apply IH.
  split.
  apply Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_lt_trans with (2 := Hx1), (Hptd O (lt_O_Sn _)).
  rewrite Hx1 -/(Riemann_sum phi ptd) pointed_pty2.
  replace (c * (b - x0) - (phi y0 * (b - x0) + 0))
    with ((c - phi y0) * (b - x0)) by ring.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ; 
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply Rlt_le, Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  by apply Req_le.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ; 
  rewrite /seq_step /= -Hx1 ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.
  apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
  by rewrite /SF_lx /= Hb.
  rewrite Hx0 -/(Riemann_sum phi ptd) pointed_pty2.
  replace (c * (b - b) - 0) with 0 by ring.
  rewrite Rabs_R0 ; apply Rlt_le, eps2.
  apply ptd_sort, Hptd.
  by rewrite /SF_lx /= Hb.
  
    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, Hptd.
    apply lt_O_Sn.
  rewrite Riemann_sum_cons /= -Ha.
  rewrite Rminus_eq0 Rmult_0_r Rplus_0_l.
  by apply IH.
Qed.

(** TODO : Corriger ex_RInt avec convergence des sommes *)

Lemma ex_RInt_correct_1 (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> ex_RInt f a b.
Proof.
Admitted.

Lemma ex_RInt_correct_2 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
Admitted.


(** * The RInt function *)

Lemma ex_RInt_cv (f : R -> R) (a b : R) : 
  ex_RInt f a b -> ex_lim_seq (RInt_val f a b).
Admitted. (** Admitted *)

Definition RInt (f : R -> R) (a b : R) := 
  match Rle_dec a b with
    | left _ => Lim_seq (RInt_val f a b)
    | right _ => -Lim_seq (RInt_val f b a)
  end.

Lemma RInt_correct (f : R -> R) (a b : R) :
  forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
Admitted. (** Admitted *) (** Admitted *)

Lemma RInt_ext (f g : R -> R) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) -> RInt f a b = RInt g a b.
Proof.
  move => Hf ; rewrite /RInt /RInt_val.
Admitted. (** Admitted *) (** Admitted *)

Lemma RInt_const (a b c : R) :
  RInt (fun _ => c) a b = c * (b-a).
Proof.
  rewrite (RInt_correct _ _ _ (Riemann_integrable_const _ _ _))
          RiemannInt_const //.
Admitted. (** Admitted *) (** Admitted *)
Lemma RInt_Chasles (f : R -> R) (a b c : R) :
  RInt f a c = RInt f a b + RInt f b c.
Proof.
Admitted. (** Admitted *) (** Admitted *)

(** * Riemann integral and derivative *)

Lemma derivable_pt_lim_RInt (f : R -> R) (a : R) (x : R) :
  ex_RInt f a x -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x -> derivable_pt_lim (fun x => RInt f a x) x (f x).
Proof.
  move => Iax Iloc Cx e He ; set eps := mkposreal e He.
Admitted. (** Admitted *) (** Admitted. *)

Lemma RInt_Derive (f : R -> R) (a b : R) (eps : posreal) :
  (forall x, Rmin a b - eps <= x <= Rmax a b + eps -> ex_derive f x) ->
  continuity_pt (Derive f) a -> continuity_pt (Derive f) b ->
  RInt (Derive f) a b = f b - f a.
Proof.
Admitted. (** Admitted. *)
