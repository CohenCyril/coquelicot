Require Import Reals Div2.
Require Import ssreflect ssrbool eqtype seq.
Require Import Markov Rcomplements Floor Total_sup Sup_seq Lim_seq Derive SF_seq.


(*
(** * compatibilities with ssreflect *)
(** ** ssrnat *)


Lemma SSR_add (n m : nat) : ssrnat.addn n m = (n + m)%nat.
Proof.
  elim: m n => //.
Qed.

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

Definition pointed_subdiv (sigma xi : seq R) :=
  size sigma = S (size xi) 
  /\ (forall i, (i < size xi)%nat -> nth 0 sigma i <= nth 0 xi i <= nth 0 sigma (S i)).
Lemma pointed_pty0 (x0 y0 : R) (sigma xi : seq R) : 
  pointed_subdiv (x0::sigma) (y0::xi) -> pointed_subdiv sigma xi.
Proof.
  case => H H0 ; split ; intuition ; apply (H0 (S i) (lt_n_S _ _ H1)).
Qed.
Lemma pointed_pty1 (sigma xi : seq R) : 
  pointed_subdiv sigma xi -> sorted Rle sigma.
Proof.
  case: sigma => [| x0 sigma].
    case => //.
  elim: sigma x0 xi => [| x1 sigma IH] x0 ; case => [| y0 xi] ; case => H H0 //.
  split.
  apply Rle_trans with y0 ; apply (H0 O (lt_O_Sn _)).
  apply (IH x1 xi) ; apply (pointed_pty0 x0 y0) ; split => //.
Qed.

Lemma sorted_const (s : seq R) : sorted Rle s -> head 0 s = last 0 s -> 
  forall i, (i < size s)%nat -> nth 0 s i = head 0 s.
Proof.
  move => Hs Heq.
  have H : (forall i, (i < size s)%nat -> head 0 s <= nth 0 s i <= last 0 s).
    move => i Hi ; split.
    apply sorted_head => //.
    apply sorted_last => //.
  move => i Hi ; apply Rle_antisym.
  rewrite Heq ; apply H => //.
  apply H => //.
Qed.

Definition seq_step s := 
  foldr Rmax 0 (pairmap (fun x y => Rabs (Rminus y x)) (head 0 s) (behead s)).

Definition Riemann_sum (f : R -> R) (sigma xi : seq R) 
  (H : pointed_subdiv sigma xi) :=
  RInt_seq (SF_map f (SF_make sigma xi (proj1 H))) Rplus Rmult 0.

Lemma pointed_pty2 f (sigma xi : seq R) : 
  forall (H : pointed_subdiv sigma xi), 
  head 0 sigma = last 0 sigma -> Riemann_sum f sigma xi H = 0.
Proof.
  case: sigma => [| x0 sigma] //.
  case => //.
  elim: sigma x0 xi => [| x1 sigma IH] x0 ; case => [| y0 xi] H Heq //.
  move: (IH x1 xi (pointed_pty0 _ _ _ _ H)) => {IH}.
  replace (Riemann_sum f [:: x0, x1 & sigma] (y0 :: xi) H) 
    with (f y0 * (x1 - x0) 
      + Riemann_sum f (x1 :: sigma) xi (pointed_pty0 x0 y0 (x1 :: sigma) xi H)).
  move => ->.
  move: (sorted_const _ (pointed_pty1 _ _ H) Heq 1%nat 
    (lt_n_S _ _ (lt_O_Sn _))) => /= -> ; ring.
  
  rewrite -nth_last ; move: (sorted_const _ (pointed_pty1 _ _ H) Heq _
    (lt_n_Sn _)) => /= ->.
  move: (sorted_const _ (pointed_pty1 _ _ H) Heq 1%nat 
    (lt_n_S _ _ (lt_O_Sn _))) => //=.
    rewrite /Riemann_sum /RInt_seq /=.
    case: sigma H Heq  => [| x2 sigma] ; case: xi => [| y1 xi] //.
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

Lemma ex_RInt_correct_aux_1 (f : R -> R) (a b : R) :
  forall pr : Riemann_integrable f a b,
    forall eps : posreal, exists alpha : posreal, 
    forall (sigma xi : seq R) (H : pointed_subdiv sigma xi), 
    sorted Rlt sigma ->
    seq_step sigma < alpha -> 
    head 0 sigma = Rmin a b -> last 0 sigma = Rmax a b ->
    Rabs (RiemannInt pr - signe (b-a) * Riemann_sum f sigma xi H) <= eps.
Proof.
  wlog: a b / (a < b) => [Hw | Hab].
    case: (total_order_T a b) => [[Hab | <-] | Hab] pr eps.
    by apply Hw.
    exists (mkposreal 1 Rlt_0_1) => sigma xi H _ _ H0 H1.
    replace (Riemann_sum _ _ _ _) with 0.
    rewrite RiemannInt_P9 Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
    apply sym_equal, pointed_pty2 ; rewrite H1 //.
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
  
have S1 : forall a0 b0 f0, a <= a0 -> a0 <= b0 -> b0 <= b ->
  forall (f := mkSF_seq a0 [::(b0,f0)]) (eps : posreal),
  exists alpha : posreal,
  forall (sigma xi : seq R) (H : pointed_subdiv sigma xi),
  sorted Rlt sigma ->
  seq_step sigma < alpha ->
  head 0 sigma = a ->
  last 0 sigma = b ->
  Rabs (RInt_seq f Rplus Rmult 0 - Riemann_sum (SF_fun f 0) sigma xi H) <= eps.

  move => {f} a0 b0 f0 Ha Hdom Hb ; 
  case: (Req_dec f0 0) => [ -> | Hf0] f eps.
  exists (mkposreal _ Rlt_0_1) => sigma xi H _ _ H0 H1.
  replace (Riemann_sum (SF_fun f 0) _ _ _) with 0.
  replace (RInt_seq f _ _ _) with 0.
  rewrite Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
  rewrite /f /RInt_seq /= => {f} ; ring.
  rewrite /f /Riemann_sum /= => {f}.
  rewrite -H0 in Ha => {H0}.
  case: sigma H {H1 Ha} => [| x0 sigma].
  by case.
  elim: sigma x0 xi => [|x1 sigma IH] x0 ;
  case => [ | y0 xi] ; try by case.
  move => H ;
  move: (IH x1 xi (pointed_pty0 x0 y0 _ _ H)) => {IH}.
  rewrite /RInt_seq /= .
  replace (_*_) with 0.
  rewrite Rplus_0_l.
  case: sigma xi H => [| x2 sigma] ; case => [ | y1 xi] ; try by case.
  rewrite /SF_fun /= ; case: Rlt_dec ; try case: Rle_dec ; intros ; ring.

  have Halp : ( 0 < eps / (2*Rabs f0)) ; [ | set alpha := mkposreal _ Halp].
    apply Rdiv_lt_0_compat, Rmult_lt_0_compat ; 
    [apply eps | apply Rlt_R0_R2 | apply Rabs_pos_lt, Hf0].
  exists alpha ; case => [ | x0 sigma] xi H Hsort Hstep H0 H1 ; 
  try by case H.
  simpl in H0 ; rewrite -H0 in Ha, Hab => {a H0}.
  simpl in H1 ; rewrite -H1 in Hb, Hab => {b H1}.
  case: sigma xi H Ha Hb Hab Hsort Hstep => [ | x1 sigma ] ; 
  case => [ | y0 xi] ; try by case.
  intros ; contradict Hab ; apply Rle_not_lt, Rle_refl.
  move => H Ha Hb _ ; move: H Ha Hb ;
  elim: sigma x0 x1 xi y0 => [| x2 sigma IH] x0 x1 ;
  case => [ | y1 xi] y0 ; try by case.
  intros ; rewrite /Riemann_sum /RInt_seq /= ?Rplus_0_r.
  rewrite /SF_fun /=.
  replace (pos eps) with (Rabs f0 * alpha + Rabs f0 * alpha) ; 
  [ | simpl ; field ; by apply Rabs_no_R0].
  case: Rlt_dec => Hy.
  rewrite -(Rplus_0_r (Rabs _)) Rmult_0_l Rminus_0_r Rabs_mult ;
  apply Rplus_le_compat.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep).
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  rewrite ?Rabs_pos_eq.
  apply Rplus_le_compat, Ropp_le_contravar => // ; by rewrite H1.
  apply Rlt_le, Rlt_Rminus, Hsort.
  rewrite -Rminus_le_0 //.
  apply Rmult_le_pos ; intuition ; apply Rabs_pos.
  case: Rle_dec => Hy'.
  apply Rle_trans with (1 := Rabs_triang _ _) ;
  rewrite Rabs_Ropp ?Rabs_mult.
  apply Rplus_le_compat ; apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep).
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  rewrite ?Rabs_pos_eq.
  apply Rplus_le_compat, Ropp_le_contravar => //.
  apply Rlt_le, Rlt_Rminus, Hsort.
  rewrite -Rminus_le_0 //.
  apply Rabs_pos.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep).
  rewrite /seq_step /=.
  apply RmaxLess1.
  rewrite -(Rplus_0_r (Rabs _)) Rmult_0_l Rminus_0_r Rabs_mult ;
  apply Rplus_le_compat.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep).
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  rewrite ?Rabs_pos_eq.
  apply Rplus_le_compat, Ropp_le_contravar => // ; by rewrite H1.
  apply Rlt_le, Rlt_Rminus, Hsort.
  rewrite -Rminus_le_0 //.
  apply Rmult_le_pos ; intuition ; apply Rabs_pos.
  
  intros ; move: (pointed_pty0 _ _ _ _ H) => H'.
  have Hstep' : seq_step [:: x1, x2 & sigma] < alpha.
    apply Rle_lt_trans with (2 := Hstep) ;
    rewrite /seq_step /= ; apply RmaxLess2.
  move: (fun Ha => IH x1 x2 xi y1 H' Ha Hb (proj2 Hsort) Hstep') => {IH} IH.
  replace (Riemann_sum (SF_fun f 0) _ _ _)
    with ((SF_fun f 0 y0) * (x1-x0) + Riemann_sum (SF_fun f 0) _ _ H').
  rewrite {1}/SF_fun /=.
  case: (Rle_lt_dec x1 a0) => Hy.
  have Hy': (y0 <= a0).
    apply Rle_trans with (2 := Hy).
    apply (proj2 H O (lt_O_Sn _)).
  apply Rle_lt_or_eq_dec in Hy' ; case: Hy' => Hy'.
  case Rlt_dec => // _.
  rewrite Rmult_0_l Rplus_0_l ; apply IH => //.
  have : (x1 = a0).
    apply Rle_antisym => //.
    rewrite -Hy' ; apply (proj2 H O (lt_O_Sn _)).
  move => {Hy IH} Hy.
  rewrite Hy' in H |- * => {y0 Hy'}.
  rewrite Hy in H, H', Hb, Hsort, Hstep, Hstep' |- * => {x1 Hy}.
  move: (Rlt_irrefl a0) ; case: Rlt_dec => // _ _.
  case: Rle_dec => // _.
  replace (pos eps) with (Rabs f0 * alpha + Rabs f0 * alpha) ;
  [ | simpl ; field ; by apply Rabs_no_R0].
  rewrite Rplus_comm /Rminus Ropp_plus_distr -Rplus_assoc.
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  clear H Hstep Ha.
  simpl in Hb.
  have : sorted Rlt [:: a0, x2 & sigma].
    apply Hsort.
  move => {Hsort x0} Hsort'.
  elim: sigma x2 xi y1 H' Hb Hstep' Hsort' => [ | x2 sigma IH] x1 ;
  case => [ | y1 xi] y0 H Hb Hstep Hsort ; try by case H.
  rewrite /Riemann_sum /RInt_seq /SF_fun ; simpl Rabs.
  rewrite ?Rplus_0_r.
  have: ~ (y0 < a0).
    apply Rle_not_lt, (proj2 H O (lt_O_Sn _)).
  case: Rlt_dec => // _ _.
  
Admitted.
Lemma ex_RInt_correct_aux_2 (f : R -> R) (a b : R) :
  (exists I : R, forall eps : posreal, exists alpha : nat, forall (sigma xi : seq R) 
  (H : pointed_subdiv a b sigma xi), (size sigma <= alpha)%nat ->
  Rabs (I - Riemann_sum f a b sigma xi H) <= eps) -> ex_RInt f a b.
Proof.
Admitted.
Lemma ex_RInt_correct_aux_3 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
Admitted.

(** * my proof *)

Lemma ex_RInt_correct_0 (f : R -> R) (a b : R) : ex_RInt f a b -> 
  forall n x, Rmin a b <= x <= Rmax a b -> 
    Rabs (f x - sf_SF_val_fun f a b n x) <= SF_psi_r f a b n x.
Proof.
  wlog: a b / (a <= b) => [Hw Hex n x | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm ;
    replace ((sf_SF_val_fun f a b n) x) with ((sf_SF_val_fun f b a n) x) ;
    [ | rewrite /sf_SF_val_fun ; case: Rle_dec ; case: Rle_dec => //= ; 
    [ move => H1 H2 ; by rewrite (Rle_antisym _ _ H1 H2) 
    | move => H1 H2 ; contradict H2 ; by apply Rlt_le]] ;
    replace ((SF_psi_r f a b n) x) with ((SF_psi_r f b a n) x) ;
    [ | rewrite /SF_psi_r ; case: Rle_dec ; case: Rle_dec => /= ; 
    rewrite SF_sup_fun_bound SF_inf_fun_bound => //= ].
    apply Hw ; [by apply Rlt_le | by apply ex_RInt_bound].
  rewrite /Rmin /Rmax /sf_SF_val_fun /SF_psi_r ; 
  case: Rle_dec => //= _ ; case => Hlim Hfin n x Hx.

  have Hsup : (exists M, forall x, Rmin a b <= x <= Rmax a b -> f x <= M).
    suff : (exists n, Finite (real (RInt_sup f a b n)) = (RInt_sup f a b n)).
      case => n0 Hn0.
      case: (RInt_sup_real_0 _ _ _ _ Hn0) => M Hm.
      exists M => x0 Hx0 ; by apply Hm.
    move: Hfin ; rewrite /Rbar_inf_seq ; case: (Rbar_ex_inf_seq _) ; 
    case => [l | | ] // Hfin ; 
    case: (Hfin (mkposreal _ Rlt_0_1)) => /= _ [n0 Hn0] _ ;
    exists n0.
    move: (RInt_sup_infty f a b n0) Hn0 ; case: (RInt_sup _ _ _ _) => //.
    
  have Hinf : (exists m, forall x, Rmin a b <= x <= Rmax a b -> m <= f x).
    suff : (exists n, Finite (real (RInt_inf f a b n)) = (RInt_inf f a b n)).
      case => n0 Hn0.
      case: (RInt_inf_real_0 _ _ _ _ Hn0) => M Hm.
      exists M => x0 Hx0 ; by apply Hm.
    move: Hfin ; rewrite Hlim /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) ; 
    case => [l | | ] // Hfin ; 
    case: (Hfin (mkposreal _ Rlt_0_1)) => /= _ [n0 Hn0] _ ;
    exists n0.
    move: (RInt_inf_infty f a b n0) Hn0 ; case: (RInt_inf _ _ _ _) => //.

  have Hsup_fin : (forall i, ( (S i) < size (RInt_part a b n))%nat ->
    Finite (real (Sup_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))) = (Sup_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))).
    case: Hsup => M Hsup ; move: (SF_sup_real_1 f a b n M Hsup) => {Hsup} Hsup.
    apply SF_ly_surj in Hsup ; rewrite SF_map_ly SF_ly_f2 in Hsup.
    move => i Hi ; 
    replace (nth 0 _ i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition ;
    rewrite -(nth_pairmap _ (Finite 0) (Sup_fct f)) ; [| apply SSR_leq ; intuition].
    rewrite -nth_behead -(nth_map _ (Finite 0) (fun x => Finite (real x))).
    by rewrite Hsup.
    apply SSR_leq ; rewrite size_behead size_pairmap ; intuition.
    
  have Hinf_fin : (forall i, ((S i) < size (RInt_part a b n))%nat ->
    Finite (real (Inf_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))) = (Inf_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))).
    case: Hinf => M Hinf ; move: (SF_inf_real_1 f a b n M Hinf) => {Hinf} Hinf.
    apply SF_ly_surj in Hinf ; rewrite SF_map_ly SF_ly_f2 in Hinf.
    move => i Hi ; 
    replace (nth 0 _ i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition ;
    rewrite -(nth_pairmap _ (Finite 0) (Inf_fct f)) ; [| apply SSR_leq ; intuition].
    rewrite -nth_behead -(nth_map _ (Finite 0) (fun x => Finite (real x))).
    by rewrite Hinf.
    apply SSR_leq ; rewrite size_behead size_pairmap ; intuition.

  rewrite SF_val_fun_rw SF_sup_fun_rw SF_inf_fun_rw ;
  case: RInt_part_nat => {Hx} [ [i [Hx Hi]] | Hx] ; simpl projT1 ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ; 
  apply Rplus_le_compat ; try apply Ropp_le_contravar ; apply Rbar_finite_le.
  
  have Hi' : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite Hinf_fin /Inf_fct /Glb_Rbar_ne ; [ | intuition] ; 
  case: (ex_glb_Rbar_ne _ (ex_Im_fct _ _ _)) => l [ub lub] /= ; apply ub ;
  exists x ; split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // ; intuition.
  
  have Hi' : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite Hsup_fin /Sup_fct /Lub_Rbar_ne ; [ | intuition] ; 
  case: (ex_lub_Rbar_ne _ _) => l [ub lub] /= ; apply ub ;
  exists (a + (2 * INR i + 1) * (b - a) / 2 ^ S n) ; 
  split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // _.
  rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR /= ; 
  [ | apply SSR_leq | apply SSR_leq] ; intuition.
  replace (a + (2 * INR i + 1) * (b - a) / (2 * 2 ^ n)) with 
  (a + INR i * (b - a) / 2 ^ n + (b-a)/2^(S n)).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  simpl ; field ; apply Rgt_not_eq ; intuition.
  replace (a + (INR i + 1) * (b - a) / (2 ^ n)) with 
  (a + (2*INR i+1) * (b - a) / (2*2 ^ n) + (b-a)/(2^(S n))).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  simpl ; field ; apply Rgt_not_eq ; intuition.
  
  have Hi' : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite Hsup_fin /Sup_fct /Lub_Rbar_ne ; [ | intuition] ; 
  case: (ex_lub_Rbar_ne _ _) => l [ub lub] /= ; apply ub ;
  exists x ; split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // ; intuition.
  
  have Hi' : (nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i)) ;
    [apply Rlt_le, Rle_lt_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite Hinf_fin /Inf_fct /Glb_Rbar_ne ; [ | intuition] ; 
  case: (ex_glb_Rbar_ne _ _) => l [ub lub] /= ; apply ub ;
  exists (a + (2 * INR i + 1) * (b - a) / 2 ^ S n) ; 
  split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // _.
  rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR /= ; 
  [ | apply SSR_leq | apply SSR_leq] ; intuition.
  replace (a + (2 * INR i + 1) * (b - a) / (2 * 2 ^ n)) with 
  (a + INR i * (b - a) / 2 ^ n + (b-a)/2^(S n)).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  simpl ; field ; apply Rgt_not_eq ; intuition.
  replace (a + (INR i + 1) * (b - a) / (2 ^ n)) with 
  (a + (2*INR i+1) * (b - a) / (2*2 ^ n) + (b-a)/(2^(S n))).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  simpl ; field ; apply Rgt_not_eq ; intuition.
  
  have Rw : (pow2 n = S (pow2 n - 1))%nat ;
   [rewrite -pred_of_minus -(S_pred _ O) // ; apply INR_lt ; rewrite pow2_INR /= ; 
   intuition | rewrite {2 4}Rw in Hx |- * ] ;
  have Hi' : (nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (S (pow2 n-1))) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite (Hinf_fin (pow2 n - 1)%nat) /Inf_fct /Glb_Rbar_ne.
  case: (ex_glb_Rbar_ne _ (ex_Im_fct _ _ _)) => l [ub lub] /= ; apply ub ;
  exists x ; split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // ; intuition.
  rewrite -Rw size_mkseq ; apply lt_n_Sn.
  
  have Rw : (pow2 n = S (pow2 n - 1))%nat ;
   [rewrite -pred_of_minus -(S_pred _ O) // ; apply INR_lt ; rewrite pow2_INR /= ; 
   intuition | rewrite {2 4}Rw in Hx |- * ] ;
  have Hi' : (nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (S (pow2 n-1))) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite (Hsup_fin (pow2 n - 1)%nat) /Sup_fct /Lub_Rbar_ne.
  case: (ex_lub_Rbar_ne _ (ex_Im_fct _ _ _)) => l [ub lub] /= ; apply ub ;
  exists (a + (2^(S n) - 1) * (b - a) / 2 ^ S n) ; 
  split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // _.
  rewrite ?nth_mkseq ?S_INR /= ; 
  [ | apply SSR_leq | apply SSR_leq] ; intuition.
  replace (a + (2*2^n-1) * (b - a) / (2 * 2 ^ n)) with 
  (a + INR (pow2 n - 1) * (b - a) / 2 ^ n + (b-a)/2^(S n)).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  rewrite minus_INR.
  rewrite pow2_INR /= ; field ; apply Rgt_not_eq ; intuition.
  apply lt_n_Sm_le, lt_n_S, INR_lt ; rewrite pow2_INR /= ; intuition.
  replace (a + (INR (pow2 n - 1) + 1) * (b - a) / (2 ^ n)) with 
  (a + (2*2^n-1) * (b - a) / (2*2 ^ n) + (b-a)/(2^(S n))).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  rewrite minus_INR.
  rewrite pow2_INR /= ; field ; apply Rgt_not_eq ; intuition.
  apply lt_n_Sm_le, lt_n_S, INR_lt ; rewrite pow2_INR /= ; intuition.
  rewrite size_mkseq -Rw ; intuition.
  
  have Rw : (pow2 n = S (pow2 n - 1))%nat ;
   [rewrite -pred_of_minus -(S_pred _ O) // ; apply INR_lt ; rewrite pow2_INR /= ; 
   intuition | rewrite {2 4}Rw in Hx |- * ] ;
  have Hi' : (nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (S (pow2 n-1))) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite (Hsup_fin (pow2 n - 1)%nat) /Sup_fct /Lub_Rbar_ne.
  case: (ex_lub_Rbar_ne _ (ex_Im_fct _ _ _)) => l [ub lub] /= ; apply ub ;
  exists x ; split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // ; intuition.
  rewrite -Rw size_mkseq ; apply lt_n_Sn.
  
  have Rw : (pow2 n = S (pow2 n - 1))%nat ;
   [rewrite -pred_of_minus -(S_pred _ O) // ; apply INR_lt ; rewrite pow2_INR /= ; 
   intuition | rewrite {2 4}Rw in Hx |- * ] ;
  have Hi' : (nth 0 (RInt_part a b n) (pow2 n - 1) <= nth 0 (RInt_part a b n) (S (pow2 n-1))) ;
    [apply Rle_trans with (1 := proj1 Hx), Hx | ] ;
  rewrite (Hinf_fin (pow2 n - 1)%nat) /Inf_fct /Glb_Rbar_ne.
  case: (ex_glb_Rbar_ne _ (ex_Im_fct _ _ _)) => l [ub lub] /= ; apply ub ;
  exists (a + (2^(S n) - 1) * (b - a) / 2 ^ S n) ; 
  split => // ; rewrite /Rmin /Rmax ; case: Rle_dec => // _.
  rewrite ?nth_mkseq ?S_INR /= ; 
  [ | apply SSR_leq | apply SSR_leq] ; intuition.
  replace (a + (2*2^n-1) * (b - a) / (2 * 2 ^ n)) with 
  (a + INR (pow2 n - 1) * (b - a) / 2 ^ n + (b-a)/2^(S n)).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  rewrite minus_INR.
  rewrite pow2_INR /= ; field ; apply Rgt_not_eq ; intuition.
  apply lt_n_Sm_le, lt_n_S, INR_lt ; rewrite pow2_INR /= ; intuition.
  replace (a + (INR (pow2 n - 1) + 1) * (b - a) / (2 ^ n)) with 
  (a + (2*2^n-1) * (b - a) / (2*2 ^ n) + (b-a)/(2^(S n))).
  rewrite (Rplus_comm _ ((b-a)/2^_)) ; apply (Rle_minus2 _ _) ; 
  field_simplify ; try apply Rgt_not_eq ; intuition.
  rewrite {1}/Rdiv Rmult_0_l Rplus_comm ; apply Rdiv_le_pos ; intuition ;
  by apply (Rminus_le_0 a b).
  rewrite minus_INR.
  rewrite pow2_INR /= ; field ; apply Rgt_not_eq ; intuition.
  apply lt_n_Sm_le, lt_n_S, INR_lt ; rewrite pow2_INR /= ; intuition.
  rewrite size_mkseq -Rw ; intuition.
Qed.

Lemma ex_RInt_correct_1 (f : R -> R) (a b : R) (eps : posreal) : ex_RInt f a b -> 
  {n : nat | Rabs (RiemannInt_SF (SF_psi_r f a b n)) < eps}.
Proof.
  move => Hex ; apply ConstructiveEpsilon.constructive_indefinite_description_nat ; [move => n ; apply Rlt_dec | ].
  have Hsup : (forall a b, ex_RInt f a b ->
    exists M, forall x, Rmin a b <= x <= Rmax a b -> f x <= M).
    move => {a b Hex} a b Hex ;
    suff : (exists n, Finite (real (RInt_sup f a b n)) = (RInt_sup f a b n)).
      case => n0 Hn0.
      case: (RInt_sup_real_0 _ _ _ _ Hn0) => M Hm.
      exists M => x0 Hx0 ; by apply Hm.
    move: (proj2 Hex) ; rewrite /Rbar_inf_seq ; case: (Rbar_ex_inf_seq _) ; 
    case => [l | | ] // Hfin ; 
    case: (Hfin (mkposreal _ Rlt_0_1)) => /= _ [n0 Hn0] _ ;
    exists n0.
    move: (RInt_sup_infty f a b n0) Hn0 ; case: (RInt_sup _ _ _ _) => //.
    
  have Hinf : (forall a b, ex_RInt f a b ->
    exists m, forall x, Rmin a b <= x <= Rmax a b -> m <= f x).
    move => {a b Hex} a b Hex ;
    suff : (exists n, Finite (real (RInt_inf f a b n)) = (RInt_inf f a b n)).
      case => n0 Hn0.
      case: (RInt_inf_real_0 _ _ _ _ Hn0) => M Hm.
      exists M => x0 Hx0 ; by apply Hm.
    move: (proj2 Hex) ; rewrite (proj1 Hex) /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) ; 
    case => [l | | ] // Hfin ; 
    case: (Hfin (mkposreal _ Rlt_0_1)) => /= _ [n0 Hn0] _ ;
    exists n0.
    move: (RInt_inf_infty f a b n0) Hn0 ; case: (RInt_inf _ _ _ _) => //.

  have Hsup_fin : (forall a b, ex_RInt f a b ->
    forall n i, ( (S i) < size (RInt_part a b n))%nat ->
    Finite (real (Sup_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))) = (Sup_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))).
    move => {a b Hex} a b Hex ;
    case: (Hsup a b Hex) => {Hsup} M Hsup n ; 
    move: (SF_sup_real_1 f a b n M Hsup) => {Hsup} Hsup.
    apply SF_ly_surj in Hsup ; rewrite SF_map_ly SF_ly_f2 in Hsup.
    move => i Hi ; 
    replace (nth 0 _ i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition ;
    rewrite -(nth_pairmap _ (Finite 0) (Sup_fct f)) ; [| apply SSR_leq ; intuition].
    rewrite -nth_behead -(nth_map _ (Finite 0) (fun x => Finite (real x))).
    by rewrite Hsup.
    apply SSR_leq ; rewrite size_behead size_pairmap ; intuition.
    
  have Hinf_fin : (forall a b, ex_RInt f a b ->
    forall n i, ((S i) < size (RInt_part a b n))%nat ->
    Finite (real (Inf_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))) = (Inf_fct f (nth 0 (RInt_part a b n) i)
    (nth 0 (RInt_part a b n) (S i)))).
    move => {a b Hex} a b Hex ;
    case: (Hinf a b Hex) => {Hinf} M Hinf n ; 
    move: (SF_inf_real_1 f a b n M Hinf) => {Hinf} Hinf.
    apply SF_ly_surj in Hinf ; rewrite SF_map_ly SF_ly_f2 in Hinf.
    move => i Hi ; 
    replace (nth 0 _ i) with (nth 0 (0::RInt_part a b n) (S i)) by intuition ;
    rewrite -(nth_pairmap _ (Finite 0) (Inf_fct f)) ; [| apply SSR_leq ; intuition].
    rewrite -nth_behead -(nth_map _ (Finite 0) (fun x => Finite (real x))).
    by rewrite Hinf.
    apply SSR_leq ; rewrite size_behead size_pairmap ; intuition.
  
  wlog: a b Hex / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    apply Rle_lt_or_eq_dec in Hab ; case: Hab => Hab.
    by apply Hw.
    exists O ; rewrite Hab /RiemannInt_SF SF_psi_subdiv SF_psi_subdiv_val ; 
    case: Rle_dec (Rle_refl b) => //= _ _.
    replace ((real (Sup_fct f (b + 0 * (b - b) / 1) (b + 1 * (b - b) / 1)) -
      real (Inf_fct f (b + 0 * (b - b) / 1) (b + 1 * (b - b) / 1))) *
      (b + 1 * (b - b) / 1 - (b + 0 * (b - b) / 1)) + 0) with 0 by field.
    rewrite Rabs_R0 ; apply eps.
    apply ex_RInt_bound in Hex ; case: (Hw _ _ Hex Hab) => n Hn ;
    exists n ; move: Hn ; rewrite /RiemannInt_SF ?SF_psi_subdiv ?SF_psi_subdiv_val; 
    move: (Rlt_le _ _ Hab) ; move: (Rlt_not_le _ _ Hab) ;
    case: Rle_dec ; case: Rle_dec => // ; intros ; by rewrite Rabs_Ropp.
    
  case: (Hsup a b Hex) => {Hsup} M Hsup ;
  case: (Hinf a b Hex) => {Hinf} m Hinf ;
  case: (Hex).
  rewrite /Rbar_inf_seq /Rbar_sup_seq ; 
  case: Rbar_ex_inf_seq ; case => [li | | ] Hli // ;
  case: Rbar_ex_sup_seq ; case => [ls | | ] Hls //= Heq _ ;
  apply Rbar_finite_eq in Heq ; rewrite Heq in Hli => {Heq}.
  
  have He : (0 < eps / (2*(b-a))).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    apply Rlt_Rminus, Hab.
  set e := mkposreal _ He ;
  case: (Hli e) => {Hli} _ [ni Hli] ;
  case: (Hls e) => {Hls} _ [ns Hls].
  exists (ni+ns)%nat.

  replace (RiemannInt_SF _) 
    with ((b-a)*(real (RInt_sup f a b (ni+ns)) - real (RInt_inf f a b (ni+ns)))).
  replace (pos eps) with ((b-a)*((ls + e) - (ls - e))).
  rewrite Rabs_mult Rabs_pos_eq.
  apply Rmult_lt_compat_l.
  apply Rlt_Rminus, Hab.
  rewrite Rabs_pos_eq.
  apply Rplus_lt_compat, Ropp_lt_contravar.
  apply Rbar_le_lt_trans with (2 := Hli)
    (x := Finite (real (RInt_sup f a b (ni + ns)))) 
    (y := (RInt_sup f a b ni))
    (z := Finite (ls + e)).
  rewrite (RInt_sup_real_1 _ _ _ _ M Hsup).
  apply RInt_sup_decr ; intuition.
  apply Rbar_lt_le_trans with (1 := Hls)
    (z := Finite (real (RInt_inf f a b (ni + ns)))) 
    (y := (RInt_inf f a b ns))
    (x := Finite (ls - e)).
  rewrite (RInt_inf_real_1 _ _ _ _ m Hinf).
  apply RInt_inf_incr ; intuition.
  apply (Rminus_le_0 (real _)), Rbar_finite_le.
  rewrite (RInt_sup_real_1 _ _ _ _ M Hsup) (RInt_inf_real_1 _ _ _ _ m Hinf) ;
  apply RInt_inf_le_sup.
  
  apply Rlt_le, Rlt_Rminus, Hab.

  simpl ; field ; apply Rgt_not_eq, Rlt_Rminus, Hab.
  
  rewrite /RInt_sup /RInt_inf /RiemannInt_SF ; 
  rewrite SF_psi_subdiv SF_psi_subdiv_val SF_sup_ly SF_inf_ly ;
  move: (Rlt_le _ _ Hab) ;
  case: Rle_dec => // _ _.
  have: (forall i, (S i < size (RInt_part a b (ni + ns)))%nat -> 
    nth 0 (RInt_part a b (ni + ns)) (S i) 
    - nth 0 (RInt_part a b (ni + ns)) i = (b-a)/2^(ni + ns)).
    move => i Hi ; rewrite size_mkseq in Hi ; rewrite ?nth_mkseq.
    rewrite S_INR ; field ; apply Rgt_not_eq ; intuition.
    apply SSR_leq ; intuition.
    apply SSR_leq ; intuition.
  case: (RInt_part a b (ni + ns)) (Hsup_fin a b Hex (ni+ns)%nat) 
  (Hinf_fin a b Hex (ni+ns)%nat) => [ | h s].
  simpl => Hval Hsup_fin' Hinf_fin' ; field ; apply Rgt_not_eq ; intuition.
  elim: s h => [| h0 s IH] h {Hsup_fin Hinf_fin} Hsup_fin Hinf_fin Hval.
  simpl ; field ; apply Rgt_not_eq ; intuition.
  simpl ; rewrite -IH. 
  rewrite (Hval O).
  replace (behead (pairmap (Sup_fct f) 0 (h0 :: s))) 
    with (pairmap (Sup_fct f) h0 s).
  replace (behead (pairmap (Inf_fct f) 0 (h0 :: s))) 
    with (pairmap (Inf_fct f) h0 s).

  have: Finite (real (Sup_fct f h h0)) = (Sup_fct f h h0).
    apply (Hsup_fin O), lt_n_S, lt_O_Sn.
  have: Finite (real (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s)))
    = (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s)).
    elim: s h h0 Hsup_fin {Hinf_fin Hval IH} => [|h1 s IH] h h0 Hsup_fin //=.
    have H : forall i, (S i < size [:: h0, h1 & s])%nat ->
      Finite (real (Sup_fct f (nth 0 [:: h0, h1 & s] i) (nth 0 [:: h0, h1 & s] (S i)))) =
      Sup_fct f (nth 0 [:: h0, h1 & s] i) (nth 0 [:: h0, h1 & s] (S i)).
      move => i Hi ; apply (Hsup_fin (S i)), lt_n_S, Hi.
    move: (Hsup_fin 1%nat (lt_n_S _ _ (lt_n_S _ _ (lt_O_Sn _)))) (IH h0 h1 H) => /=.
    case: (Sup_fct f h0 h1) => // ;
    case: (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h1 s)) => //.
  have: Finite (real (Inf_fct f h h0)) = (Inf_fct f h h0).
    apply (Hinf_fin O), lt_n_S, lt_O_Sn.
  have: Finite (real (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s)))
    = (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s)).
    elim: s h h0 Hinf_fin {Hsup_fin Hval IH} => [|h1 s IH] h h0 Hinf_fin //=.
    have H : forall i, (S i < size [:: h0, h1 & s])%nat ->
      Finite (real (Inf_fct f (nth 0 [:: h0, h1 & s] i) (nth 0 [:: h0, h1 & s] (S i)))) =
      Inf_fct f (nth 0 [:: h0, h1 & s] i) (nth 0 [:: h0, h1 & s] (S i)).
      move => i Hi ; apply (Hinf_fin (S i)), lt_n_S, Hi.
    move: (Hinf_fin 1%nat (lt_n_S _ _ (lt_n_S _ _ (lt_O_Sn _)))) (IH h0 h1 H) => /=.
    case: (Inf_fct f h0 h1) => // ;
    case: (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h1 s)) => //.

  case: (Sup_fct f h h0) => [s1 | | ] // ;
  case: (Inf_fct f h h0) => [i1 | | ] // ;
  case: (foldr Rbar_plus (Finite 0) (pairmap (Sup_fct f) h0 s)) => [s2 | | ] // ;
  case: (foldr Rbar_plus (Finite 0) (pairmap (Inf_fct f) h0 s)) => [i2 | | ] //= _ _ _ _.
  field ; apply Rgt_not_eq ; intuition.
  case s => //.
  case s => //.
  apply lt_n_S, lt_O_Sn.
  move => i Hi ; apply (Hsup_fin (S i)), lt_n_S, Hi.
  move => i Hi ; apply (Hinf_fin (S i)), lt_n_S, Hi.
  move => i Hi ; apply (Hval (S i)), lt_n_S, Hi.
Qed.

Lemma ex_RInt_correct_2 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
  move => Hri eps.
  case: (ex_RInt_correct_1 f a b eps Hri) => n Hn.
  exists (sf_SF_val_fun f a b n) ; exists (SF_psi_r f a b n) ; split => // ;
  apply ex_RInt_correct_0, Hri.
Defined.


Fixpoint insert_pos (l : Rlist) (x : R) (n : nat) :=
  match n with
    | O => RList.cons x l
    | S n => match l with
        | RList.nil => RList.cons x RList.nil
        | RList.cons h l => RList.cons h (insert_pos l x n)
      end
  end.

Lemma Rlength_insert_pos (l : Rlist) (x : R) (n : nat) :
  Rlength (insert_pos l x n) = S (Rlength l).
Proof.
  elim: n l => [| n IH] l.
  elim: l => [|h l IH] //.
  case : l => [| h l] //=.
  by rewrite IH.
Qed.

Fixpoint Rlist_cut_up (l : Rlist) (x : R) :=
  match l with
    | RList.nil => RList.nil
    | RList.cons h l => 
        match (Rle_dec x h) with
          | left _ => RList.cons h l
          | right _ => Rlist_cut_up l x
        end
  end.

Fixpoint Rlist_cut_down (l : Rlist) (x : R) :=
  match l with
    | RList.nil => RList.nil
    | RList.cons h l => 
        match (Rle_dec x h) with
          | left _ => RList.nil
          | right _ => RList.cons h (Rlist_cut_down l x)
        end
  end.

Lemma Rlist_cut (l : Rlist) (x : R) : ordered_Rlist l ->
  cons_Rlist (Rlist_cut_down l x) (Rlist_cut_up l x) = l.
Proof.
  elim: l => [ | h s IH] Hsort //=.
  case: Rle_dec => //= Hx.
  rewrite IH //.
  move => i Hi ; apply (Hsort (S i)) => /= ; intuition.
Qed.

Lemma sorted2_dec (s s0 : seq R) : sorted Rle s -> sorted Rle s0 ->
  (forall i0, (i0 < size s)%nat -> head 0 s0 <= nth 0 s i0 <= last 0 s0) ->
  (1 < size s0)%nat ->
  forall i, (S i < size s)%nat 
    -> {j : nat | nth 0 s0 j < nth 0 s i /\ nth 0 s (S i) < nth 0 s0 (S j) /\ (S j < size s0)%nat}
      + {j : nat | nth 0 s i <= nth 0 s0 j <= nth 0 s (S i) /\ (j < size s0)%nat}.
Proof.
  move => Hs Hs0 Hhl Hls0 i Hi.
  case: (sorted_dec s0 0 (nth 0 s i) Hs0 (Hhl i (lt_trans _ _ _ (lt_n_Sn _) Hi))) 
    => [[j [Hij Hj]] | Hij ] ;
  case: (sorted_dec s0 0 (nth 0 s (S i)) Hs0 (Hhl (S i) Hi)) 
    => [[j' [Hij' Hj']] | Hij' ].
  case: (le_lt_dec j j') => Hjj'.
  apply le_lt_eq_dec in Hjj' ; case: Hjj' => Hjj'.
  have H : (nth 0 s0 (S j) <= nth 0 s0 j').
  apply sorted_incr ; intuition.
  apply Rle_lt_or_eq_dec in H ; case: H => H.
  right ; exists j' ; intuition.
  apply Rlt_le, Rlt_trans with (1 := H1), H.
  rewrite -H in Hij' => {H}.
  right ; exists (S j) ; intuition.
  rewrite -Hjj' in Hij', Hj' => {j' Hjj'}.
  case: Hij => Hij _ ; apply Rle_lt_or_eq_dec in Hij ; case: Hij => Hij.
  left ; exists j ; intuition.
  right ; exists j ; rewrite Hij ; intuition.
  apply (sorted_nth Rle) ; intuition.
  absurd (nth 0 s0 j < nth 0 s0 (S j')).
  apply Rle_not_lt ; apply sorted_incr ; intuition.
  apply Rle_lt_trans with (1 := proj1 Hij), 
  Rle_lt_trans with (2 := proj2 Hij').
  apply (sorted_nth Rle) ; intuition.

  case: Hij' => Hij' Hij0.
  apply Rle_lt_or_eq_dec in Hij0 ; case: Hij0 => Hij0.
  have H : (nth 0 s0 (S j) <= nth 0 s0 (size s0 - 2)).
  apply sorted_incr ; intuition.
  apply Rle_lt_or_eq_dec in H ; case: H => H.
  right ; exists (size s0 - 2)%nat ; intuition.
  apply Rlt_le, Rlt_trans with (1 := H1), H.
  rewrite -H in Hij' => {H}.
  right ; exists (S j) ; intuition.
  right ; exists (size s0 - 1)%nat ; intuition.
  apply Rlt_le, Rlt_le_trans with (1 := H0), sorted_incr ; intuition.
  
  absurd (nth 0 s0 (size s0 - 2) < nth 0 s0 (S j')).
  apply Rle_not_lt, sorted_incr ; intuition.
  apply Rle_lt_trans with (1 := proj1 Hij),
  Rle_lt_trans with (2 := proj2 Hij'), sorted_incr ; intuition.

  case: (Rle_lt_or_eq_dec _ _ (proj1 Hij)) => {Hij} Hij.
  case: (Rle_lt_or_eq_dec _ _ (proj2 Hij')) => {Hij'} Hij'.
  left ; exists (size s0 - 2)%nat ; intuition.
  apply Rlt_le_trans with (1 := Hij'), Req_le.
  case: (s0) Hls0 => //= t ; case => //= t0 ;
  [by apply lt_irrefl in t0 | by case ].
  right ; exists (size s0 - 1)%nat ; intuition ; rewrite -Hij' ;
  apply sorted_incr ; intuition.
  right ; exists (size s0 - 2)%nat ; intuition ; rewrite Hij ;
  apply sorted_incr ; intuition.
Qed.

Lemma RInt_sup_down f a b n (Hab : a < b) :
  forall s : StepFun a b, forall M,
  (forall t, a <= t <= b -> s t <= f t) ->
  (forall t, a <= t <= b -> f t <= M) ->
    Rbar_le (Finite (RiemannInt_SF s)) 
      (Rbar_mult_pos (RInt_sup f a b n) (mkposreal (b-a) (Rlt_Rminus _ _ Hab))).
Proof.
  move => s M Hsf HfM.
  apply Rbar_le_trans with (Finite (RiemannInt_SF (SF_sup_r f a b n))).
  apply Rbar_finite_le.
  apply StepFun_P37 ; [ by apply Rlt_le | ].
  move => x Hx ; apply Rle_trans with (f x).
  apply: Hsf ; intuition.
  rewrite /SF_sup_r ; move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  apply Rbar_finite_le, Rbar_le_trans with (SF_sup_fun f a b n x).
  apply SF_sup_ge_f ; rewrite /Rmin /Rmax ; 
  move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _ ; intuition.
  rewrite SF_sup_fun_rw.
  intuition.
  move => H ; case: RInt_part_nat => {Hx} // [[i [Hx Hi]] | Hx] ; simpl projT1.
  right ; rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; simpl projT1 ;
  case => // [ [_ lub] | [ub _]].
  absurd (Rbar_le p_infty (Finite M)).
  by apply Rbar_lt_not_le.
  apply lub => {lub x H Hx} _ [x [-> lub]].
  apply Rbar_finite_le, HfM.
  split ; 
  [apply Rle_trans with (2 := proj1 lub) 
  | apply Rle_trans with (1 := proj2 lub)].
  apply Rmin_case_strong => _ ; rewrite size_mkseq in Hi ; 
  rewrite nth_mkseq ; try apply SSR_leq ; intuition  ;
  apply (Rminus_le_0 a) ; ring_simplify ; apply Rdiv_le_pos ; 
  intuition ; apply Rmult_le_pos ; try apply pos_INR ; 
  apply (Rminus_le_0 a) ; intuition.
  apply Rmax_case_strong => _ ; rewrite size_mkseq in Hi ; 
  rewrite nth_mkseq ; try apply SSR_leq ; intuition  ;
  apply (Rminus_le_0 _ b).
  replace (_-_) with ((b-a) * (1 - INR i/2^n)) ; 
  [ | field_simplify ; [ | apply Rgt_not_eq | apply Rgt_not_eq ] ; intuition].
  apply Rmult_le_pos ; [apply -> Rminus_le_0 ; by apply Rlt_le |] ;
  apply -> Rminus_le_0 ; apply -> Rdiv_le_1 ; intuition ; 
  rewrite -pow2_INR ; apply le_INR ; intuition.
  replace (_-_) with ((b-a) * (1 - INR (S i)/2^n)) ; 
  [ | field_simplify ; [ | apply Rgt_not_eq | apply Rgt_not_eq ] ; intuition].
  apply Rmult_le_pos ; [apply -> Rminus_le_0 ; by apply Rlt_le |] ;
  apply -> Rminus_le_0 ; apply -> Rdiv_le_1 ; intuition ; 
  rewrite -pow2_INR ; apply le_INR ; intuition.
  absurd (Rbar_le (Finite (f (nth 0 (RInt_part a b n) i))) m_infty).
   by apply Rbar_lt_not_le.
   apply ub ; exists (nth 0 (RInt_part a b n) i) ; split => // ;
   apply Rmin_Rmax_l.
  right ; rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; simpl projT1 ;
  case => // [ [_ lub] | [ub _]].
  absurd (Rbar_le p_infty (Finite M)).
  by apply Rbar_lt_not_le.
  apply lub => {lub x H Hx} _ [x [-> lub]].
  apply Rbar_finite_le, HfM.
  split ; 
  [apply Rle_trans with (2 := proj1 lub) 
  | apply Rle_trans with (1 := proj2 lub)].
  apply Rmin_case_strong => _ ; 
  rewrite nth_mkseq ; try apply SSR_leq ; intuition  ;
  apply (Rminus_le_0 a) ; ring_simplify ; apply Rdiv_le_pos ; 
  intuition ; apply Rmult_le_pos ; try apply pos_INR ; 
  apply (Rminus_le_0 a) ; intuition.
  apply Rmax_case_strong => _ ; 
  rewrite nth_mkseq ; try apply SSR_leq ; intuition  ;
  apply (Rminus_le_0 _ b).
  replace (_-_) with ((b-a) * (1 - INR (pow2 n - 1)/2^n)) ; 
  [ | field_simplify ; [ | apply Rgt_not_eq | apply Rgt_not_eq ] ; intuition].
  apply Rmult_le_pos ; [apply -> Rminus_le_0 ; by apply Rlt_le |] ;
  apply -> Rminus_le_0 ; apply -> Rdiv_le_1 ; intuition ; 
  rewrite -pow2_INR ; apply le_INR ; intuition.
  apply Req_le ; rewrite pow2_INR ; field ; apply Rgt_not_eq ; intuition.
  absurd (Rbar_le (Finite (f (nth 0 (RInt_part a b n) (pow2 n)))) m_infty).
   by apply Rbar_lt_not_le.
   apply ub ; exists (nth 0 (RInt_part a b n) (pow2 n)) ; split => // ;
   apply Rmin_Rmax_r.
  right.
  rewrite (RInt_sup_compat f a b n M) ;
  [rewrite -(RInt_sup_real_1 f a b n M) /= 1?Rmult_comm // | ] ; 
  move: (Rlt_le _ _ Hab) ; rewrite /Rmin /Rmax ; case: Rle_dec => //.
Qed.

Lemma sorted_cons_ORlist (s s' : Rlist) :
  (ordered_Rlist s) -> (ordered_Rlist s') ->
     cons_ORlist s s' =
       match s with
         | RList.nil => s'
         | RList.cons h t =>
             match s' with
               | RList.nil => s
               | RList.cons h' t' =>
                   match Rle_dec h' h with
                     | left _ => RList.cons h' (cons_ORlist s t')
                     | right _ => RList.cons h (cons_ORlist t s')
                   end
            end
        end.
Proof.
  have H : (forall s s', ordered_Rlist s -> ordered_Rlist s' ->
    ((0 < Rlength s)%nat -> pos_Rl s' (Peano.pred (Rlength s')) <= pos_Rl s O) ->
    cons_ORlist s s' = cons_Rlist s' s).
    move => {s s'} s s' ; elim: s s' => [ | h s IH] s' Hs Hs' Hpos //=.
    elim: s' {Hs' Hpos} => [ | h' s' IH] //=.
    by rewrite -IH.
    case: s' Hs' Hpos => [ | h' s'] Hs' Hpos.
    apply IH => //.
    apply (RList_P4 _ _ Hs).
    move => i Hi ; by apply lt_n_O in Hi.
    simpl ; case: s Hs {IH Hpos} => [ | h0 s] Hs Hi //=.
    by apply lt_n_O in Hi.
    by apply (Hs O (lt_O_Sn _)).
    have : (h' <= h).
      replace h' with (pos_Rl (RList.cons h' s') O) by auto.
      apply Rle_trans with (2 := Hpos (lt_O_Sn _)).
      elim: s' h' Hs' {Hpos} => {IH} [| h'0 s' IH] h' Hs'.
      by apply Rle_refl.
      apply Rle_trans with (1 := Hs' O (lt_O_Sn _)).
      apply (IH h'0 (RList_P4 _ _ Hs')).
    simpl ; case: Rle_dec => // _ _.
    rewrite IH // => {IH}.
    simpl ;
    replace (cons_Rlist (insert s' h) s) with 
      (cons_Rlist s' (RList.cons h s)) => //.
    move: (Hpos (lt_O_Sn _)) Hs' Hs ; elim: s' h' s h {Hpos} =>
      [ | h'0 s' IH] h' s h Hpos Hs' Hs //=.
      have : (h'0 <= h).
      replace h'0 with (pos_Rl (RList.cons h' (RList.cons h'0 s')) 1) by auto.
      apply Rle_trans with (2 := Hpos).
      elim: s' h' h'0 Hs' {IH Hpos} => [| h'1 s' IH] h' h'0 Hs'.
      by apply Rle_refl.
      apply Rle_trans with (1 := Hs' 1%nat (lt_n_S _ _ (lt_O_Sn _))).
      apply (IH h'0 h'1 (RList_P4 _ _ Hs')).
      case: Rle_dec => //= _ _.
      rewrite (IH h'0 s h) => //.
      apply (RList_P4 _ _ Hs').
      apply (RList_P4 _ _ Hs).
    have : (h' <= h).
      replace h' with (pos_Rl (RList.cons h' s') O) by auto.
      apply Rle_trans with (2 := Hpos (lt_O_Sn _)).
      elim: s' h' Hs' {Hpos} => [| h'0 s' IH] h' Hs'.
      by apply Rle_refl.
      apply Rle_trans with (1 := Hs' O (lt_O_Sn _)).
      apply (IH h'0 (RList_P4 _ _ Hs')).
      elim: s' h' Hs' Hpos => [ | h'0 s' IH] h' Hs' Hpos Hle //= i Hi.
      case: i Hi => [ | i] //= Hi.
      by apply lt_S_n, lt_n_O in Hi.
      have : (h'0 <= h).
      replace h'0 with (pos_Rl (RList.cons h' (RList.cons h'0 s')) 1) by auto.
      apply Rle_trans with (2 := (Hpos (lt_O_Sn _))).
      elim: s' h' h'0 Hs' {IH Hpos Hle Hi} => [| h'1 s' IH] h' h'0 Hs'.
      by apply Rle_refl.
      apply Rle_trans with (1 := Hs' 1%nat (lt_n_S _ _ (lt_O_Sn _))).
      apply (IH h'0 h'1 (RList_P4 _ _ Hs')).
      move: Hi ; case: Rle_dec => // _ Hi H.
      case: i Hi => [ | i] Hi.
      apply (Hs' O) => //= ; by apply lt_O_Sn.
      apply (IH h'0 (RList_P4 _ _ Hs')) => //.
      apply lt_S_n, Hi.
      case: s Hs Hpos => [ | h0 s] Hs Hpos Hi.
      by apply lt_n_O in Hi.
      clear Hi.
      simpl Peano.pred.
      apply Rle_trans with (2 := Hs O (lt_O_Sn _)).
      move: (Hpos (lt_O_Sn _)) => {Hpos} ; 
      elim: s' h' s h h0 {1 3}((Rlength (insert s' h))) (le_refl (Rlength (insert s' h))) Hs' Hs 
      => [ | h'0 s' IH]  h' s h h0 i Hi Hs' Hs Hpos //.
      simpl ; case: i Hi => // ; case => //.
      move => _ ; apply Rle_refl.
      move => i /= Hi ; by apply lt_S_n, lt_n_O in Hi.
      have : (h'0 <= h).
      replace h'0 with (pos_Rl (RList.cons h' (RList.cons h'0 s')) 1) by auto.
      apply Rle_trans with (2 := (Hpos)).
      elim: s' h' h'0 Hs' {IH Hpos Hi} => [| h'1 s' IH] h' h'0 Hs'.
      by apply Rle_refl.
      apply Rle_trans with (1 := Hs' 1%nat (lt_n_S _ _ (lt_O_Sn _))).
      apply (IH h'0 h'1 (RList_P4 _ _ Hs')).
      move: Hi ; simpl RList.cons ; simpl Rlength ; case: Rle_dec => // _ Hi _.
      case: i Hi => [ /= |i] Hi.
      replace h' with (pos_Rl (RList.cons h' s') O) by auto.
      apply Rle_trans with (2 := Hpos).
      elim: s' h' h'0 Hs' {IH Hpos Hi} => [| h'1 s' IH] h' h'0 Hs'.
      by apply (Hs' O (lt_O_Sn _)).
      apply Rle_trans with (1 := Hs' O (lt_O_Sn _)).
      apply (IH h'0 h'1 (RList_P4 _ _ Hs')).
    apply (IH h'0 s h h0) => // ; intuition.
    apply (RList_P4 _ _ Hs').

  elim: s s' => [ | h s IH] ; case => [ | h' s'] // Hs Hs'.
  simpl ; apply H => //= ; intuition.
  apply (RList_P4 _ _ Hs).
  move => i Hi ; by apply lt_n_O in Hi.
  case: s Hs H0 {IH} => // ; intuition.
  by apply lt_n_O in H0.
  by apply (Hs O (lt_O_Sn _)).
  simpl ; case: Rle_dec => // H0.
  simpl ; rewrite IH => {IH}.
  case: s Hs => [ | h0 s] Hs //.
  have : (h' <= h0).
    apply Rle_trans with (1 := H0), (Hs O (lt_O_Sn _)).
  case: Rle_dec => // _ _.
  apply RList_P4 with (1 := Hs).
  case: s' Hs' => // [ | h'0 s'] Hs' ; case => [ | i] // Hi.
  simpl in Hi ; by apply lt_S_n, lt_n_O in Hi.
  case: (RList_P0 (RList.cons h'0 s') h) => //= -> //.
  apply (Hs' O (lt_O_Sn _)).
  apply (RList_P1 _ _ (RList_P4 _ _ Hs') i) ; intuition.
  simpl ; rewrite IH => {IH}.
  case: s Hs => [ | h0 s] Hs //.
  move: (Hs O (lt_O_Sn _)).
  case: Rle_dec => // _ _.
  apply RList_P4 with (1 := Hs).
  case => [ | i] Hi.
  apply Rlt_le, Rnot_le_lt, H0.
  apply (Hs' i (lt_S_n _ _ Hi)).
Admitted.

Lemma RInt_sup_up f a b n (Hab : a < b) :
  forall sf : StepFun a b, forall M,
  (forall t, a <= t <= b -> 0 <= f t <= sf t) ->
  (forall t, a <= t <= b -> 0 <= f t <= M) ->
    Rbar_le 
      (Rbar_mult_pos (RInt_sup f a b n) (mkposreal (b-a) (Rlt_Rminus _ _ Hab)))
      (Finite (RiemannInt_SF sf + M*(b-a)/2^n * INR (Rlength (projT1 (pre sf))))).
Proof.
  intros.
  rewrite -(RInt_sup_real_1 f a b n M) ; 
  [ | rewrite /Rmin /Rmax ; move: (Rlt_le _ _ Hab) ; 
  case: Rle_dec => // _ _ x Hx ; by apply H0].
  replace (Rbar_mult_pos _ _) with 
    (Finite (RiemannInt_SF (SF_sup_r f a b n))) ; 
    [ | rewrite (RInt_sup_compat f a b n M) /= ; 
    [ apply Rbar_finite_eq ; ring 
    | rewrite /Rmin /Rmax ; move: (Rlt_le _ _ Hab) ; 
    case: Rle_dec => // _ _ x Hx ; by apply H0]].
  apply Rbar_finite_le.
  move : (proj1 (ad_SF_sup_r f a b n) (Rlt_le _ _ Hab)) => Had.
  rewrite /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ; 
  move: (Rlt_le _ _ Hab) ; case: Rle_dec => // _ _.
  rewrite /subdivision_val /subdivision ;
  case: sf H => sf [sx [sy' Hsf]] ; simpl Rlength ; 
  simpl Int_SF at 2 ; simpl fe => H.

  have Hnth : (forall i, (S i < Rlength (seq2Rlist (RInt_part a b n)))%nat ->
    pos_Rl (seq2Rlist (RInt_part a b n)) (S i) - pos_Rl (seq2Rlist (RInt_part a b n)) i 
      = (b-a)/2^n).
    move => i ; rewrite ?nth_compat size_compat ?size_mkseq => Hi ; 
    rewrite ?nth_mkseq ?S_INR /= ; try apply SSR_leq ; intuition ;
    field ; apply Rgt_not_eq ; intuition.
  move: Had ; rewrite /SF_sup_fun ; move: (Rlt_le _ _ Hab) ; 
  case: Rle_dec => // _ _ ; rewrite /SF_sup_seq.
  rewrite -{1 3 4}(Rlist2seq_bij (RInt_part a b n)) => Had.
(* initialisation *)
  move: (seq2Rlist (RInt_part a b n)) (seq2Rlist
    (behead
    (pairmap (fun x y : R => real (Sup_fct f x y)) 0
    (Rlist2seq (seq2Rlist (RInt_part a b n)))))) Had Hnth => rx ry' Had Hnth.
  case: (StepFun_P23 (existT (fun _ => _) sy' Hsf) (existT (fun _ => _) ry' Had))
    => sy Hsy ;
  case: (StepFun_P25 (existT (fun _ => _) sy' Hsf) (existT (fun _ => _) ry' Had))
    => ry Hry ;
  move: (StepFun_P9 Hsf (Rlt_not_eq _ _ Hab)) => Hsx ;
  move: (StepFun_P9 Had (Rlt_not_eq _ _ Hab)) => Hrx ;
  rewrite (StepFun_P17 Had Hry) ;
  rewrite (StepFun_P17 Hsf Hsy).
  case: (RList_P20 sx Hsx) Hsf Hsy Hry => {sx Hsx} x0 [x1 [sx ->]] Hsf ;
  case: (RList_P20 rx Hrx) Had Hnth => {rx Hrx} h0 [h1 [rx ->]] Had Hnth Hsy Hry.
  have H1 : exists y0, exists y1, exists y2, exists sy0, 
    sy = RList.cons y0 (RList.cons y1 (RList.cons y2 sy0)).
    move: (sy) (proj1 (proj2 (proj2 (proj2 Hsy)))) ;
    rewrite RList_P11 ; case => //= y0 ; rewrite -?plus_n_Sm ; 
    case => //= y1 ; case => //= y2 sy0 _ ;
    exists y0 ; exists y1 ; exists y2 ; exists sy0 => //.
  case: H1 Hsy => {sy} y0 [y1 [y2 [sy ->]]] Hsy.
  have H1 : exists l0, exists l1, exists l2, exists ry0, 
    ry = RList.cons l0 (RList.cons l1 (RList.cons l2 ry0)).
    move: (ry) (proj1 (proj2 (proj2 (proj2 Hry)))) ;
    rewrite RList_P11 ; case => //= l0 ; rewrite -?plus_n_Sm ; 
    case => //= l1 ; case => //= l2 ry0 _ ;
    exists l0 ; exists l1 ; exists l2 ; exists ry0 => //.
  case: H1 Hry => {ry} l0 [l1 [l2 [ry ->]]] Hry.
  move: (proj1 Hsf) (proj1 Had) (proj1 (proj2 (proj2 (proj2 Hsy))))
  (proj1 (proj2 (proj2 (proj2 Hry)))) => {Hsf Had} Hsx Hrx.
  rewrite RList_P11 ; simpl Rlength ; rewrite -?plus_n_Sm ?plus_Sn_m => Hsxy Hrxy.
  repeat apply eq_add_S in Hsxy ;
  repeat apply eq_add_S in Hrxy.

  have Ha : a = Rmin x0 h0.
    rewrite sorted_cons_ORlist in Hsy => //.
    apply Rmin_case_strong => H1 ; 
    [apply Rle_lt_or_eq_dec in H1 ; case: H1 => H1 ; 
    [ apply Rlt_not_le in H1 | ] | ] ;
    move: Hsy ; rewrite /Rmin ; case: Rle_dec => // H2 Hsy.
    apply sym_equal ; rewrite -(Rmin_left a b (Rlt_le _ _ Hab)) ; apply Hsy.
    rewrite -H1 in Hsy ; apply sym_equal ; 
    rewrite -(Rmin_left a b (Rlt_le _ _ Hab)) ; apply Hsy.
    contradict H2 ; apply Req_le ; by rewrite H1.
    apply sym_equal ; rewrite -(Rmin_left a b (Rlt_le _ _ Hab)) ; apply Hsy.
  move : (Hab) => Hb ; rewrite Ha in H, H0, Hsy, Hry, Hb.
  
  move : {2}(Rlength sx + Rlength rx)%nat (le_refl (Rlength sx + Rlength rx)%nat) 
  (Req_le _ _ Ha) (Rlt_le _ _ Hb) Hsx Hrx => {sy' ry' Ha Hb} i.
  
(* récurrence *)
  elim: i x0 x1 sx sy h0 h1 rx ry H H0 Hsy Hry Hsxy Hrxy Hnth 
    => [ | i IH] x0 x1 sx sy h0 h1 rx ry H H0 Hsy Hry Hsxy Hrxy Hnth Hi Ha Hb Hsx Hrx.

(* * |sx| + |rx| = 0*)
  apply le_n_0_eq, sym_equal, plus_is_O in Hi ; case: Hi => Hi Hi'.
  case: sx Hi Hsx Hi' Hrx Hsy Hsxy Hry Hrxy => // _ Hsx.
  case: rx Hnth => // Hnth _ Hrx Hsy Hsxy Hry Hrxy.
  case: ry Hrxy Hry => // _ Hry.
  case: sy Hsxy Hsy => // _ Hsy.
  have Hs0 : ordered_Rlist RList.nil.
    move => i Hi ; by apply lt_n_O in Hi.
  have Hh1 : ordered_Rlist (RList.cons h1 RList.nil).
    move => i Hi ; by apply lt_n_O in Hi.
  have Hx1 : ordered_Rlist (RList.cons x1 RList.nil).
    move => i Hi ; by apply lt_n_O in Hi.
  move: Hsy Hry ; rewrite ?sorted_cons_ORlist // => {Hs0 Hh1 Hx1}.
  move: (Hsx O (lt_O_Sn _)) => {Hsx} Hsx ; simpl in Hsx.
  move: (Hrx O (lt_O_Sn _)) => {Hrx} Hrx ; simpl in Hrx.
  case: Rle_dec => // H2 ; case: Rle_dec => // H3 ; 
  try case: Rle_dec => // H4 ; move => /= Hsy Hry ;
  rewrite !Rplus_0_r.
  move: (proj2 (proj2 (proj2 (proj2 Hry))) O (lt_O_Sn _) ((h1-h0)/2)) => /= <-.
  replace (y0 * (h1 - h0) + (y1 * (x0 - h1) + (y2 * (x1 - x0))) +
    M * (b - a) / 2 ^ n * 2) with 
    (M*(b-a)/2^n + (y0 * (h1 - h0) + (y1 * (x0 - h1) + (y2 * (x1 - x0))) +
    M * (b - a) / 2 ^ n)) by ring.
  apply Rplus_le_compat.
  move: (Hnth O (lt_n_S _ _ (lt_O_Sn _))) => /= ->.
  rewrite /Rdiv ?Rmult_assoc.
  apply Rmult_le_compat_r.
  apply Rdiv_le_pos.
  apply Rlt_le, Rlt_Rminus => //.
  intuition.
  rewrite /SF_fun /=.
Admitted.

Lemma ex_RInt_correct_4 (f : R -> R) (a b : R) : Riemann_integrable f a b -> 
  forall (eps : posreal), exists n, 
    Rbar_le (RInt_sup f a b n) (Rbar_plus (RInt_inf f a b n) (Finite eps)).
Proof.
  wlog: a b / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab Hri eps.
    case: (Rle_lt_or_eq_dec _ _ Hab) Hri => {Hab} [ Hab | <- ] Hri.
    by apply Hw.
    exists O ; 
    replace (RInt_sup f a a O) with (Finite (f a)) ; 
    [replace (RInt_inf f a a O) with (Finite (f a)) | ] ; simpl.
    apply Rbar_finite_le, Rminus_le_0 ; ring_simplify ; apply Rlt_le, eps.
    rewrite /RInt_inf /=.
    replace (Inf_fct f (a + 0 * (a - a) / 1) (a + 1 * (a - a) / 1))
      with (Finite (f a)).
      simpl ; apply Rbar_finite_eq ; field.
      replace (a + 0 * (a - a) / 1) with a by field ;
      replace (a + 1 * (a - a) / 1) with a by field ;
      rewrite /Inf_fct /Glb_Rbar_ne ; case: ex_glb_Rbar_ne => g Hg /=.
      apply Rbar_le_antisym ; apply Hg.
      move => {Hg} _ [x [-> Hg]].
      case: Hg (Rle_refl a) ; rewrite /Rmin /Rmax ; 
      case: Rle_dec => // _ Hax Hxa _ ; rewrite (Rle_antisym x a) // ;
      by right.
      exists a ; split => // ; by apply Rmin_Rmax_l.
    rewrite /RInt_sup /=.
    replace (Sup_fct f (a + 0 * (a - a) / 1) (a + 1 * (a - a) / 1))
      with (Finite (f a)).
      simpl ; apply Rbar_finite_eq ; field.
      replace (a + 0 * (a - a) / 1) with a by field ;
      replace (a + 1 * (a - a) / 1) with a by field ;
      rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l Hl /=.
      apply Rbar_le_antisym ; apply Hl.
      exists a ; split => // ; by apply Rmin_Rmax_l.
      move => {Hl} _ [x [-> Hl]].
      case: Hl (Rle_refl a) ; rewrite /Rmin /Rmax ; 
      case: Rle_dec => // _ Hax Hxa _ ; rewrite (Rle_antisym x a) // ;
      by right.
    apply RiemannInt_P1 in Hri ; 
    case: (Hw b a Hab Hri eps) => {Hw} n Hw ; exists n.
    rewrite RInt_sup_bound RInt_inf_bound ; apply Hw.

  move => Hri eps ; set e2 := pos_div_2 eps ; 
  case: (Riemann_integrable_bound _ _ _ (RiemannInt_P16 Hri)) => [M Hub] ;
  case: (Hri e2) => phi [psi [Hle Heps]] ;
  set SF_max := mkStepFun (StepFun_P28 1 phi psi) ;
  set SF_min := mkStepFun (StepFun_P28 (-1) phi psi) ;
  set SF_psi := mkStepFun (StepFun_P28 (-1) SF_max SF_min).

  have : forall t : R, a <= t <= b -> SF_min t <= f t <= SF_max t.
    move => t Ht ; apply Rlt_le in Hab ; 
    rewrite /SF_min /SF_max /= Ropp_mult_distr_l_reverse Rmult_1_l ; 
    apply Rabs_le_between', Hle ; rewrite /Rmin /Rmax ; case: Rle_dec => //.
  move => {Hle} Hle.
  have : Rabs (RiemannInt_SF SF_psi) < eps.
    rewrite ?StepFun_P30. 
    replace (RiemannInt_SF phi + 1 * RiemannInt_SF psi +
      -1 * (RiemannInt_SF phi + -1 * RiemannInt_SF psi))
      with (2*RiemannInt_SF psi) by ring.
    rewrite Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ Rlt_R0_R2)).
    replace (pos eps) with (2*e2).
    apply Rmult_lt_compat_l with (2 := Heps), Rlt_R0_R2.
    simpl ; field.
  move => {Heps} Heps.
  case: SF_max SF_psi Hle Heps => SF_max [SF_max_x [SF_max_y H_max]] SF_psi /= Hle Heps.
  set SF_max_fun := mkStepFun (existT (fun _ => _) SF_max_x 
    (existT (fun _ => _) SF_max_y H_max)).
  have H_max_dec : forall n i, (S i < size (RInt_part a b n))%nat -> 
    {j : nat | pos_Rl SF_max_x j < nth 0 (RInt_part a b n) i 
    /\ nth 0 (RInt_part a b n) (S i) < pos_Rl SF_max_x (S j) 
    /\ (S j < Rlength SF_max_x)%nat} 
    + {j : nat | nth 0 (RInt_part a b n) i <= pos_Rl SF_max_x j <= nth 0 (RInt_part a b n) (S i) 
    /\ (j < Rlength SF_max_x)%nat}.
    move => n i Hi.
    have H : sorted Rle (Rlist2seq SF_max_x).
      apply sorted_compat ; rewrite seq2Rlist_bij ; apply H_max.
    have H0 : forall i, (i < size (RInt_part a b n))%nat -> 
      head 0 (Rlist2seq SF_max_x) <= nth 0 (RInt_part a b n) i <=
        last 0 (Rlist2seq SF_max_x).
      move => i0 Hi0.
      rewrite -nth0 -nth_last -?[nth _ (Rlist2seq _) _]nth_compat 
      -size_compat seq2Rlist_bij.
      rewrite (proj1 (proj2 H_max)) (proj1 (proj2 (proj2 H_max))).
      rewrite /Rmin /Rmax ; set Hab' := Rlt_le _ _ Hab ; case: Rle_dec => //_.
      pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
      pattern b at 4 ; replace b with (last 0 (RInt_part a b n)).
      set (RInt_part_sort a b n (Rlt_le _ _ Hab)) ;
      split ; [apply sorted_head | apply sorted_last] => // ; intuition.
      rewrite -nth_last size_mkseq nth_mkseq // pow2_INR ; 
      field ; apply Rgt_not_eq ; intuition.
      rewrite -nth0 nth_mkseq //= ; 
      field ; apply Rgt_not_eq ; intuition.
    rewrite -(seq2Rlist_bij SF_max_x).
    case: (sorted_dec (Rlist2seq SF_max_x) 0 (nth 0 (RInt_part a b n) i) H (H0 i _)) 
      => // [ | [j [Hij Hj]] | Hij] ; [intuition | | ] ;
    case: (sorted_dec (Rlist2seq SF_max_x) 0 (nth 0 (RInt_part a b n) (S i)) H (H0 (S i) _)) 
      => // [[j' [Hij' Hj']] | Hij'].
    case: (le_lt_dec j j') => Hjj'.
    apply le_lt_eq_dec in Hjj' ; case: Hjj' => Hjj'.
    right ; exists j' ; rewrite ?nth_compat size_compat ; intuition.
    apply Rlt_le, Rlt_le_trans with (1 := H2).
    apply sorted_incr ; intuition.
    rewrite -Hjj' in Hij', Hj' => {j' Hjj'}.
    case: Hij => Hij _ ; apply Rle_lt_or_eq_dec in Hij ; case: Hij => Hij.
    left ; exists j ; rewrite ?nth_compat size_compat ; intuition.
    right ; exists j ; rewrite ?nth_compat size_compat ; intuition.
    absurd (nth 0 (Rlist2seq SF_max_x) j < nth 0 (Rlist2seq SF_max_x) (S j')).
    apply Rle_not_lt, sorted_incr ; intuition.
    apply Rle_lt_trans with (1 := proj1 Hij).
    apply Rle_lt_trans with (2 := proj2 Hij').
    apply (sorted_nth Rle) ; intuition ; apply RInt_part_sort ; intuition.
    case: (le_lt_dec j (size (Rlist2seq SF_max_x) - 2)%nat) => Hjj'.
    apply le_lt_eq_dec in Hjj' ; case: Hjj' => Hjj'.
    right ; exists (size (Rlist2seq SF_max_x) - 2)%nat ; 
    rewrite ?nth_compat size_compat ; intuition.
    apply Rlt_le, Rlt_le_trans with (1 := H2).
    apply sorted_incr ; intuition.
    rewrite Hjj' in Hij, Hj => {j Hjj'}.
    case: Hij => Hij Hij0 ; apply Rle_lt_or_eq_dec in Hij ; case: Hij => Hij.
    case: Hij' => Hij'0 Hij' ; apply Rle_lt_or_eq_dec in Hij' ; case: Hij' => Hij'.
    left ; exists ((size (Rlist2seq SF_max_x) - 2)%nat) ; 
    rewrite ?nth_compat size_compat ; intuition.
    apply Rlt_le_trans with (1 := Hij') ; apply Req_le.
    move: (StepFun_P9 H_max (Rlt_not_eq _ _ Hab)).
    case: (SF_max_x) => [|x0 s] //= ; case: s => [|x1 s] Hs //=.
    by apply le_S_n, le_Sn_O in Hs.
    by rewrite -minus_n_O.
    right ; exists (size (Rlist2seq SF_max_x) - 1)%nat ; 
    rewrite ?nth_compat size_compat -Hij' ; intuition.
    apply (sorted_nth Rle) ; intuition ; apply RInt_part_sort ; intuition.
    right ; exists (size (Rlist2seq SF_max_x) - 2)%nat ; 
    rewrite ?nth_compat size_compat -Hij ; intuition.
    contradict Hjj' ; apply le_not_lt ; intuition.
    absurd (nth 0 (Rlist2seq SF_max_x) (size (Rlist2seq SF_max_x) -2) < nth 0 (Rlist2seq SF_max_x) ( S j')).
    apply Rle_not_lt, sorted_incr ; intuition.
    apply Rle_lt_trans with (1 := proj1 Hij).
    apply Rle_lt_trans with (2 := proj2 Hij').
    apply (sorted_nth Rle) ; intuition ; apply RInt_part_sort ; intuition.
    case: Hij => Hij _ ; apply Rle_lt_or_eq_dec in Hij ; case: Hij => Hij.
    case: Hij' => _ Hij' ; apply Rle_lt_or_eq_dec in Hij' ; case: Hij' => Hij'.
    left ; exists (size (Rlist2seq SF_max_x) - 2)%nat ; 
    rewrite ?nth_compat size_compat ; intuition.
    apply Rlt_le_trans with (1 := Hij'), Req_le.
    move: (StepFun_P9 H_max (Rlt_not_eq _ _ Hab)).
    case: (SF_max_x) => [|x0 s] //= ; case: s => [|x1 s] Hs //=.
    by apply le_S_n, le_Sn_O in Hs.
    by rewrite -minus_n_O.
    move: (StepFun_P9 H_max (Rlt_not_eq _ _ Hab)).
    case: (SF_max_x) => [|x0 s] //= ; case: s => [|x1 s] Hs //=.
    by rewrite -minus_n_O.
    right ; exists (size (Rlist2seq SF_max_x) - 1)%nat ;
    rewrite ?nth_compat size_compat -Hij' ; intuition.
    apply (sorted_nth Rle) ; intuition ; apply RInt_part_sort ; intuition.
    move: (StepFun_P9 H_max (Rlt_not_eq _ _ Hab)).
    case: (SF_max_x) => [|x0 s] //= Hs.
    by apply le_Sn_O in Hs.
    by rewrite -minus_n_O.
    right ; exists (size (Rlist2seq SF_max_x) - 2)%nat ;
    rewrite ?nth_compat size_compat Hij ; intuition.
    apply (sorted_nth Rle) ; intuition ; apply RInt_part_sort ; intuition.
    move: (StepFun_P9 H_max (Rlt_not_eq _ _ Hab)).
    case: (SF_max_x) => [|x0 s] //= Hs.
    by apply le_Sn_O in Hs.
    case: s Hs => [|x1 s] //= Hs.
    by apply le_S_n, le_Sn_O in Hs.
    rewrite -minus_n_O ; intuition.

  have H_le_dec : forall n i Hi, Rbar_le (nth (Finite 0) (SF_ly (SF_sup_seq f a b n)) i) 
    (match (H_max_dec n i Hi) with
      | inl H => Finite (pos_Rl SF_max_y (projT1 H))
      | inr H => Finite M
    end).
    move => n i Hi ; rewrite SF_sup_ly nth_behead (nth_pairmap 0).
    replace (nth _ (0::_) _) with (nth 0 (RInt_part a b n) i) by auto.
    case: H_max_dec ; case => j Hj ; simpl projT1.
    rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l Hl ; simpl projT1.
    apply Hl => {Hl} _ [x [ -> Hl]].
    move: Hl (proj1 (sorted_nth _ _) 
    (RInt_part_sort a b n (Rlt_le _ _ Hab)) i (lt_pred _ _ Hi) 0) ; 
    rewrite /Rmin /Rmax ; case: Rle_dec => // _ Hl _.
    apply Rbar_finite_le ; apply Rle_trans with (r2 := SF_max x).
    apply Hle ; admit.
    apply Req_le ; apply (proj2 (proj2 (proj2 (proj2 H_max)))) ; intuition.
    split.
    apply Rlt_le_trans with (1 := H), H1.
    apply Rle_lt_trans with (1 := H2), H3.
    rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l Hl ; simpl projT1.
    apply Hl => {Hl} _ [x [-> Hl]].
    apply Rbar_finite_le, Rle_trans with (1 := Rle_abs _), Hub ; admit.
    apply SSR_leq ; intuition.
  
  have: (forall n, Rbar_le (RInt_sup f a b n) 
    (Finite (RiemannInt_SF SF_max_fun / (b-a) + (M/2^n)* INR (Rlength SF_max_x)))).
    move => n ; move: (H_max_dec n) (H_le_dec n) ; rewrite /RInt_sup SF_sup_ly.
    have: forall i, (S i < size (RInt_part a b n))%nat ->
      nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/2^n.
      admit.
    have: (1 < size (RInt_part a b n))%nat.
      rewrite size_mkseq /= ; apply lt_n_S.
      apply INR_lt ; rewrite pow2_INR ; intuition.
    move: (Rlt_le _ _ Hab) ; rewrite /RiemannInt_SF /subdivision /subdivision_val ; 
    case: Rle_dec => // _ _ ; simpl Int_SF.
    move: (proj1 (proj2( proj2 (proj2 H_max)))).
    generalize (RInt_part a b n) SF_max_x SF_max_y.
    case => [| h s] // SFx SFy Hs Hl.
    by apply lt_n_O in Hl.
    case: s Hl => [| h0 s] // Hl.
    by apply lt_irrefl in Hl.
    elim: s h h0 SFx SFy Hs {Hl Hle} => [| h1 s IH] h h0 SFx SFy Hs Hnth Hdec Hle //.
    move: (Hle O (lt_n_S _ _ (lt_O_Sn _))) ; 
    case: (Hdec O _) => /= [[j Hj]|[j Hj]] /= Hle0.
    replace (Rbar_div_pos (Rbar_plus (Sup_fct f h h0) (Finite 0)) _) 
      with (Rbar_div_pos (Sup_fct f h h0) (mkposreal _ (pow_lt 2 n Rlt_R0_R2))).
    replace (Finite _) with
      (Rbar_div_pos (Finite (Int_SF SFy SFx * 2^n / (b - a) + M*INR (Rlength SFx)))
       {| pos := 2 ^ n; cond_pos := pow_lt 2 n Rlt_R0_R2 |}).
    apply Rbar_div_pos_le, Rbar_le_trans with (1 := Hle0).
Admitted.

Lemma ex_RInt_correct_3 (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> ex_RInt f a b.
Proof.
  wlog : a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab H.
    by apply Hw.
    apply Rlt_le in Hab ; apply  ex_RInt_bound, Hw => // ; 
    by apply RiemannInt_P1.
  move => Hri.
  case: (Riemann_integrable_bound f a b Hri) => M Hmax.
  have : (exists m, forall x : R, Rmin a b <= x <= Rmax a b -> m <= f x).
    have: exists m : R, forall x : R, Rmin a b <= x <= Rmax a b -> 0+ (-1)* f x <= m.
      apply (Riemann_integrable_bound (fun x => 0+ (-1)* f x) a b).
      apply RiemannInt_P10 => // ; apply RiemannInt_P14.
    case => m Hm ; exists (-m) => h Hx ; apply Ropp_le_cancel ;
    rewrite Ropp_involutive ; replace (- f h) with (0 + -1 * f h) by ring => // ;
    by apply Hm.
  case => m Hmin.
  have H : (Finite (real (Rbar_inf_seq (RInt_sup f a b))) = Rbar_inf_seq (RInt_sup f a b)).
    rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq ; case => glb //=.
  (* RInt_sup --> p_infty *)
    move: (glb M O) => {glb} glb.
    contradict glb ; apply Rbar_le_not_lt.
    rewrite /RInt_sup SF_sup_ly /= ;
    replace (Finite M) with 
    (Rbar_div_pos (Finite M) (mkposreal _ (pow_lt 2 O Rlt_R0_R2))).
    apply Rbar_div_pos_le ; rewrite /= Rmult_1_l.
    rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l Hl /=.
    replace (Rbar_plus _ _) with l.
    apply Hl => {Hl} _ [x [-> Hl]] ; apply Rbar_finite_le, Hmax ;
    replace a with (a + 0 * (b - a) / 1) by field ;
    pattern b at 2 4 ; replace b with (a + (b - a) / 1) by field ;
    by apply Hl.
    case: (l) => //= r ; by rewrite Rplus_0_r.
    simpl ; apply Rbar_finite_eq ; field.
    
  (* RInt_inf --> p_infty *)
    case: (glb m) => {glb} n glb.
    contradict glb ; apply Rbar_le_not_lt.
    rewrite /RInt_sup SF_sup_ly.
    replace (Finite m) with 
      (Rbar_div_pos (Finite (2^n*m)) (mkposreal _ (pow_lt 2 n Rlt_R0_R2))).
    apply Rbar_div_pos_le.
    replace (2^n) with (INR (Peano.pred (size (RInt_part a b n)))).
    have: (forall i, (i < size (RInt_part a b n))%nat -> 
      Rmin a b <= nth 0 (RInt_part a b n) i <= Rmax a b).
      move => i Hi ; 
      replace (Rmin a b) with (head 0 (RInt_part a b n)).
      replace (Rmax a b) with (last 0 (RInt_part a b n)).
      split.
      apply sorted_head => // ; by apply RInt_part_sort.
      apply sorted_last => // ; by apply RInt_part_sort.
      rewrite /Rmax ; case: Rle_dec => // _ ; 
      rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ;
      field ; apply Rgt_not_eq ; intuition.
      rewrite /Rmin ; case: Rle_dec => // _ ; 
      rewrite -nth0 nth_mkseq //= ;
      field ; apply Rgt_not_eq ; intuition.
    case: (RInt_part a b n) => [| h s] /=.
    right ; apply Rbar_finite_eq ; ring.
    elim: s h => [| h0 s IH] h Hdom.
    right => /= ; apply Rbar_finite_eq ; ring.
    replace (size (_::_)) with (S (size s)) by auto ; rewrite S_INR /=.
    rewrite Rmult_plus_distr_r Rplus_comm Rmult_1_l ; 
    apply (Rbar_plus_le_compat (Finite m) _ (Finite (INR (size s) * m))).
    rewrite /Sup_fct /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l Hl /=.
    apply Rbar_le_trans with (Finite (f h)).
    apply Rbar_finite_le, Hmin, (Hdom O), lt_O_Sn.
    apply Hl ; exists h ; split => // ; apply Rmin_Rmax_l.
    apply (IH h0) => i Hi ; apply (Hdom (S i)) => /= ; intuition.
    rewrite size_mkseq /= pow2_INR //.
    simpl ; apply Rbar_finite_eq ; field ; apply Rgt_not_eq ; intuition.
  have H0 : (Finite (real (Rbar_sup_seq (RInt_inf f a b))) = Rbar_sup_seq (RInt_inf f a b)).
    rewrite /Rbar_sup_seq ; case: Rbar_ex_sup_seq ; case => lub //=.
  (* RInt_inf --> p_infty *)
    case: (lub M) => {lub} n lub.
    contradict lub ; apply Rbar_le_not_lt.
    rewrite /RInt_inf SF_inf_ly.
    replace (Finite M) with 
      (Rbar_div_pos (Finite (2^n*M)) (mkposreal _ (pow_lt 2 n Rlt_R0_R2))).
    apply Rbar_div_pos_le.
    replace (2^n) with (INR (Peano.pred (size (RInt_part a b n)))).
    have: (forall i, (i < size (RInt_part a b n))%nat -> 
      Rmin a b <= nth 0 (RInt_part a b n) i <= Rmax a b).
      move => i Hi ; 
      replace (Rmin a b) with (head 0 (RInt_part a b n)).
      replace (Rmax a b) with (last 0 (RInt_part a b n)).
      split.
      apply sorted_head => // ; by apply RInt_part_sort.
      apply sorted_last => // ; by apply RInt_part_sort.
      rewrite /Rmax ; case: Rle_dec => // _ ; 
      rewrite -nth_last size_mkseq nth_mkseq //= pow2_INR ;
      field ; apply Rgt_not_eq ; intuition.
      rewrite /Rmin ; case: Rle_dec => // _ ; 
      rewrite -nth0 nth_mkseq //= ;
      field ; apply Rgt_not_eq ; intuition.
    case: (RInt_part a b n) => [| h s] /=.
    right ; apply Rbar_finite_eq ; ring.
    elim: s h => [| h0 s IH] h Hdom.
    right => /= ; apply Rbar_finite_eq ; ring.
    replace (size (_::_)) with (S (size s)) by auto ; rewrite S_INR /=.
    rewrite Rmult_plus_distr_r Rplus_comm Rmult_1_l ; 
    apply (Rbar_plus_le_compat _ (Finite M) _ (Finite (INR (size s) * M))).
    rewrite /Inf_fct /Glb_Rbar_ne ; case: ex_glb_Rbar_ne => l Hl /=.
    apply Rbar_le_trans with (Finite (f h)).
    apply Hl ; exists h ; split => // ; apply Rmin_Rmax_l.
    apply Rbar_finite_le, Hmax, (Hdom O), lt_O_Sn.
    apply (IH h0) => i Hi ; apply (Hdom (S i)) => /= ; intuition.
    rewrite size_mkseq /= pow2_INR //.
    simpl ; apply Rbar_finite_eq ; field ; apply Rgt_not_eq ; intuition.
  (* RInt_inf --> m_infty *)
    move: (lub m O) => {lub} lub.
    contradict lub ; apply Rbar_le_not_lt.
    rewrite /RInt_inf SF_inf_ly /= ;
    replace (Finite m) with 
      (Rbar_div_pos (Finite (m)) (mkposreal _ (pow_lt 2 O Rlt_R0_R2))).
    apply Rbar_div_pos_le ; rewrite /= Rmult_1_l.
    rewrite /Inf_fct /Glb_Rbar_ne ; case: ex_glb_Rbar_ne => l Hl /=.
    replace (Rbar_plus _ _) with l.
    apply Hl => {Hl} _ [x [-> Hl]] ; apply Rbar_finite_le, Hmin ;
    replace a with (a + 0 * (b - a) / 1) by field ;
    pattern b at 2 4 ; replace b with (a + (b - a) / 1) by field ;
    by apply Hl.
    case: (l) => //= r ; by rewrite Rplus_0_r.
    simpl ; apply Rbar_finite_eq ; field.
    
  split => //.
  move: H ; rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq ; 
    case => [g | | ] glb // _ ; simpl projT1.
  move: H0 ; rewrite /Rbar_sup_seq ; case: Rbar_ex_sup_seq ; 
    case => [l | | ] lub // _ ; simpl projT1.
  apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => eps Heps ; 
  set e := mkposreal eps Heps ; case: (Hri e) => phi [psi [Hphi Hpsi]]. 
  set e2 := pos_div_2 e ; set e4 := pos_div_2 e2 ; 
  case: (lub e4) => {lub} ub _ ; case: (glb e2) => {glb} lb _.
  
  case: (ex_RInt_correct_4 f a b Hri e4) => {Hri} n Hri.
  apply Rbar_finite_le ; replace g with ((g-e2)+e2) by ring ;
  replace (l+eps) with (((l+e4)+e4)+e2).
  apply (Rbar_plus_le_compat (Finite _) (Finite _) (Finite e2) (Finite e2)) ;
  try by right.
  left ; apply (Rbar_lt_le_trans (Finite (g - e2)) (RInt_sup f a b n)) with (1 := lb n).
  apply Rbar_le_trans with (1 := Hri).
  apply (Rbar_plus_lt_le_compat _ (Finite _) (Finite _) (Finite _)) ;
  try by right.
  apply ub.
  simpl ; field.
  
  set e2 := pos_div_2 e ; 
  case: (lub e2) => {lub} _ [Nl lub] ; case: (glb e2) => {glb} _ [Ng glb].
  replace l with ((l-e2)+e2) by ring ; replace (g+eps) with ((g+e2)+e2) ;
  try apply Rplus_le_compat_r, Rlt_le.
  apply (Rbar_lt_trans (Finite (l-e2)) _ (Finite (g+e2))) with (1 := lub).
  apply (Rbar_le_lt_trans _ _ (Finite (g+e2))) with (2 := glb).
  case: (le_dec Nl Ng) => Hn.
  apply Rbar_le_trans with (2 := RInt_inf_le_sup _ _ _ _) ;
  by apply RInt_inf_incr.
  apply not_le, lt_le_weak in Hn.
  apply Rbar_le_trans with (1 := RInt_inf_le_sup _ _ _ _) ;
  by apply RInt_sup_decr.
  simpl ; field.
Qed.

(** * The RInt function *)

Lemma ex_RInt_cv (f : R -> R) (a b : R) : 
  ex_RInt f a b -> ex_lim_seq (RInt_val f a b).
Admitted.

Definition RInt (f : R -> R) (a b : R) := 
  match Rle_dec a b with
    | left _ => Lim_seq (RInt_val f a b)
    | right _ => -Lim_seq (RInt_val f b a)
  end.

Lemma RInt_correct (f : R -> R) (a b : R) :
  forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab] pr.
    case: (Rle_lt_dec a b) => Hab //.
    by apply Hw.
    rewrite (RiemannInt_P8 _ (RiemannInt_P1 pr)).
    rewrite -(Hw _ _ (Rlt_le _ _ Hab)).
    move: (Rlt_le _ _ Hab) (Rlt_not_le _ _ Hab) ; rewrite /RInt ; 
    case: Rle_dec ; case: Rle_dec => // _ _ _ _.
  set Hex := (ex_RInt_correct_3 f a b pr) ;
  rewrite (RiemannInt_P5 pr (ex_RInt_correct_2 f a b Hex)).
  rewrite /RInt /RiemannInt => /= ; case: RiemannInt_exists => l /= Hl.
  case: Rle_dec => // _ ; apply Lim_seq_rw => /= eps. 
  set e2 := pos_div_2 eps ; set e4 := pos_div_2 e2.
  case: (Hl _ (cond_pos e2)) => {Hl} Naux Hl.
  move: (Hl Naux (le_refl Naux)) => {Hl} ; rewrite /R_dist.
  rewrite /phi_sequence /ex_RInt_correct_2 ; 
  case: ex_RInt_correct_1 => N HN /= Hl.
  
  case: (ex_RInt_correct_1 f a b e4 Hex) => N0 HN0.

  exists (N + N0)%nat => n Hn ; rewrite RInt_val_correct.

  replace (RiemannInt_SF (sf_SF_val_fun f a b n) - l) 
    with ((RiemannInt_SF (sf_SF_val_fun f a b n) - (RiemannInt_SF (sf_SF_val_fun f a b N))
      + (RiemannInt_SF (sf_SF_val_fun f a b N) - l))) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite (double_var eps) ; apply Rplus_lt_compat with (2 := Hl).
  replace (RiemannInt_SF (sf_SF_val_fun f a b n) -
    RiemannInt_SF (sf_SF_val_fun f a b N)) with
    (RiemannInt_SF (sf_SF_val_fun f a b n) + (-1)*
    RiemannInt_SF (sf_SF_val_fun f a b N)) by ring.
  rewrite -StepFun_P30.
  apply Rle_lt_trans with (1 := StepFun_P34 _ Hab) => /=.
  
  have: (forall n, (N0 <= n)%nat -> Rabs (RiemannInt_SF (SF_psi_r f a b n)) < e4).
    move => n0 Hn0 ; apply Rle_lt_trans with (2 := HN0).

    have Rw : (forall n, 0 <= RiemannInt_SF (SF_psi_r f a b n)).
      move => n1 ; rewrite -(Rmult_0_l (b-a)) -StepFun_P18.
      apply StepFun_P37 => //= x Hx.
      apply ->Rminus_le_0 ; apply Rbar_finite_le.
      rewrite /SF_inf_fun /SF_sup_fun ; case: Rle_dec => //_.
      move: (SF_fun_incr (SF_inf_seq f a b n1) (Finite 0) x) 
            (SF_fun_incr (SF_sup_seq f a b n1) (Finite 0) x).
        rewrite SF_inf_lx SF_sup_lx => Hi Hs.
      have Hx0 : head 0 (RInt_part a b n1) <= x <= last 0 (RInt_part a b n1).
        rewrite -nth0 -nth_last size_mkseq ?nth_mkseq //= pow2_INR.
        replace (a + 0 * (b - a) / 2 ^ n1) with a.
        replace (a + 2 ^ n1 * (b - a) / 2 ^ n1) with b.
        intuition.
        field ; apply Rgt_not_eq ; intuition.
        field ; apply Rgt_not_eq ; intuition.
      move: (Hi (RInt_part_sort a b n1 Hab) Hx0) 
        (Hs (RInt_part_sort a b n1 Hab) Hx0) => {Hi Hs} -> ->.
      case: sorted_dec => {Hx0} [[i [Hx0 Hi]]| Hx0] ; simpl projT1.
      rewrite SF_sup_ly SF_inf_ly ?nth_behead ?(nth_pairmap (0)).
      replace (nth 0 (0 :: RInt_part a b n1) (S i))
      with (nth 0 ( RInt_part a b n1) (i)) by auto.

Admitted.

Lemma RInt_ext (f g : R -> R) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) -> RInt f a b = RInt g a b.
Proof.
  move => Hf ; rewrite /RInt /RInt_val.
Admitted.

(** * Riemann integral and derivative *)

Lemma derivable_pt_lim_RInt (f : R -> R) (a : R) (x : R) :
  ex_RInt f a x -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x -> derivable_pt_lim (fun x => RInt f a x) x (f x).
Proof.
Admitted. (** Admitted. *)

Lemma RInt_Derive (f : R -> R) (a b : R) (eps : posreal) :
  (forall x, Rmin a b - eps <= x <= Rmax a b + eps -> ex_derive f x) ->
  continuity_pt (Derive f) a -> continuity_pt (Derive f) b ->
  RInt (Derive f) a b = f b - f a.
Proof.
Admitted. (** Admitted. *)
