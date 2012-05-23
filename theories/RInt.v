Require Import Reals Div2.
Require Import ssreflect ssrbool eqtype seq.
Require Import Arithmetique Floor Total_sup Sup_seq Lim_seq Deriv_fct SF_seq.


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
Definition SF_sup_real (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_map real (SF_sup_seq f a b n).
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
  SF_seq_f2 (Sup_fct f) (RInt_part a b n) 0.
Definition SF_inf_real (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_map real (SF_inf_seq f a b n).
Lemma SF_inf_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_inf_seq f a b n) = RInt_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_inf_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_inf_seq f a b n) = behead (pairmap (Sup_fct f) 0 (RInt_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_sup_seq f a b n) = SF_sup_seq f b a n.
Proof.
  rewrite /SF_sup_seq RInt_part_bound => //.
Search _ SF_rev SF_seq_f2.
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
  rewrite /Sup_fct /Lub_Rbar_ne ; case: (ex_lub_Rbar_ne _ _) => l1 [ub1 lub1] ;
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
Qed.

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
  have H : SF_lx (SF_sup_real f a b n) = RInt_part a b n ;
    [by rewrite /SF_sup_real SF_map_lx SF_sup_lx | rewrite -H].
  have : head 0 (SF_lx (SF_sup_real f a b n)) = a ;
    [rewrite H -nth0 /= ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2 |
    move => {2}<-].
  have : last 0 (SF_lx (SF_sup_real f a b n)) = b ;
    [rewrite H -nth_last size_mkseq nth_mkseq //= pow2_INR ;
    field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2|
    move => {3}<-].
  have H0 : SF_sorted Rle (SF_sup_real f a b n).
    rewrite /SF_sorted H ; by apply RInt_part_sorted_0.
  move : (ad_SF_compat (SF_sup_real f a b n) H0) => H1 ;
  rewrite /adapted_couple ?size_compat ?size_behead ?size_pairmap in H1 |-* ; 
  intuition => x Hx.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => // _ ; rewrite -SF_fun_map ;
  rewrite (H6 i H5 x Hx) ?nth_compat SF_map_ly SF_map_lx SF_sup_ly SF_sup_lx -behead_map.
  rewrite SF_map_lx SF_sup_lx in H5.
  case: (RInt_part a b n) {2 4}(0) (i) H5 => {i Hx} //= h s _ ;
  elim: s h => // h s IH h0 ; case => //= i Hi ; apply IH.
  apply lt_S_n, Hi.
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
  have H : SF_lx (SF_inf_real f a b n) = RInt_part a b n ;
    [by rewrite /SF_inf_real SF_map_lx SF_inf_lx | rewrite -H].
  have : head 0 (SF_lx (SF_inf_real f a b n)) = a ;
    [rewrite H -nth0 /= ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2 |
    move => {2}<-].
  have : last 0 (SF_lx (SF_inf_real f a b n)) = b ;
    [rewrite H -nth_last size_mkseq nth_mkseq //= pow2_INR ;
    field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2|
    move => {3}<-].
  have H0 : SF_sorted Rle (SF_inf_real f a b n).
    rewrite /SF_sorted H ; by apply RInt_part_sorted_0.
  move : (ad_SF_compat (SF_inf_real f a b n) H0) => H1 ;
  rewrite /adapted_couple ?size_compat ?size_behead ?size_pairmap in H1 |-* ; 
  intuition => x Hx.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => // _ ; rewrite -SF_fun_map ;
  rewrite (H6 i H5 x Hx) ?nth_compat SF_map_ly SF_map_lx SF_inf_ly SF_inf_lx -behead_map.
  rewrite SF_map_lx SF_inf_lx in H5.
  case: (RInt_part a b n) {2 4}(0) (i) H5 => {i Hx} //= h s _ ;
  elim: s h => // h s IH h0 ; case => //= i Hi ; apply IH.
  apply lt_S_n, Hi.
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

(** ** SF_sup_r - SF_inf_r *)

Lemma ad_SF_sup_inf_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => SF_sup_r f a b n x - SF_inf_r f a b n x) a b 
      (seq2Rlist (RInt_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => SF_sup_r f a b n x - SF_inf_r f a b n x) a b 
      (seq2Rlist (RInt_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part b a n))))).
Proof.
  wlog: a b /(a <= b) => [Hw | H] ; split ; case: (Rle_dec a b) => // Hab _.
    by apply Hw.
    apply Rnot_le_lt, Rlt_le in Hab.
    case: (Hw b a Hab) => {Hw} Hw _ ; move: (Hw Hab) => {Hw}.
    rewrite /adapted_couple Rmin_comm Rmax_comm ; intuition => x Hx.
    rewrite /SF_sup_r /SF_inf_r /= SF_sup_fun_bound SF_inf_fun_bound ; 
      apply (H4 i H3 x Hx).
  rewrite /adapted_couple ; split.
  by apply sorted_compat, RInt_part_sorted_0.
  rewrite /Rmin /Rmax ?nth_compat ?nth_mkseq ?size_compat ?size_behead ?size_pairmap
  ?size_mkseq ; [case: Rle_dec => // _ 
  | apply SSR_leq ; intuition | apply SSR_leq ; intuition ] ; split.
  simpl ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
  split.
  rewrite /= pow2_INR ; field ; apply Rgt_not_eq, pow_lt, Rlt_R0_R2.
  split => // i Hi x Hx.
  rewrite nth_compat nth_behead (nth_pairmap 0) ; 
  [| rewrite size_mkseq ; apply SSR_leq ; intuition] ;
  apply Rplus_eq_compat ; [|apply Ropp_eq_compat].
  case: (proj1 (ad_SF_sup_r f a b n) Hab) => _ [_ [_ [_ Hs]]] ;
  have Hi' : (i < Peano.pred (Rlength (seq2Rlist (RInt_part a b n))))%nat ;
    [rewrite size_compat size_mkseq => // | ] ;
  move: (Hs i Hi' x Hx) => {Hs Hi'} Hs ;
  rewrite /SF_sup_r /= Hs nth_compat nth_behead (nth_pairmap 0) => // ;
  apply SSR_leq ; rewrite size_mkseq ; intuition.
  case: (proj1 (ad_SF_inf_r f a b n) Hab) => _ [_ [_ [_ Hs]]] ;
  have Hi' : (i < Peano.pred (Rlength (seq2Rlist (RInt_part a b n))))%nat ;
    [rewrite size_compat size_mkseq => // | ] ;
  move: (Hs i Hi' x Hx) => {Hs Hi'} Hs ;
  rewrite /SF_sup_r /= Hs nth_compat nth_behead (nth_pairmap 0) => // ;
  apply SSR_leq ; rewrite size_mkseq ; intuition.
Qed.

Definition SF_sup_inf_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => SF_sup_r f a b n x - SF_inf_r f a b n x) ; 
  case: (Rle_dec a b) => Hab.
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part a b n)))) ;
  by apply ad_SF_sup_inf_r.
  exists (seq2Rlist (RInt_part b a n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part b a n)))) ;
  by apply ad_SF_sup_inf_r.
Defined.
Lemma SF_sup_inf_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_sup_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /SF_sup_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_sup_inf_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_sup_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y) - real (Inf_fct f x y)) 0 (RInt_part b a n))))
  end.
Proof.
  rewrite /SF_sup_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.

(** *)
Lemma SF_sup_finite (f : R -> R) (a b : R) (n : nat) (M : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> f x <= M) ->
  (SF_sup f a b n) = SF_map Finite (SF_sup_real f a b n).
Proof.
Admitted. (** Admitted. *) 

Definition RInt_sup f a b n := 
  Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_sup f a b (S n)))) (mkposreal _ (lt_0_INR _ (lt_O_Sn n))).
Definition RInt_inf f a b n := 
  Rbar_div_pos (foldr Rbar_plus (Finite 0) (SF_ly (SF_inf f a b (S n)))) (mkposreal _ (lt_0_INR _ (lt_O_Sn n))).

Lemma RInt_sup_bound f a b n :
  RInt_sup f a b n = RInt_sup f b a n.
Proof.
Admitted. (** Admitted. *)
Lemma RInt_inf_bound f a b n :
  RInt_inf f a b n = RInt_inf f b a n.
Proof.
Admitted. (** Admitted. *)

(** * A new Riemann_integrable in Prop *)

Definition ex_RInt (f : R -> R) (a b : R) :=
  Rbar_inf_seq (RInt_sup f a b) = Rbar_sup_seq (RInt_inf f a b)
  /\ Finite (real (Rbar_inf_seq (RInt_sup f a b))) = Rbar_inf_seq (RInt_sup f a b).

Lemma ex_RInt_bound (f : R -> R) (a b : R) :
  ex_RInt f a b -> ex_RInt f b a.
Proof.
  rewrite /ex_RInt ; case => H H0 ;
  rewrite (Rbar_inf_seq_rw _ _ (RInt_sup_bound _ _ _)) ;
  rewrite (Rbar_sup_seq_rw _ _ (RInt_inf_bound _ _ _)) ; by split.
Qed.

Lemma ex_RInt_correct_0 (f : R -> R) (a b : R) : ex_RInt f a b -> 
  forall n x, Rmin a b <= x < Rmax a b -> 
    Rabs (f x - SF_val_fun f a b n x) <= SF_sup_inf_r f a b n x.
Proof.
  case => Heq Hr n x Hx.
  apply Rabs_le_encadre ; move: Hx ; 
  rewrite Ropp_minus_distr' /Rmin /Rmax /SF_val_fun /SF_sup_inf_r ; 
  case: Rle_dec => //= Hab Hx ;
  rewrite /SF_inf_fun /SF_sup_fun ; case: Rle_dec => // _.
  case: (RInt_part_nat_0 a b n x Hx) => i [Hx' Hi].
  rewrite ?(SF_fun_incr _ _ _ i) /SF_sorted -?SF_size_ly ?SF_seq_bij_lx ?SF_sup_lx ?SF_inf_lx 
  ?SF_seq_bij_ly ?SF_sup_ly ?SF_inf_ly ?size_belast ?size_behead ?size_map
  ?size_pairmap ?size_mkseq ?size_iota => // ; 
  try by apply RInt_part_sorted_0.
(** big problem !!! *) 
Admitted.

Lemma ex_RInt_correct_1 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
  wlog : a b / (a <= b).
  move => Hgen ; case: (Rle_lt_dec a b) => Hab H.
  by apply Hgen.
  apply Rlt_le in Hab ;
  apply RiemannInt_P1, Hgen => // ; by apply ex_RInt_bound.
  move => Hab Hri eps.
Admitted. (** Admitted. *)
Lemma ex_RInt_correct_1 (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> ex_RInt f a b.
Proof.
  wlog : a b / (a <= b).
  move => Hgen ; case: (Rle_lt_dec a b) => Hab H.
  by apply Hgen.
  apply Rlt_le in Hab ;
  apply  ex_RInt_bound, Hgen => // ; by apply RiemannInt_P1.
Admitted. (** Admitted. *)

(** * The RInt function *)

Definition RInt (f : R -> R) (a b : R) := Lim_seq (RInt_val f a b).

Lemma RInt_correct (f : R -> R) (a b : R) :
  forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
Admitted. (** Admitted. *)

(** * Riemann integral and derivative *)

Lemma Deriv_RInt (f : R -> R) (a : R) (x : R) (eps : posreal) :
  (ex_RInt f a x) -> (ex_RInt f (x-eps) (x+eps)) -> continuity_pt f x ->
  Deriv (RInt f a) x = f x.
Proof.
Admitted. (** Admitted. *)

Lemma RInt_Deriv (f : R -> R) (a b : R) (eps : posreal) :
 (forall x, Rmin a b - eps <= x <= Rmax a b + eps -> ex_deriv f x) ->
   (continuity_pt (Deriv f) a) -> (continuity_pt (Deriv f) b) -> 
     RInt (Deriv f) a b = f b - f a.
Proof.
Admitted. (** Admitted. *)
