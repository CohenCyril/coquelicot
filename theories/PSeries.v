Require Import Reals Even Div2 ssreflect.
Require Import Lim_seq Floor Rcomplements Rbar_theory Sup_seq Total_sup.

Definition Zpow (x : R) (n : Z) : R :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ (nat_of_P p)
    | Zneg p => / x ^ (nat_of_P p)
  end.

Fixpoint is_even (n : nat) :=
  match n with
    | O => 1
    | 1%nat => 0
    | S (S n) => is_even n
  end.
Definition is_odd (n : nat) := is_even (S n).

Lemma is_even_simplify (n : nat) :
  is_even n = match (even_odd_dec n) with
    | left _ => 1
    | right _ => 0
  end.
Proof.
  move: n ; apply ind_0_1_SS => // n Hn.
  simpl.
  by case: (even_odd_dec n) Hn => /=.
Qed.

(** * Series *)

Definition is_series (a : nat -> R) (l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k)) l.
Definition ex_series (a : nat -> R) :=
  ex_lim_seq (sum_f_R0 (fun k => a k)).
Definition Series (a : nat -> R) : R :=
  Lim_seq (sum_f_R0 (fun k => a k)).

Lemma is_series_equiv (a : nat -> R) (l : R) :
  is_series a l <-> infinite_sum a l.
Proof.
  split => H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 a n) with (sum_f_R0 (fun k : nat => a k) n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a k) n) with (sum_f_R0 a n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.
Lemma ex_series_equiv_0 (a : nat -> R) :
  ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
  move => H ;
  exists (Series a) ;
  apply Lim_seq_correct in H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 a n) with (sum_f_R0 (fun k : nat => a k) n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.
Lemma ex_series_equiv_1 (a : nat -> R) :
  { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l } -> ex_series a.
Proof.
  case => l H.
  exists l.
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a k) n) with (sum_f_R0 a n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.

(** ** Convergence theorems *)

(** Cauchy Criterion *)

Lemma Cauchy_ex_pseries (a : nat -> R) :
  ex_series a <-> (Cauchy_crit_series a).
Proof.
  split => Hcv.
  by apply cv_cauchy_1, ex_series_equiv_0.
  by apply ex_series_equiv_1, cv_cauchy_2.
Qed.

(** Absolute convergence *)

Lemma Abs_ex_series (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) -> ex_series a.
Proof.
  move => H.
  apply Cauchy_ex_pseries.
  apply cauchy_abs.
  by apply Cauchy_ex_pseries.
Qed.

(** D'Alembert criterium *)

Lemma DAlembert_ex_series (a : nat -> R) (k : R) :
  k < 1 -> (forall n, a n <> 0) 
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) k
      -> ex_series a.
Proof.
  move => Hk Ha H.
  apply ex_series_equiv_1.
  apply Alembert_C5 with k.
  split.
  apply Rnot_lt_le => Hk0.
  apply Ropp_0_gt_lt_contravar in Hk0.
  case: (H (mkposreal _ Hk0)) => /= {H} N H.
  move: (H N (le_refl _)).
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rminus_le_0 ; ring_simplify.
  apply Rabs_pos.
  by apply Hk.
  by apply Ha.
  move => e He ; case: (H (mkposreal _ He)) => /= {H} N H ; by exists N.
Qed.

(** Comparison *)

Lemma Comp_ex_series (a b : nat -> R) :
   (forall n : nat, 0 <= a n <= b n) ->
   ex_series b -> ex_series a.
Proof.
  move => H Hb.
  apply ex_series_equiv_1.
  apply Rseries_CV_comp with b.
  by apply H.
  by apply ex_series_equiv_0.
Qed.

(** Comming soon : alternated series *)

(** ** Operations *)
(** Extentionality *)

Lemma is_series_ext (a b : nat -> R) (l : R) :
  (forall n, a n = b n) -> (is_series a l) 
    -> is_series b l.
Proof.
  move => Heq Ha.
  apply is_lim_seq_ext with (2 := Ha).
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.
Lemma ex_series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> ex_series a
    -> ex_series b.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_series_ext with a.
Qed.
Lemma Series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> Series a = Series b.
Proof.
  move => Heq.
  apply Lim_seq_ext.
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.

(** * Power series *)
(** A new definition using our limits *)

Definition is_pseries (a : nat -> R) (x l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k * x ^ k)) l.
Definition ex_pseries (a : nat -> R) (x : R) :=
  ex_lim_seq (sum_f_R0 (fun k => a k * x ^ k)).
Definition PSeries (a : nat -> R) (x : R) : R :=
  Lim_seq (sum_f_R0 (fun k => a k * x ^ k)).

(** This new formalisation is equivalent with standard library *)

Lemma is_pseries_equiv (a : nat -> R) (x l : R) :
  is_pseries a x l <-> Pser a x l.
Proof.
  split => H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => {H} N H.
  exists N => n Hn.
  by apply H.
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  by apply H.
Qed.

(** ** Domain of definition *)
(** A power series is always defined at 0 *)
Lemma is_pseries_0 (a : nat -> R) :
  is_pseries a 0 (a O).
Proof.
  apply is_lim_seq_ext with (fun _ => a O).
  elim => [ | n IH] /=.
  ring.
  rewrite -IH ; ring.
  by apply is_lim_seq_const.
Qed.
Lemma ex_pseries_0 (a : nat -> R) :
  ex_pseries a 0.
Proof.
  exists (a O) ; by apply is_pseries_0.
Qed.
Lemma PSeries_0 (a : nat -> R) :
  PSeries a 0 = a O.
Proof.
  by apply is_lim_seq_unique, is_pseries_0.
Qed.

(** Convergence circle *)

Definition CV_circle_set (a : nat -> R) (r : R) :=
  0 <= r /\ ex_pseries (fun n => Rabs (a n)) r.

Lemma CV_circle_pty1 (a : nat -> R) (r1 r2 : R) :
  0 <= r1 <= r2 -> CV_circle_set a r2 -> CV_circle_set a r1.
Proof.
  move => H H0 ; split.
  by apply H.
  move: (proj2 H0) => {H0}.
  apply Comp_ex_series => n ; split.
  apply Rmult_le_pos.
  by apply Rabs_pos.
  by apply pow_le, H.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  by apply pow_incr, H.
Qed.
Lemma CV_circle_pty2 (a : nat -> R) (x : R) :
  CV_circle_set a (Rabs x) -> ex_pseries a x.
Proof.
  move => [Hx Ha].
  apply Abs_ex_series.
  move: Ha ; apply ex_series_ext => n.
  by rewrite Rabs_mult RPow_abs.
Qed.

Lemma CV_circle_ne (a : nat -> R) :
  exists x, (CV_circle_set a) x.
Proof.
  exists 0.
  split.
  by apply Rle_refl.
  by apply ex_pseries_0.
Qed.
Definition CV_circle (a : nat -> R) : Rbar :=
  Lub_Rbar_ne (CV_circle_set a) (CV_circle_ne a).

Lemma CV_circle_carac (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a)
    -> ex_pseries a x.
Proof.
  move => Ha.
  have H : ~ ~ ex_pseries a x.
    contradict Ha.
    apply Rbar_le_not_lt.
    rewrite /CV_circle /Lub_Rbar_ne.
    case: ex_lub_Rbar_ne => l /= [ub lub].
    apply: lub => r Hr.
    apply Rbar_finite_le.
    apply Rnot_lt_le ; contradict Ha.
    apply CV_circle_pty2.
    move: (Hr).
    apply CV_circle_pty1.
    split.
    by apply Rabs_pos.
    by apply Rlt_le.
  by case: (ex_lim_seq_dec (sum_f_R0 (fun k : nat => a k * x ^ k))).
Qed.

(** ** Convergence criterion *)

(** D'Alembert Criterion for power series *)

Lemma Alembert_crit (a : nat -> R) (x:R) l :
  (forall n:nat, a n <> 0) ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  (l = 0 \/ (l <> 0 /\ Rabs x < / l)) -> ex_pseries a x.
Proof.
  move => Ha Hl ; case => H.
  rewrite H in Hl => {l H}.
  case: (Alembert_C3 a x Ha).
  move => e He ; 
  set eps := mkposreal e He ;
  case: (Hl eps) => {Hl} N Hl.
  exists N => n Hn.
  by apply Hl.
  move => s Hs ; exists s ; by apply is_pseries_equiv.
  case: (Alembert_C6 a x l).
  rewrite -(Rinv_involutive l).
  apply Rinv_0_lt_compat.
  apply Rle_lt_trans with (1 := Rabs_pos x).
  by apply H.
  by apply H.
  by apply Ha.
  move => e He ; 
  set eps := mkposreal e He ;
  case: (Hl eps) => {Hl} N Hl.
  exists N => n Hn.
  by apply Hl.
  by apply H.
  move => s Hs ; exists s ; by apply is_pseries_equiv.
Qed.

Lemma DAlembert_CV_circle_neq_0 (a : nat -> R) (l : R) :
  (forall n:nat, a n <> 0) -> l <> 0 ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  CV_circle a = Finite (/l).
Proof.
Admitted. (** Admitted *)
Lemma DAlembert_CV_circle_eq_0 (a : nat -> R) :
  (forall n:nat, a n <> 0) -> 
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) 0 ->
  CV_circle a = p_infty.
Admitted. (** Admitted *)

(** Comming soon
  - convergence circle *)

(** * Operations *)
(** Extentionality *)

Lemma is_pseries_ext (a b : nat -> R) (x l : R) :
  (forall n, a n = b n) -> (is_pseries a x l) 
    -> is_pseries b x l.
Proof.
  move => Heq Ha.
  apply is_lim_seq_ext with (2 := Ha).
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.
Lemma ex_pseries_ext (a b : nat -> R) (x : R) :
  (forall n, a n = b n) -> ex_pseries a x
    -> ex_pseries b x.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_pseries_ext with a.
Qed.
Lemma PSeries_ext (a b : nat -> R) (x : R) :
  (forall n, a n = b n) -> PSeries a x = PSeries b x.
Proof.
  move => Heq.
  apply Lim_seq_ext.
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.

(** Addition of two power series *)

Definition PS_plus (a b : nat -> R) (n : nat) : R :=
  a n + b n.
Lemma is_pseries_plus (a b : nat -> R) (x la lb : R) :
  is_pseries a x la -> is_pseries b x lb
    -> is_pseries (PS_plus a b) x (la + lb).
Proof.
  move => Ha Hb.
  apply is_lim_seq_ext 
    with (fun n => (sum_f_R0 (fun k => a k * x ^ k) n) + (sum_f_R0 (fun k => b k * x ^ k) n)).
  elim => [ | n IH].
  simpl ; rewrite /PS_plus ; ring.
  simpl ; rewrite -IH /PS_plus ; ring.
  by apply is_lim_seq_plus with la lb.
Qed.
Lemma ex_pseries_plus (a b : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries b x
    -> ex_pseries (PS_plus a b) x.
Proof.
  move => [la Ha] [lb Hb].
  exists (la + lb).
  by apply is_pseries_plus.
Qed.
Lemma PSeries_plus (a b : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries b x
    -> PSeries (PS_plus a b) x = PSeries a x + PSeries b x.
Proof.
  intros Ha Hb.
  apply is_lim_seq_unique, is_pseries_plus ;
  by apply Lim_seq_correct.
Qed.

(** Scalar multiplication *)

Definition PS_scal (c : R) (a : nat -> R) (n : nat) : R :=
  c * a n.
Lemma is_pseries_scal (c : R) (a : nat -> R) (x l : R) :
  is_pseries a x l -> is_pseries (PS_scal c a) x (c * l).
Proof.
  move => Ha.
  apply is_lim_seq_ext with (fun n => c * (sum_f_R0 (fun k => a k * x ^ k) n)).
  elim => [ | n IH].
  simpl ; rewrite /PS_scal ; ring.
  simpl ; rewrite -IH /PS_scal ; ring.
  by apply is_lim_seq_scal.
Qed.
Lemma ex_pseries_scal (c : R) (a : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries (PS_scal c a) x.
Proof.
  move => [l Ha].
  exists (c * l).
  by apply is_pseries_scal.
Qed.
Lemma PSeries_scal (c : R) (a : nat -> R) (x : R) :
  PSeries (PS_scal c a) x = c * PSeries a x.
Proof.
  rewrite -Lim_seq_scal.
  apply Lim_seq_ext.
  elim => [ | n IH].
  simpl ; rewrite /PS_scal ; ring.
  simpl ; rewrite IH /PS_scal ; ring.
Qed.

(** Multiplication and division by a variable *)

Definition PS_incr_1 (a : nat -> R) (n : nat) : R :=
  match n with
    | 0 => 0
    | S n => a n
  end.
Lemma is_pseries_incr_1 (a : nat -> R) (x l : R) :
  is_pseries a x l -> is_pseries (PS_incr_1 a) x (x * l).
Proof.
  move => Ha.
  move: (is_lim_seq_scal _ x l Ha) => {Ha} Ha.
  apply is_lim_seq_decr in Ha.
  apply is_lim_seq_ext with (2 := Ha).
  case.
  simpl ; ring.
  elim => /= [ | n IH].
  ring.
  rewrite -IH ; ring.
Qed.
Lemma ex_pseries_incr_1 (a : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries (PS_incr_1 a) x.
Proof.
  move => [l Ha] ; exists (x * l) ; by apply is_pseries_incr_1.
Qed.
Lemma PSeries_incr_1 a x :
  PSeries (PS_incr_1 a) x = x * PSeries a x.
Proof.
  rewrite -Lim_seq_scal.
  rewrite -Lim_seq_decr /=.
  apply Lim_seq_ext.
  case.
  simpl ; ring.
  elim => /= [ | n IH].
  ring.
  rewrite IH ; ring.
Qed.

Fixpoint PS_incr_n (a : nat -> R) (n k : nat) : R :=
  match n with
    | O => a k
    | S n => PS_incr_1 (PS_incr_n a n) k
  end.
Lemma PS_incr_n_simplify (a : nat -> R) (n k : nat) :
  PS_incr_n a n k = 
  match (le_lt_dec n k) with
    | left _ => a (k-n)%nat
    | right _ => 0
  end.
Proof.
  case: le_lt_dec => H.
  elim: n k H => [ | n IH] k H.
  rewrite /PS_incr_n ; by case: k H.
  case: k H => [ | k] H.
  by apply le_Sn_0 in H.
  rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
  rewrite IH.
  apply f_equal.
  by elim: n k H {IH} => /= [ | n IH] k H.
  by apply le_S_n.
  elim: n k H => [ | n IH] k H.
  by apply lt_n_O in H.
  rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
  case: k H => [ | k] H.
  by [].
  by apply IH, lt_S_n.
Qed.
Lemma is_pseries_incr_n (a : nat -> R) (n : nat) (x l : R) :
  is_pseries a x l -> is_pseries (PS_incr_n a n) x (x^n * l).
Proof.
  move => Ha.
  elim: n => /= [ | n IH].
  by rewrite Rmult_1_l.
  rewrite Rmult_assoc.
  by apply is_pseries_incr_1.
Qed.
Lemma ex_pseries_incr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x -> ex_pseries (PS_incr_n a n) x.
Proof.
  move => [l Ha].
  exists (x^n*l) ; by apply is_pseries_incr_n.
Qed.
Lemma PSeries_incr_n (a : nat -> R) (n : nat) (x : R) :
  PSeries (PS_incr_n a n) x = x^n * PSeries a x.
Proof.
  elim: n => /= [ | n IH].
  by rewrite Rmult_1_l.
  rewrite Rmult_assoc.
  by rewrite PSeries_incr_1 IH.
Qed.

Definition PS_decr_1 (a : nat -> R) (n : nat) : R :=
  a (S n).
Lemma is_pseries_decr_1 (a : nat -> R) (x l : R) :
  x <> 0 -> is_pseries a x l 
    -> is_pseries (PS_decr_1 a) x ((l - a O) / x).
Proof.
  move => Hx Ha eps.
  have He : 0 < eps * Rabs x.
    apply Rmult_lt_0_compat.
    by apply eps.
    by apply Rabs_pos_lt.
  case: (Ha (mkposreal _ He)) => /= {Ha} N Ha.
  exists N => n Hn.
  rewrite /PS_decr_1.
  replace (sum_f_R0 (fun k : nat => a (S k) * x ^ k) n - (l - a 0%nat) / x)
    with ((sum_f_R0 (fun k : nat => a k * x ^ k) (S n) - l)/x).
  Focus 2.
    elim: n {Hn} => /= [ | n IH].
    by field.
    rewrite /Rminus (Rplus_assoc (sum_f_R0 (fun k : nat => a (S k) * x ^ k) n)).
    rewrite (Rplus_comm (a (S (S n)) * (x * x ^ n))).
    rewrite -(Rplus_assoc (sum_f_R0 (fun k : nat => a (S k) * x ^ k) n)).
    rewrite /Rminus in IH ; rewrite -IH.
    by field.
  rewrite Rabs_div.
  apply Rlt_div.
  by apply Rabs_pos_lt.
  apply Ha ; by intuition.
  by [].
Qed.
Lemma ex_pseries_decr_1 (a : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries (PS_decr_1 a) x.
Proof.
  move => [l Ha].
  case: (Req_dec x 0) => Hx.
  rewrite Hx ; by apply ex_pseries_0.
  exists ((l-a O)/x) ; by apply is_pseries_decr_1.
Qed.
Lemma PSeries_decr_1 (a : nat -> R) (x : R) :
  ex_pseries a x 
    -> PSeries a x = a O + x * PSeries (PS_decr_1 a) x.
Proof.
  move => Ha.
  case: (Req_dec x 0) => Hx.
  rewrite Hx PSeries_0 ; ring.
  move: (is_pseries_decr_1 a x (PSeries a x) Hx (Lim_seq_correct _ Ha)) => Hb.
  rewrite {2}/PSeries (is_lim_seq_unique _ _ Hb).
  by field.
Qed.
Lemma PSeries_decr_1_aux (a : nat -> R) (x : R) :
  a O = 0 -> (PSeries a x) = x * PSeries (PS_decr_1 a) x.
Proof.
  intros Ha0.
  rewrite -PSeries_incr_1.
  rewrite /PS_incr_1 /PS_decr_1 /=.
  apply Lim_seq_ext.
  elim => [ | n IH] /=.
  by rewrite Ha0.
  by rewrite IH.
Qed.

Definition PS_decr_n (a : nat -> R) (n k : nat) : R :=
  a (n + k)%nat.
Lemma is_pseries_decr_n (a : nat -> R) (n : nat) (x l : R) :
  x <> 0 -> (0 < n)%nat -> is_pseries a x l 
    -> is_pseries (PS_decr_n a n) x ((l - sum_f_R0 (fun k => a k * x^k) (n-1)%nat)/x^n).
Proof.
  move => Hx Hn Ha.
  case: n Hn => [ | n] Hn.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl ; rewrite -minus_n_O /PS_decr_n /=.
  elim: n => /= [ | n IH].
  rewrite ?Rmult_1_r.
  by apply is_pseries_decr_1.
  set ln := ((l - sum_f_R0 (fun k : nat => a k * x ^ k) n) / (x * x ^ n)) ;
  rewrite -/ln in IH.
  replace ((l - (sum_f_R0 (fun k : nat => a k * x ^ k) n + a (S n) * (x * x ^ n))) /
    (x * (x * x ^ n))) with ((ln - a (S (n + 0)))/x).
  move: (is_pseries_decr_1 (fun k : nat => a (S (n + k))) x ln Hx IH).
  rewrite /PS_decr_1 /=.
  apply is_pseries_ext => k.
  apply f_equal ; ring.
  rewrite /ln plus_0_r ; field ; split.
  by apply pow_nonzero.
  by [].
Qed.
Lemma ex_pseries_decr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x -> ex_pseries (PS_decr_n a n) x.
Proof.
  move => Ha.
  elim: n => [ | n IH].
  move: Ha ; apply ex_pseries_ext => n ; by rewrite /PS_decr_n.
  move: (ex_pseries_decr_1 _ _ IH).
  apply ex_pseries_ext => k.
  rewrite /PS_decr_1 /PS_decr_n.
  apply f_equal ; ring.
Qed.
Lemma PSeries_decr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x
    -> PSeries a x = sum_f_R0 (fun k => a k * x^k) n + x^(S n) * PSeries (PS_decr_n a (S n)) x.
Proof.
  move => Ha.
  case: (Req_dec x 0) => Hx.
  rewrite Hx PSeries_0 ; simpl ; ring_simplify.
  elim: n => /= [ | n IH].
  ring.
  rewrite -IH ; ring.
  move: (is_pseries_decr_n a (S n) x (PSeries a x) Hx (lt_0_Sn _) (Lim_seq_correct _ Ha)) => Hb.
  rewrite {2}/PSeries (is_lim_seq_unique _ _ Hb).
  simpl ; rewrite -minus_n_O ; field.
  split.
  by apply pow_nonzero.
  by [].
Qed.
Lemma PSeries_decr_n_aux (a : nat -> R) (n : nat) (x : R) :
  (forall k : nat, (k < n)%nat -> a k = 0) 
    -> PSeries a x = x^n * PSeries (PS_decr_n a n) x.
Proof.
  elim: n => /= [ | n IH] Ha.
  rewrite Rmult_1_l.
  apply PSeries_ext => n ; by intuition.
  rewrite IH.
  rewrite PSeries_decr_1_aux.
  rewrite (Rmult_comm _ (x^n)) Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  apply PSeries_ext => k ; rewrite /PS_decr_1 /PS_decr_n ; by intuition.
  apply Ha ; by intuition.
  move => k Hk.
  apply Ha ; by intuition.
Qed.

(** Sums on even and odd *)

Lemma is_pseries_odd_even (a : nat -> R) (x l1 l2 : R) :
  is_pseries (fun n => a (2*n)%nat) (x^2) l1 -> is_pseries (fun n => a (2*n+1)%nat) (x^2) l2
    -> is_pseries a x (l1 + x * l2).
Proof.
rewrite /is_pseries.
  move => H1 H2.
  apply is_lim_seq_ext with (fun n => 
    (sum_f_R0 (fun k : nat => a (2 * k)%nat * (x ^ 2) ^ k) (div2 n)) +
    x * match n with | O => 0 
    | S n => (sum_f_R0 (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 n)) end).
  case => [ | n].
  simpl ; ring.
  case: (even_odd_dec n) => Hn.
(* even n *)
  rewrite -(even_div2 _ Hn) {3}(even_double _ Hn).
  elim: (div2 n) => {n Hn} [ | n] ;
  rewrite ?double_S /sum_f_R0 -/sum_f_R0.
  rewrite /double /= ; ring.
  rewrite -pow_mult.
  replace (2 * S n)%nat with (S (S (double n))) 
    by (rewrite -double_S /double ; ring).
  replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
  move => <- ; simpl ; ring.
(* odd n *)
  rewrite -(odd_div2 _ Hn) {3}(odd_double _ Hn).
  elim: (div2 n) => {n Hn} [ | n] ;
  rewrite ?double_S /sum_f_R0 -/sum_f_R0.
  rewrite /double /= ; ring.
  rewrite -?pow_mult.
  replace (2 * S n)%nat with (S (S (double n))) 
    by (rewrite -double_S /double ; ring).
  replace (2 * S (S n))%nat with (S (S (S (S (double n))))) 
    by (rewrite -double_S /double ; ring).
  replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
  move => <- ; simpl ; ring.
  apply is_lim_seq_plus with l1 (x*l2).
(* a(2k)x^(2k) *)
  move => eps ; case: (H1 eps) => {H1} N H1.
  exists (double N) => n Hn.
  apply H1.
  case: (even_odd_dec n) => Hn'.
  rewrite (even_double _ Hn') in Hn.
  elim: (div2 n) N Hn {H1 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
  rewrite (odd_double _ Hn') in Hn.
  elim: (div2 n) N Hn {H1 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_S_n, le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
(* a(2k+1)x^(2k+1) *)
  apply is_lim_seq_scal.
  move => eps ; case: (H2 eps) => {H1 H2} N H2.
  exists (S (double N)) => n Hn.
  case: n Hn => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  apply H2.
  case: (even_odd_dec n) => Hn'.
  rewrite (even_double _ Hn') in Hn.
  elim: (div2 n) N Hn { H2 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_S_n, le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
  rewrite (odd_double _ Hn') in Hn.
  elim: (div2 n) N Hn {H2 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_S_n, le_S_n, le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
  by [].
Qed.
Lemma ex_pseries_odd_even (a : nat -> R) (x : R) :
  ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2)
    -> ex_pseries a x.
Proof.
  move => [l1 H1] [l2 H2].
  exists (l1 + x * l2).
  by apply is_pseries_odd_even.
Qed.
Lemma PSeries_odd_even (a : nat -> R) (x : R) :
  ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2)
    -> PSeries a x = PSeries (fun n => a (2*n)%nat) (x^2) + x * PSeries (fun n => a (2*n+1)%nat) (x^2).
Proof.
  move => H1 H2 ;
  apply is_lim_seq_unique.
  apply is_pseries_odd_even ; by apply Lim_seq_correct.
Qed.

(** Coming soon: (* bonus *)
  - multiplication
  - composition
  - inverse *)

(** * Differentiability and Integrability *)
(** Coming soon *) (* bonus *)

(** * Bessel functions *)

Definition Bessel1_seq (n k : nat) :=
  is_even k * (-1)^(div2 k)/(INR (fact (div2 k)) * INR (fact (n + (div2 k)))).
Lemma ex_Bessel1 (n : nat) (x : R) :
  ex_pseries (Bessel1_seq n) x.
Proof.
  apply ex_pseries_odd_even.
  have H : forall n0 : nat, Bessel1_seq n (2 * n0) <> 0.
    move => m.
    rewrite /Bessel1_seq.
    replace (is_even _) with 1.
    replace ((-1)^_) with ((-1)^m).
    rewrite Rmult_1_l.
    apply Rmult_integral_contrapositive_currified.
    apply pow_nonzero, Ropp_neq_0_compat, R1_neq_R0.
    apply Rinv_neq_0_compat, Rmult_integral_contrapositive_currified ;
    apply INR_fact_neq_0.
    apply (f_equal (fun n => (-1)^n)).
    replace (2 * m)%nat with (double m).
    elim: m => [ | m IH].
    by [].
    by rewrite double_S /= {1}IH.
    rewrite /double /= ; ring.
    replace (2 * m)%nat with (double m).
    elim: m => [ | m IH].
    by [].
    by rewrite double_S /= {1}IH.
    rewrite /double /= ; ring.
  apply Alembert_crit with 0.
  by apply H.
  move => eps.
  have H0 : 0 <= /(sqrt eps).
    apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0, eps.
  set N := nfloor (/(sqrt eps)) H0.
  exists N => k Hk.
  rewrite Rminus_0_r Rabs_Rabsolu Rabs_div.
  have H2 : forall m, div2 (2*m) = m.
    elim => [ | m IH].
    by [].
    replace (2 * S m)%nat with (S(S(2*m))) by ring.
    simpl ; by rewrite IH.
  rewrite 2?Rabs_div ?Rabs_mult -?RPow_abs ?Rabs_Ropp ?Rabs_R1 
    ?pow1 ?(Rabs_pos_eq _ (pos_INR _)) ?H2.
  have H1 : forall m, is_even (2*m) = 1.
    elim => [ | m IH].
    by [].
    replace (2 * S m)%nat with (S(S(2*m))) by ring.
    simpl ; by rewrite IH.
  rewrite ?H1 Rabs_R1 /Rdiv ?Rmult_1_l.
  rewrite Rinv_involutive.
  rewrite -plus_n_Sm.
  rewrite /fact -/fact ?mult_INR.
  field_simplify ; rewrite -?Rdiv_1 /Rdiv ?Rmult_1_l.
  rewrite Rinv_mult_distr.
  rewrite -(sqrt_sqrt eps (Rlt_le _ _ (cond_pos eps))).
  apply Rmult_gt_0_lt_compat ; try by intuition.
  apply sqrt_lt_R0, eps.
  rewrite -(Rinv_involutive (sqrt eps)).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; try by intuition.
  apply Rinv_0_lt_compat, sqrt_lt_R0, eps.
  apply Rlt_le_trans with (INR (S N)).
  rewrite /N /nfloor in Hk |- * ;
  case: nfloor_ex Hk => {N} /= N HN Hk ; rewrite -/(INR (S N)) S_INR.
  by apply HN.
  by apply le_INR, le_n_S.
  apply Rgt_not_eq, sqrt_lt_R0, eps.
  rewrite -(Rinv_involutive (sqrt eps)).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; try by intuition.
  apply Rinv_0_lt_compat, sqrt_lt_R0, eps.
  apply Rlt_le_trans with (INR (S N)).
  rewrite /N /nfloor in Hk |- * ;
  case: nfloor_ex Hk => {N} /= N HN Hk ; rewrite -/(INR (S N)) S_INR.
  by apply HN.
  apply le_INR, le_n_S ; by intuition.
  apply Rgt_not_eq, sqrt_lt_R0, eps.
  apply Rgt_not_eq ; by intuition.
  apply Rgt_not_eq ; by intuition.
  repeat split.
  apply INR_fact_neq_0.
  apply Rgt_not_eq ; by intuition.
  apply INR_fact_neq_0.
  apply Rgt_not_eq ; by intuition.
  apply Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
  apply Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
  apply Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
  by apply H.
  by left.
  apply ex_lim_seq_ext with (2 := ex_lim_seq_const 0).
  elim => [ | m IH] ; rewrite /sum_f_R0 -/sum_f_R0.
  rewrite /Bessel1_seq /= /Rdiv ; ring.
  rewrite -IH /Bessel1_seq.
  replace (is_even _) with 0.
  rewrite /Rdiv ; ring.
  elim: m {IH} => [ | m IH].
  by [].
  replace (2 * S (S m) + 1)%nat with (S(S(2 * S m + 1))) by ring.
  by apply IH.
Qed.
Definition Bessel1 (n : nat) (x : R) :=
  (x/2)^n * PSeries (Bessel1_seq n) (x/2).

Lemma Bessel1_equality (n : nat) (x : R) : (0 < n)%nat -> x<>0
  -> Bessel1 (n+1)%nat x + Bessel1 (n-1)%nat x = (2*INR n)/x * Bessel1 n x.
Proof.
  case: n => [ | n] Hn Hx.
  by apply lt_irrefl in Hn.
  clear Hn.
  replace (S n - 1)%nat with n by (case: n => //=).
  replace (S n + 1)%nat with (S (S n)) by ring.
  rewrite /Bessel1.
  rewrite -Rmult_assoc.
  replace (2 * INR (S n) / x * (x / 2) ^ S n) with (INR (S n) * (x/2)^n)
    by (rewrite /pow -/pow ; field ; apply Hx).
  rewrite Rmult_assoc.
  rewrite -?PSeries_incr_n.
  rewrite -PSeries_scal.
  rewrite -PSeries_plus.
  apply PSeries_ext => k.
Focus 2. (* ex_pseries (PS_incr_n (Bessel1_seq (S (S n))) (S (S n))) (x / 2) *)
  apply ex_pseries_incr_n, ex_Bessel1.
Focus 2. (* ex_pseries (PS_incr_n (Bessel1_seq n) n) (x / 2) *)
  apply ex_pseries_incr_n, ex_Bessel1.
(* egalité *)
  rewrite /PS_plus /PS_scal.
  rewrite ?PS_incr_n_simplify.
  case: (le_lt_dec n k) => H1 ;
  case: (le_lt_dec (S (S n)) k) => H2.
  case: k H2 {H1} => [ | k] H2 ; [ by apply le_Sn_0 in H2 | apply le_S_n in H2].
  case: k H2 => [ | k] H2 ; [ by apply le_Sn_0 in H2 | apply le_S_n in H2].
  replace (S (S k) - S (S n))%nat with (k-n)%nat by (case: n H2 => //).
  replace (S (S k) - n)%nat with (S (S (k-n)))%nat by (rewrite -?minus_Sn_m ; auto).
  rewrite /Bessel1_seq.
  simpl is_even ; rewrite is_even_simplify.
  case: (even_odd_dec (k-n)) => Hnk.
  simpl div2 ; set p := div2 (k - n).
  rewrite /pow -/pow -?plus_n_Sm /fact -/fact ; simpl plus.
  rewrite ?mult_INR -/fact ?S_INR ?plus_INR.
  field.
  rewrite -plus_INR -?S_INR ; repeat split ; 
    try by [apply not_0_INR, sym_not_eq, O_S | apply INR_fact_neq_0].
  rewrite /Rdiv ; ring.
  have Hk : {k = n} + {k = S n}.
    elim: n k H1 H2 => [ | n IH] ;
    case => [ | k] H1 H2.
    by left.
    apply lt_S_n in H2 ; case: k {H1} H2 => [ | k] H2.
    by right.
    by apply lt_S_n, lt_n_O in H2.
    by apply le_Sn_0 in H1.
    apply le_S_n in H1.
    apply lt_S_n in H2.
    case: (IH _ H1 H2) => H.
    left ; by rewrite H.
    right ; by rewrite H.
  case: Hk => -> {k H1 H2}.
  rewrite minus_diag Rplus_0_l.
  rewrite /Bessel1_seq.
  simpl div2 ; simpl is_even ; simpl pow ; simpl (fact 0) ; simpl (INR 1).
  rewrite ?plus_0_r /fact -/fact .
  rewrite mult_INR S_INR ; field.
  rewrite -S_INR ; split ; [apply INR_fact_neq_0 | apply not_0_INR, sym_not_eq, O_S].
  rewrite -minus_Sn_m // minus_diag Rplus_0_l.
  rewrite /Bessel1_seq.
  simpl is_even.
  rewrite /Rdiv ; ring.
  have : False => //.
  move: H1 ; apply le_not_lt ; by intuition.
  ring.
Qed.

(* Fonctions de Bessel du premier ordre (cf: wikipédia)
  - Lire article d'Harrison
  - résoudre égalités avec dérivées *)

(*
(** * Power series for equivalent computation *)

Record PSeries_equiv := mk_pse {ind : Z ; seq : nat -> R}.
Definition PSE_fun (A : PSeries_equiv) (x : R) : R :=
  (seq A 0) * Zpow x (ind A) * (1 + PSeries (seq A) 1 x).

(** ** PSeries_equiv is a field *)

Definition PSE_zero := mk_pse 0 (fun _ => 0).
Lemma PSE_zero_carac (A : PSeries_equiv) :
  seq A 0 = 0 -> forall x, PSE_fun A x = 0.
Proof.
  move => H x.
  by rewrite /PSE_fun H !Rmult_0_l.
Qed.

Definition PSE_one := mk_pse 0 (fun n => match n with | 0 => 1 | _ => 0 end).
Lemma PSE_one_carac :
  forall x, PSE_fun PSE_one x = 1.
Proof.
  move => x.
  rewrite /PSE_fun.
  replace (PSeries (seq PSE_one) 1 x) with 0.
  simpl ; ring.
  apply sym_equal.
  rewrite -(Lim_seq_const 0).
  apply Lim_seq_ext => n.
  rewrite /sum_f.
  case: n => [ | n].
  simpl ; ring.
  rewrite -pred_of_minus ; simpl pred.
  elim: n => [ | n IH] /=.
  ring.
  rewrite IH ; ring.
Qed.

Definition PSE_opp (A : PSeries_equiv) := mk_pse (ind A) (fun n => - seq A n).
Lemma PSE_opp_carac (A : PSeries_equiv) :
  forall x, PSeries *)