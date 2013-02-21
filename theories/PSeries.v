Require Import Reals Even Div2 ssreflect.
Require Import Lim_seq Floor Rcomplements Rbar_theory Sup_seq Total_sup.

(** todo: move this to Rcomplements.v *)

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

Lemma sum_f_rw (a : nat -> R) (n m : nat) :
  (n < m)%nat -> sum_f (S n) m a = sum_f_R0 a m - sum_f_R0 a n.
Proof.
  move => Hnm ; rewrite /sum_f.
  elim: m a n Hnm => [ | m IH] a n Hnm.
  by apply lt_n_O in Hnm.
  rewrite (decomp_sum _ _ (lt_O_Sn _)) /=.
  case: n Hnm => [ | n] Hnm.
  rewrite -minus_n_O /= ; ring_simplify.
  elim: (m) {IH} => /= [ | k IH].
  by [].
  by rewrite -plus_n_Sm plus_0_r IH.
  rewrite (decomp_sum _ _ (lt_O_Sn _)) /= ; ring_simplify.
  apply lt_S_n in Hnm.
  rewrite -(IH _ _ Hnm).
  elim: (m - S n)%nat {IH} => /= [ | k IH].
  by [].
  by rewrite -plus_n_Sm IH.
Qed.

(** * Series *)
(** todo: move to Series.v *)
(** ** Definitions *)

Definition is_series (a : nat -> R) (l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k)) l.
Definition ex_series (a : nat -> R) :=
  ex_lim_seq (sum_f_R0 (fun k => a k)).
Definition Series (a : nat -> R) : R :=
  Lim_seq (sum_f_R0 (fun k => a k)).

Lemma ex_series_dec (a : nat -> R) :
  {ex_series a} + {~ex_series a}.
Proof.
  by apply ex_lim_seq_dec.
Qed.

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

(** Multiplication by a scalar *)

Lemma is_series_scal (c : R) (a : nat -> R) (l : R) :
  is_series a l -> is_series (fun n => c * a n) (c * l).
Proof.
  move => Ha.
  apply is_lim_seq_ext with (fun n => c * (sum_f_R0 (fun k => a k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  by apply is_lim_seq_scal.
Qed.
Lemma ex_series_scal (c : R) (a : nat -> R) :
  ex_series a -> ex_series (fun n => c * a n).
Proof.
  move => [l Ha].
  exists (c * l).
  by apply is_series_scal.
Qed.
Lemma Series_scal (c : R) (a : nat -> R) :
  Series (fun n => c * a n) = c * Series a.
Proof.
  rewrite -Lim_seq_scal.
  apply Lim_seq_ext.
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite IH ; ring.
Qed.

(** Comming soon:
  - addition
  - multiplication *)

(** Decallage d'incice *)

Lemma is_series_incr_1 (a : nat -> R) (l : R) :
  is_series a (l + a O)
    -> is_series (fun k => a (S k)%nat) l.
Proof.
  move => Ha eps.
  case: (Ha eps) => {Ha} N Ha.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a (S k)) n - l)
    with (a O + sum_f_R0 (fun k : nat => a (S k)) (pred (S n)) - (l + a O))
    by (simpl ; ring).
  rewrite -(decomp_sum (fun k => a k)).
  apply (Ha (S n)).
  by intuition.
  by apply lt_O_Sn.
Qed.
Lemma is_series_incr_n (a : nat -> R) (n : nat) (l : R) :
  (0 < n)%nat -> is_series a (l + sum_f_R0 a (pred n))
    -> is_series (fun k => a (n + k)%nat) l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n l Ha => [ | n IH] l Ha.
  by apply is_series_incr_1.
  apply is_series_ext with (fun k : nat => a (S (n + S k))).
    move => k ; apply f_equal ; ring.
  apply is_series_incr_1 with (a := fun k : nat => a (S (n + k))).
  rewrite plus_0_r.
  apply IH.
  by rewrite Rplus_assoc (Rplus_comm (a (S n))).
Qed.

Lemma is_series_decr_1 (a : nat -> R) (l : R) :
  is_series (fun k => a (S k)%nat) (l - a O) -> is_series a l.
Proof.
  move => Ha eps.
  case: (Ha eps) => {Ha} N Ha.
  exists (S N) ; elim => [ | n IH] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  rewrite decomp_sum /=.
  replace (a 0%nat + sum_f_R0 (fun i : nat => a (S i)) n - l) 
    with(sum_f_R0 (fun k : nat => a (S k)) n - (l - a 0%nat)) by ring.
  by apply Ha.
  by apply lt_0_Sn.
Qed.
Lemma is_series_decr_n (a : nat -> R) (n : nat) (l : R) :
  (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (l - sum_f_R0 a (pred n))
    -> is_series a l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n a l Ha => [ | n IH] a l Ha.
  by apply is_series_decr_1.
  apply is_series_decr_1.
  apply IH.
  replace (l - a 0%nat - sum_f_R0 (fun k : nat => a (S k)) n)
    with (l - sum_f_R0 a (S n)).
  by apply Ha.
  rewrite decomp_sum /=.
  ring.
  by apply lt_O_Sn.
Qed.

Lemma ex_series_decal_1 (a : nat -> R) :
  ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
  split ; move => [la Ha].
  exists (la - a O).
  apply is_series_incr_1.
  by ring_simplify (la - a 0%nat + a 0%nat).
  exists (la + a O).
  apply is_series_decr_1.
  by ring_simplify (la + a 0%nat - a 0%nat).
Qed.
Lemma ex_series_decal_n (a : nat -> R) (n : nat) :
  ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
  case: n => [ | n].
  split ; apply ex_series_ext ; by intuition.
  split ; move => [la Ha].
  exists (la - sum_f_R0 a (pred (S n))).
  apply is_series_incr_n.
  by apply lt_O_Sn.
  by ring_simplify (la - sum_f_R0 a (pred (S n)) + sum_f_R0 a (pred (S n))).
  exists (la + sum_f_R0 a (pred (S n))).
  apply is_series_decr_n with (S n).
  by apply lt_O_Sn.
  by ring_simplify (la + sum_f_R0 a (pred (S n)) - sum_f_R0 a (pred (S n))).
Qed.

Lemma Series_decal_1 (a : nat -> R) :
  ex_series a -> Series a = a O + Series (fun k => a (S k)).
Proof.
  move => Ha.
  apply is_lim_seq_unique.
  rewrite Rplus_comm.
  apply is_series_decr_1 ;
  ring_simplify (Series (fun k : nat => a (S k)) + a 0%nat - a 0%nat).
  by apply Lim_seq_correct, (ex_series_decal_1 a).
Qed.
Lemma Series_decal_n (a : nat -> R) (n : nat) :
  (0 < n)%nat -> ex_series a 
    -> Series a = sum_f_R0 a (pred n)  + Series (fun k => a (n + k)%nat).
Proof.
  move => Hn Ha.
  apply is_lim_seq_unique.
  rewrite Rplus_comm.
  apply is_series_decr_n with n.
  by [].
  ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) -
   sum_f_R0 a (pred n)).
  by apply Lim_seq_correct, (ex_series_decal_n a).
Qed.

Lemma Series_decal_1_aux (a : nat -> R) :
  a O = 0 -> Series a = Series (fun k => a (S k)).
Proof.
  move => Ha.
  rewrite /Series.
  rewrite -Lim_seq_incr.
  apply Lim_seq_ext => n.
  rewrite decomp_sum /=.
  rewrite Ha ; by apply Rplus_0_l.
  by apply lt_O_Sn.
Qed.
Lemma Series_decal_n_aux (a : nat -> R) (n : nat) :
   (forall k, (k < n)%nat -> a k = 0) 
     -> Series a = Series (fun k => a (n + k)%nat).
Proof.
  elim: n => [ | n IH] Ha.
  by apply Series_ext => k.
  rewrite IH.
  rewrite Series_decal_1_aux.
  apply Series_ext => k.
  apply f_equal ; ring.
  intuition.
  move => k Hk ; intuition.
Qed.

(** ** Convergence theorems *)


(** Cauchy Criterion *)

Lemma Cauchy_ex_series (a : nat -> R) :
  ex_series a <-> (Cauchy_crit_series a).
Proof.
  split => Hcv.
  by apply cv_cauchy_1, ex_series_equiv_0.
  by apply ex_series_equiv_1, cv_cauchy_2.
Qed.

(** Series and Limits *)

Lemma ex_series_lim_0 (a : nat -> R) :
  ex_series a -> is_lim_seq a 0.
Proof.
  move => Hs eps.
  apply Cauchy_ex_series in Hs.
  case: (Hs eps (cond_pos eps)) => {Hs} N Hs.
  exists (S N) ; case => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  replace (a (S n) - 0)
    with (sum_f_R0 a (S n) - sum_f_R0 a n)
    by (simpl ; ring).
  apply Hs ; by intuition.
Qed.

(** Absolute convergence *)

Lemma Abs_ex_series (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) -> ex_series a.
Proof.
  move => H.
  apply Cauchy_ex_series.
  apply cauchy_abs.
  by apply Cauchy_ex_series.
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

(** D'Alembert criterium *)

Lemma DAlembert_ex_series (a : nat -> R) (k : R) :
  k < 1 -> (forall n, a n <> 0) 
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) k
      -> ex_series (fun n => Rabs (a n)).
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
  move => n ; by apply Rabs_no_R0, Ha.
  move => e He ; case: (H (mkposreal _ He)) => /= {H} N H ; exists N => n Hn.
  rewrite -Rabs_div // Rabs_Rabsolu.
  by apply H.
Qed.

Lemma DAlembert_not_ex_series (a : nat -> R) (l : R) :
  l > 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) l
      -> ~ ex_series (fun n => Rabs (a n)).
Proof.
  move => Hk Ha H Hex.
  have Hl1 : 1 < (l+1)/2.
    pattern 1 at 1.
    replace 1 with ((1 + 1) / 2) by field.
    apply Rlt_div.
    by apply Rlt_R0_R2.
    replace ((l + 1) / 2 * 2) with (l+1) by field.
    by apply Rplus_lt_compat_r.
  have H0 : exists N, forall n, (N <= n)%nat -> (l+1)/2 * Rabs (a n) <= Rabs (a (S n)).
  have He : 0 < (l-1)/2.
    apply Rdiv_lt_0_compat.
    by apply Rlt_Rminus.
    by apply Rlt_0_2.
  case: (H (mkposreal _ He)) => {H} /= N H.
  exists N => n Hn.
  move: (H n Hn) => {H} H.
  apply Rlt_le, Rabs_le_between' in H.
  case: H => H _.
  replace ((l + 1) / 2) with (l - (l - 1) / 2) by field.
  apply Rle_div2.
  by apply Rabs_pos_lt.
  rewrite -Rabs_div => // ; by apply Rgt_not_eq.
  case: H0 => N H0.
  apply (ex_series_decal_n _ N) in Hex.
  have Hl: ~ (ex_series (fun n => Rabs (a N) * ((l + 1) / 2)^n)).
    have Hl : ~ (ex_series (fun n => ((l + 1) / 2)^n)).
    case => L Hl.
    case: (Hl (mkposreal _ Rlt_0_1)) => {Hl} /= Nl Hl.
    case: (fun H => Pow_x_infinity ((l + 1) / 2) H ((L+1) * (((l + 1) / 2)-1) + 1)).
      apply Rlt_le_trans with ((l + 1) / 2).
      by apply Hl1.
      by apply Rle_abs.
    move => n Hn.
    move: (Hl (n + Nl)%nat (le_plus_r _ _)).
    apply Rle_not_lt.
    apply Rle_trans with (2 := Rle_abs _).
    rewrite Rminus_le_0.
    replace (sum_f_R0 (fun k : nat => ((l + 1) / 2) ^ k) (n + Nl) - L - 1)
      with (sum_f_R0 (fun k : nat => ((l + 1) / 2) ^ k) (n + Nl) - (L + 1))
      by ring.
    rewrite -Rminus_le_0.
    rewrite tech3.
    replace ((1 - ((l + 1) / 2) ^ S (n + Nl)) / (1 - (l + 1) / 2))
      with ((((l + 1) / 2) ^ S (n + Nl) - 1) / ((l + 1) / 2 - 1)).
    apply Rle_div2.
    by apply Rlt_Rminus.
    rewrite Rminus_le_0.
    replace (((l + 1) / 2) ^ S (n + Nl) - 1 - (L + 1) * ((l + 1) / 2 - 1))
      with (((l + 1) / 2) ^ S (n + Nl) - ((L + 1) * ((l + 1) / 2 - 1) + 1))
      by ring.
    rewrite -Rminus_le_0.
    rewrite -(Rabs_pos_eq (((l + 1) / 2) ^ S (n + Nl))).
    apply Rge_le, Hn.
    by intuition.
    apply pow_le.
    apply Rlt_le, Rlt_trans with 1 => //.
    by apply Rlt_0_1.
    field ; ring_simplify (2 - (l + 1)) ;
    ring_simplify (l + 1 - 2) ; split.
    apply Rlt_not_eq.
    rewrite Rplus_comm -/(Rminus 1 l).
    by apply Rlt_minus.
    apply Rgt_not_eq.
    by apply Rlt_Rminus.
    by apply Rgt_not_eq.
  contradict Hl.
  apply ex_series_ext with (fun n : nat => / Rabs (a N) * (Rabs (a N) * ((l + 1) / 2) ^ n)).
    move => n ; field.
    by apply Rabs_no_R0.
    by apply ex_series_scal.
  apply: Hl.
  move: Hex.
  apply Comp_ex_series.
  move => n ; split.
  apply Rmult_le_pos.
  by apply Rabs_pos.
  by apply pow_le, Rlt_le, Rlt_trans with (1 := Rlt_0_1).
  elim: n => /= [ | n IH].
  rewrite Rmult_1_r plus_0_r ; by apply Req_le.
  rewrite (Rmult_comm ((l + 1) / 2)) -Rmult_assoc.
  apply Rle_trans with (Rabs (a (N + n)%nat) * ((l + 1) / 2)).
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
  by [].
  rewrite Rmult_comm.
  rewrite -plus_n_Sm.
  apply H0 ; by intuition.
Qed.

(** Comming soon : alternated series *)

(** ** Operations *)

(** * Power series *)
(** A new definition using our limits *)

Definition is_pseries (a : nat -> R) (x l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k * x ^ k)) l.
Definition ex_pseries (a : nat -> R) (x : R) :=
  ex_lim_seq (sum_f_R0 (fun k => a k * x ^ k)).
Definition PSeries (a : nat -> R) (x : R) : R :=
  Lim_seq (sum_f_R0 (fun k => a k * x ^ k)).

Lemma ex_pseries_dec (a : nat -> R) (x : R) :
  {ex_pseries a x} + {~ ex_pseries a x}.
Proof.
  by apply ex_lim_seq_dec.
Qed.

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


(** Convergence circle *)

Definition CV_circle_set (a : nat -> R) (r : R) :=
  ex_series (fun n => Rabs (a n * r^n)).

Lemma CV_circle_pty1 (a : nat -> R) (r1 r2 : R) :
  Rabs r1 <= Rabs r2 -> CV_circle_set a r2 -> CV_circle_set a r1.
Proof.
  move => H.
  apply Comp_ex_series => n ; split.
  rewrite Rabs_mult ; apply Rmult_le_pos ; by apply Rabs_pos.
  rewrite ?Rabs_mult ; apply Rmult_le_compat_l.
  by apply Rabs_pos.
  rewrite -?RPow_abs ; apply pow_incr ; split.
  by apply Rabs_pos.
  by apply H.
Qed.
Lemma CV_circle_pty2 (a : nat -> R) (x : R) :
  CV_circle_set a x -> ex_pseries a x.
Proof.
  by apply Abs_ex_series.
Qed.

Lemma CV_circle_0 (a : nat -> R) :
  CV_circle_set a 0.
Proof.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
  elim => /= [ | n IH].
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
  by apply ex_lim_seq_const.  
Qed.

Lemma CV_circle_ne (a : nat -> R) :
  exists x, (CV_circle_set a) x.
Proof.
  exists 0.
  by apply CV_circle_0.
Qed.
Definition CV_circle (a : nat -> R) : Rbar :=
  Lub_Rbar_ne (CV_circle_set a) (CV_circle_ne a).

Lemma CV_circle_bounded (a : nat -> R) :
  is_lub_Rbar (fun r => exists M, forall n, Rabs (a n * r ^ n) <= M) (CV_circle a).
Proof.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => cv /= [ub lub].
  split.
  
  move => r /= [M Hr].
  
  have : forall y, Rabs y < Rabs r -> (CV_circle_set a) y.
    move => y Hy ; rewrite /CV_circle_set /=.
  set l := (Rabs (y / r)).
  have : ex_series (fun n => M * l ^ n).
  apply ex_series_scal.
  apply ex_lim_seq_ext with (fun n => (1 - l ^ S n) / (1 - l)).
  move => n ; rewrite tech3.
  by [].
  move => H.
  have H0 : Rabs y = Rabs r.
  rewrite -(Rmult_1_l (Rabs r)) ; rewrite -H.
  rewrite /l Rabs_div ; try field.
  apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hy), Rabs_pos.
  have Hr0 : Rabs r <> 0.
    apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hy), Rabs_pos.
  contradict Hr0 ; rewrite Hr0 Rabs_R0 //.
  rewrite H0 in Hy ; by apply Rlt_irrefl in Hy.
  case: (Req_dec l 0) => Hl0.
  rewrite Hl0 ; exists 1.
  apply is_lim_seq_ext with (2 := is_lim_seq_const 1).
  move => n ; rewrite /Rdiv ?Rmult_0_l pow_i.
  field.
  by apply lt_0_Sn.
  exists (/ (1 - l)) => eps.
  have Hl1 : Rabs l < 1.
    rewrite /l Rabs_Rabsolu Rabs_div.
    apply (Rdiv_lt_1 (Rabs _)).
    apply Rle_lt_trans with (2 := Hy), Rabs_pos.
    by apply Hy.
    have Hr0 : Rabs r <> 0.
      apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
    contradict Hr0 ; by rewrite Hr0 Rabs_R0.
  have Hl2 : 1 - l <> 0.
    apply Rminus_eq_contra.
    contradict Hl1 ; rewrite -Hl1.
    apply Rle_not_lt ; rewrite Rabs_R1 ; by apply Rle_refl.

  case: (pow_lt_1_zero l _ (eps * Rabs (1-l)/ Rabs l)) => //.
  repeat apply Rmult_lt_0_compat.
  apply eps.
  by apply Rabs_pos_lt.
  by apply Rinv_0_lt_compat, Rabs_pos_lt.

  move => N H.
  exists N => n Hn /=.
    
  field_simplify ((1 - l * l ^ n) / (1 - l) - / (1 - l)) ;
  try by intuition.
  rewrite  ?Rabs_mult Rabs_Ropp Rabs_Rinv ; try by intuition.
  replace (pos eps) with (Rabs l * (eps * Rabs (1 - l) / Rabs l) * / Rabs (- l + 1)).
  apply Rmult_lt_compat_r => //.
    apply Rinv_0_lt_compat, Rabs_pos_lt ; by rewrite Rplus_comm.
  apply Rmult_lt_compat_l.
  by apply Rabs_pos_lt.
  by apply H.
  rewrite Rplus_comm /Rminus.
  field ; try by (split ; apply Rabs_no_R0).
  by rewrite Rplus_comm.

  apply Comp_ex_series => n.
  split.
  by apply Rabs_pos.
  replace (Rabs (a n * y ^ n)) with (Rabs (a n * r ^ n) * l^n).
  apply Rmult_le_compat_r.
  apply pow_le ; by apply Rabs_pos.
  by apply Hr.
  rewrite ?Rabs_mult Rmult_assoc ; apply Rmult_eq_compat_l.

  rewrite /l RPow_abs -Rabs_mult.
  apply f_equal.
  elim: n  => /= [ | n IH].
  ring.
  rewrite -IH ; field.
  have Hr0 : Rabs r <> 0.
    apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
  contradict Hr0 ; by rewrite Hr0 Rabs_R0.
  
  move => H.
  
  have : forall y, Rabs y < Rabs r -> Rbar_le (Finite (y)) cv.
  move => y Hy.
  apply ub.
  by apply (H y Hy).

  have Hc0 : Rbar_le (Finite 0) cv.
  apply ub, CV_circle_0.
  case: (cv) Hc0 => [c | | ] Hc0 Hcv.
  apply Rbar_finite_le.

  case: (Rle_lt_dec r 0) => Hr0.
  by apply Rle_trans with (1 := Hr0), Rbar_finite_le.

  have H0 : forall e, 0 < e <= r -> r - e <= c.
    intros.
    apply Rbar_finite_le, Hcv.
    apply Rlt_le_trans with (2 := Rle_abs _).
    rewrite Rabs_pos_eq.
    rewrite -(Rplus_0_r (r - e)).
    pattern r at 2 ; replace r with ((r-e)+e) by ring.
    apply Rplus_lt_compat_l, H0.
    rewrite -Rminus_le_0 ; by apply H0.

  apply Rnot_lt_le => H1.
  apply Rbar_finite_le in Hc0.
  have H2: (c < ((c+r)/2) < r).
    pattern r at 3 ; replace r with ((r+r)/2) by field.
    pattern c at 1 ; replace c with ((c+c)/2) by field.
    split ; apply Rmult_lt_compat_r ; by intuition.
  have H3 : 0 < ((r-c)/2) <= r.
  split.
  apply Rdiv_lt_0_compat.
  by apply Rlt_Rminus.
  by apply Rlt_R0_R2.
  pattern r at 2 ; replace r with ((r+r)/2) by field.
  apply Rmult_le_compat_r ; intuition.
  apply Rplus_le_compat_l.
  apply Rle_trans with 0.
  rewrite -(Rminus_eq0 c).
  rewrite -(Rplus_0_l (-c)).
  by apply Rplus_le_compat_r.
  by apply Rlt_le.
  move: (H0 _ H3).
  apply Rlt_not_le.
  rewrite {1}(Rdiv_1 r).
  rewrite Rdiv_minus ; try by [intuition | apply Rgt_not_eq ; intuition].
  ring_simplify (r * 2 - (r - c) * 1) ; rewrite Rmult_1_l.
  rewrite Rplus_comm ; by apply H2.

  by left.
  by case: Hc0.

(* lub *)
  move => b Hb.
  apply lub => x Hx.
  apply Hb.
  apply ex_series_lim_0 in Hx.
  case: (Hx (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.
  
  set M := fix f N := match N with 
    | O => Rabs (a O * x ^ O) 
    | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
  exists (Rmax (M N) 1) => n.
  case: (le_lt_dec N n) => Hn.
  apply Rle_trans with (2 := Rmax_r _ _).
  move: (Hx n Hn).
  rewrite Rminus_0_r Rabs_Rabsolu.
  by apply Rlt_le.
  apply Rle_trans with (2 := Rmax_l _ _).
  elim: N n Hn {Hx} => [ | N IH] /= n Hn.
  by apply lt_n_O in Hn.
  apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
  apply Rle_trans with (2 := Rmax_l _ _).
  by apply IH.
  rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
Qed.

Lemma CV_circle_carac (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a)
    -> ex_series (fun n => Rabs (a n * x ^ n)).
Proof.
  move => Ha.
  have H : ~ ~ ex_series (fun n => Rabs (a n * x ^ n)).
    contradict Ha.
    apply Rbar_le_not_lt.
    rewrite /CV_circle /Lub_Rbar_ne ;
    case: ex_lub_Rbar_ne => l /= [ub lub].
    apply: lub => r Hr.
    apply Rbar_finite_le.
    apply Rnot_lt_le ; contradict Ha.
    move: Hr.
    apply CV_circle_pty1.
    by apply Rlt_le, Rlt_le_trans with (2 := Rle_abs _).
  by case: (ex_series_dec (fun n => Rabs (a n * x ^ n))).
Qed.

Lemma CV_circle_carac_not (a : nat -> R) (x : R) :
  Rbar_lt (CV_circle a) (Finite (Rabs x))
    -> ~ is_lim_seq (fun n => a n * x ^ n) 0.
Proof.
  case: (CV_circle_bounded a) => ub lub.
  move => Hx.
  have H : ~ (fun r : R => exists M : R, forall n : nat, Rabs (a n * r ^ n) <= M) x.
    contradict Hx ; apply Rbar_le_not_lt.
    apply ub.
    case: Hx => M Hx.
    exists M => n.
    by rewrite Rabs_mult RPow_abs Rabs_Rabsolu -Rabs_mult.
  contradict H.

  case: (H (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.
  
  set M := fix f N := match N with 
    | O => Rabs (a O * x ^ O) 
    | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
  exists (Rmax (M N) 1) => n.
  case: (le_lt_dec N n) => Hn.
  apply Rle_trans with (2 := Rmax_r _ _).
  move: (Hx n Hn).
  rewrite Rminus_0_r.
  by apply Rlt_le.
  apply Rle_trans with (2 := Rmax_l _ _).
  elim: N n Hn {Hx} => [ | N IH] /= n Hn.
  by apply lt_n_O in Hn.
  apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
  apply Rle_trans with (2 := Rmax_l _ _).
  by apply IH.
  rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
Qed.

(** ** Convergence criterion *)

(** D'Alembert Criterion for power series *)

Lemma Dalembert_ex_pseries_aux (a : nat -> R) (x k : R) : 
  x <> 0 -> (forall n, a n <> 0) ->
  (is_lim_seq (fun n => Rabs (a (S n) / a n)) k
    <-> is_lim_seq (fun n => Rabs ((a (S n) * x^(S n)) / (a n * x ^ n))) (Rabs x * k)).
Proof.
  move => Hx Ha ; split => H.
  apply (fun Heq => is_lim_seq_ext _ _ _ Heq (is_lim_seq_scal _ _ _ H)).
  move => n ; rewrite ?Rabs_div => //=.
  rewrite ?Rabs_mult.
  field.
  split ; apply Rabs_no_R0 => //.
  by apply pow_nonzero.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero.
  replace k with (/ (Rabs x) * ((Rabs x)*k)) by (field ; by apply Rabs_no_R0).
  apply (is_lim_seq_ext ((fun n : nat => / Rabs x * Rabs (a (S n) * x ^ S n / (a n * x ^ n)) ))).
  move => n ; rewrite ?Rabs_div => //=.
  rewrite ?Rabs_mult.
  field.
  repeat split ; apply Rabs_no_R0 => //.
  by apply pow_nonzero.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero.
  by apply is_lim_seq_scal.
Qed.

Lemma DAlembert_crit (a : nat -> R) (x:R) l :
  (forall n:nat, a n <> 0) ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  (l = 0 \/ (l <> 0 /\ Rabs x < / l)) -> ex_pseries (fun n => Rabs (a n)) x.
Proof.
  move => Ha Hl ; case => H.
  rewrite H in Hl => {l H}.
  case: (Alembert_C3 (fun n => Rabs (a n)) x).
  move => n ; by apply Rabs_no_R0.
  move => e He ; 
  set eps := mkposreal e He ;
  case: (Hl eps) => {Hl} N Hl.
  exists N => n Hn.
  rewrite -Rabs_div ?Rabs_Rabsolu.
  by apply Hl.
  by apply Ha.
  move => s Hs ; exists s ; by apply is_pseries_equiv.
  case: (Alembert_C6 (fun n => Rabs (a n)) x l).
  rewrite -(Rinv_involutive l).
  apply Rinv_0_lt_compat.
  apply Rle_lt_trans with (1 := Rabs_pos x).
  by apply H.
  by apply H.
  move => n ; by apply Rabs_no_R0.
  move => e He ; 
  set eps := mkposreal e He ;
  case: (Hl eps) => {Hl} N Hl.
  exists N => n Hn.
  rewrite -Rabs_div ?Rabs_Rabsolu.
  by apply Hl.
  by apply Ha.
  by apply H.
  move => s Hs ; exists s ; by apply is_pseries_equiv.
Qed.

Lemma DAlembert_CV_circle_neq_0 (a : nat -> R) (l : R) :
  (forall n:nat, a n <> 0) -> 0 < l ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  CV_circle a = Finite (/l).
Proof.
  move => Ha Hl Hda.
  apply Rbar_le_antisym.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => /= cv [ub lub].
  apply lub => x Hax.
  apply Rbar_finite_le.
  case: (Rle_lt_dec x 0) => Hx.
  apply Rlt_le, Rle_lt_trans with 0.
  by apply Hx.
  by apply Rinv_0_lt_compat.
  rewrite -(Rabs_pos_eq x (Rlt_le _ _ Hx)).
  rewrite -(Rmult_1_l (/l)).
  replace (Rabs x) with ((Rabs x * l) /l) by (field ; apply Rgt_not_eq, Hl).
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rinv_0_lt_compat.
  apply Rnot_lt_le.
  contradict Hax.
  apply DAlembert_not_ex_series with (Rabs x * l) => //.
  move => n.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero, Rgt_not_eq.
  apply Dalembert_ex_pseries_aux.
  by apply Rgt_not_eq.
  by apply Ha.
  by apply Hda.

  apply Rbar_not_lt_le.
  move : (CV_circle_carac_not a).
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ;
  case => [cv | | ] /= [ub lub] Hnot_ex H ; try by auto.
  suff H0 : cv < ((cv+/l)/2) < /l.
  absurd (ex_series (fun n => Rabs (a n * ((cv+/l)/2)^n))).
  
  suff H1 : cv < Rabs ((cv + / l) / 2).
  move: (Hnot_ex ((cv + / l) / 2) H1) => {Hnot_ex} Hnot_ex.
  contradict Hnot_ex ; by apply ex_series_lim_0, Abs_ex_series.
  apply Rlt_le_trans with (2 := Rle_abs _), H0.
  suff : ex_series (fun n : nat => Rabs (a n) * Rabs(((cv + / l) / 2)) ^ n).
    apply ex_series_ext => n.
    by rewrite Rabs_mult RPow_abs.
  apply (DAlembert_crit (fun n : nat => (a n)) (Rabs ((cv + / l) / 2))) with l.
  by apply Ha.
  by apply Hda.
  right ; split.
  by apply Rgt_not_eq.
  rewrite Rabs_Rabsolu Rabs_pos_eq.
  by apply H0.
  apply Rlt_le, Rle_lt_trans with (2 := proj1 H0).
  apply Rbar_finite_le, ub.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
    elim => [ | n IH] /=.
    by rewrite Rmult_1_r.
    by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
    by apply ex_lim_seq_const.
  pattern (/l) at 3 ;
  replace (/ l) with ((/l + / l) / 2) by (field ; by apply Rgt_not_eq).
  pattern (cv) at 1 ;
  replace (cv) with ((cv + cv) / 2) by field.
  split ; apply Rmult_lt_compat_r ; by intuition.
  case: (ub 0) => //.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
    elim => [ | n IH] /=.
    by rewrite Rmult_1_r.
    by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
    by apply ex_lim_seq_const.
Qed.
Lemma DAlembert_CV_circle_eq_0 (a : nat -> R) :
  (forall n:nat, a n <> 0) -> 
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) 0 ->
  CV_circle a = p_infty.
Proof.
  move => Ha Hda.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ; case => [cv | | ] //= [ub lub] ;
  have : False => //.
  have H : CV_circle_set a (cv + 1).
    have H : 0 < cv + 1.
      apply Rlt_le_trans with (0+1).
      rewrite Rplus_0_l ; by apply Rlt_0_1.
      apply Rplus_le_compat_r.
      apply Rbar_finite_le, ub.
      apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
      elim => [ | k IH] /=.
      by rewrite Rmult_1_r.
      by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
      by apply ex_lim_seq_const.
      
    apply DAlembert_ex_series with 0.
    by apply Rlt_0_1.
    move => n ; apply Rmult_integral_contrapositive_currified.
    by[].
    by apply Rgt_not_eq, pow_lt.
  rewrite -(Rmult_0_r (Rabs (cv + 1))).
  apply (Dalembert_ex_pseries_aux a (cv + 1)).
  by apply Rgt_not_eq.
  by [].
  by [].
  move: (ub (cv+1) H).
  by apply Rbar_lt_not_le, Rlt_n_Sn.
  case: (ub 0) => //.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
  elim => [ | k IH] /=.
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
  by apply ex_lim_seq_const.
Qed.

(** Comming soon
  - convergence circle *)

(** * Operations *)

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

  case: (Req_dec x 0) => Hx.
  rewrite Hx /pow ?Rmult_0_l ; by apply ex_pseries_0.
  have H0 : ex_pseries (fun n0 : nat => Rabs (Bessel1_seq n (2 * n0))) (x ^ 2).
  apply DAlembert_crit with 0.
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
  apply Abs_ex_series ; move: H0.
  apply ex_series_ext => k.
  rewrite Rabs_mult ; apply f_equal.
  rewrite -RPow_abs ; apply (f_equal (fun x => x^k)).
  apply sym_equal, Rabs_pos_eq.
  case: (Rle_lt_dec 0 x) => Hx0.
  by apply pow_le.
  apply Rlt_le ; rewrite /pow -Rmult_opp_opp Rmult_1_r.
  apply Rmult_lt_0_compat ; by apply Ropp_0_gt_lt_contravar.
  
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