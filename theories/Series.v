Require Import Reals ssreflect.
Require Import Rcomplements.
Require Import Lim_seq Rbar_theory.

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

(** Addition of two power series *)

Lemma is_series_plus (a b : nat -> R) (la lb : R) :
  is_series a la -> is_series b lb
    -> is_series (fun n => a n + b n) (la + lb).
Proof.
  move => Ha Hb.
  apply is_lim_seq_ext 
    with (fun n => (sum_f_R0 (fun k => a k) n) + (sum_f_R0 (fun k => b k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  by apply is_lim_seq_plus with la lb.
Qed.
Lemma ex_series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> ex_series (fun n => a n + b n).
Proof.
  move => [la Ha] [lb Hb].
  exists (la + lb).
  by apply is_series_plus.
Qed.
Lemma Series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n + b n) = Series a + Series b.
Proof.
  intros Ha Hb.
  apply is_lim_seq_unique, is_series_plus ;
  by apply Lim_seq_correct.
Qed.

(** Coming soon:
  - multiplication *)

(** Index offset *)

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

(** Cauchy Criterion : A redemontrer sans Rcomplete.R_complete *)

Lemma Cauchy_ex_series (a : nat -> R) :
  ex_series a <-> (Cauchy_crit_series a).
Proof.
  split => Hcv.
  by apply cv_cauchy_1, ex_series_equiv_0.
  apply ex_series_equiv_1.
  apply R_complete.
  by apply Hcv.
Qed.
(** %$\sum a_n$ is convergent $\Rightarrow \lim_{n\to + \infty} a_n = 0$%
#if a is summable, then its limit is 0# *)

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

(** #Absolute convergence imply convergence#
%$\sum | a_n |$ converge $\Rightarrow \sum a_n$ is convergent% *)

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
  apply Cauchy_ex_series.
  apply Cauchy_ex_series in Hb.
  move => e He.
  case (Hb e He) => {Hb} N Hb.
  exists N => n m Hn Hm.
  wlog: n m Hn Hm /(n > m)%nat => [Hw | Hnm].
  case: (le_lt_dec n m) => Hnm.
  apply le_lt_eq_dec in Hnm ; case: Hnm => Hnm.
  rewrite /R_dist -Ropp_minus_distr' Rabs_Ropp ; by apply Hw.
  by rewrite Hnm /R_dist Rminus_eq0 Rabs_R0.
  by apply Hw.
  move: (Hb n m Hn Hm).
  rewrite /R_dist (tech2 a m n Hnm) (tech2 b m n Hnm) ; 
    ring_simplify (sum_f_R0 a m 
    + sum_f_R0 (fun i : nat => a (S m + i)%nat) (n - S m) 
    - sum_f_R0 a m) ; 
    ring_simplify (sum_f_R0 b m 
    + sum_f_R0 (fun i : nat => b (S m + i)%nat) (n - S m) 
    - sum_f_R0 b m).
  apply Rle_lt_trans.
  apply Rle_trans with (2 := Rle_abs _).
  rewrite Rabs_pos_eq.
  elim: (n - S m)%nat => /= [ | k IH].
  by apply H.
  apply Rplus_le_compat.
  exact: IH.
  by apply H.
  elim: (n - S m)%nat => /= [ | k IH].
  by apply H.
  apply Rplus_le_le_0_compat.
  exact: IH.
  by apply H.
Qed.

(** D'Alembert criterium *)

Lemma DAlembert_ex_series (a : nat -> R) (k : R) :
  k < 1 -> (forall n, a n <> 0) 
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) k
      -> ex_series (fun n => Rabs (a n)).
Proof.
  move => Hk Ha H.
  have : exists N, forall n, (N <= n)%nat -> Rabs (a (S n) / a n) <= (k+1)/2.
    case: (fun He => H (mkposreal ((1-k)/2) He)).
      move: (fun He => is_pos_div_2 (mkposreal (1-k) He)) => /= He ;
      apply: He.
      by apply -> Rminus_lt_0.
    move => {H} /= Hk1 N H.
    exists N => n Hn.
    move: (H n Hn) => {H} H.
    apply Rabs_lt_between' in H ; case: H => _ H ; 
    field_simplify in H ; rewrite -Rdiv_1 in H ; by apply Rlt_le.
  case => {H} N H.
  apply ex_series_decal_n with N.
  apply Comp_ex_series with (fun n => Rabs (a N) * ((k+1)/2)^n).
  move => n ; split.
  by apply Rabs_pos.
  rewrite Rmult_comm ; apply Rle_div_l.
  by apply Rabs_pos_lt.
  rewrite -Rabs_div.
  elim: n => [ | n IH].
  rewrite plus_0_r /Rdiv Rinv_r.
  rewrite Rabs_R1 ; by apply Rle_refl.
  by apply Ha.
  replace (Rabs (a (N + S n)%nat / a N)) 
    with (Rabs (a (S (N + n))/a (N+n)%nat) * Rabs (a (N + n)%nat / a N)).
  simpl ; apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  apply H, le_plus_l.
  by apply IH.
  rewrite -Rabs_mult ; apply f_equal.
  rewrite plus_n_Sm ; field ; split ; by apply Ha.
  by apply Ha.
  apply ex_series_scal.
  set k0 := ((k + 1) / 2).
  apply ex_lim_seq_ext with (fun N => / (1 - k0) * (1 - k0 ^ S N)).
  move => n ; rewrite tech3.
  by apply Rmult_comm.
  apply Rlt_not_eq.
  replace 1 with ((1+1)/2) by field ; rewrite /k0.
  apply Rmult_lt_compat_r ; by intuition.
  apply ex_lim_seq_scal.
  exists (1-0).
  apply is_lim_seq_minus.
  by apply is_lim_seq_const.
  simpl ; rewrite -(Rmult_0_r k0) ; apply is_lim_seq_scal.
  apply (is_lim_seq_geom k0).
  rewrite Rabs_pos_eq.
  replace 1 with ((1+1)/2) by field ; rewrite /k0.
  apply Rmult_lt_compat_r ; by intuition.
  apply Rle_trans with (2 := H N (le_refl _)) ; by apply Rabs_pos.
Qed.

Lemma DAlembert_not_ex_series (a : nat -> R) (l : R) :
  l > 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) l
      -> ~ is_lim_seq a 0.
Proof.
  move => Hl Ha Hda Ha0.
  set k := (l+1)/2.
  have Hk1 : 1 < k.
    apply Rminus_lt ; unfold k ; field_simplify ; rewrite -Rdiv_1.
    rewrite -(Rmult_0_l (/2)) ; apply Rmult_lt_compat_r ; try by intuition.
    rewrite Rplus_comm ; by apply Rlt_minus.
  have : exists N, forall n, (N <= n)%nat -> k <= Rabs (a (S n) / a n).
    case: (fun H => Hda (mkposreal ((l-1)/2) H)) => [ | /= {Hda} H N Hda].
    apply Rdiv_lt_0_compat.
    by apply -> Rminus_lt_0.
    by apply Rlt_R0_R2.
    exists N => n Hn.
    move: (Hda n Hn) => {Hda} Hda.
    apply Rabs_lt_between' in Hda.
    replace (k) with (l - (l - 1) / 2) by (unfold k ; field).
    by apply Rlt_le, Hda.
  case => N H.
  apply is_lim_seq_abs_0, (is_lim_seq_incr_n _ N) in Ha0.
  have : forall n, Rabs (a N) * k ^ n <= Rabs (a (n + N)%nat).
    elim => /= [ | n IH].
    rewrite Rmult_1_r ; by apply Rle_refl.
    replace (Rabs (a (S (n + N)))) 
      with (Rabs (a (S (n+N)) / a (n+N)%nat) * Rabs (a (n+N)%nat))
      by (rewrite -Rabs_mult ; apply f_equal ; by field).
    replace (Rabs (a N) * (k * k ^ n)) with (k * (Rabs (a N) * k ^ n)) by ring.
    apply Rmult_le_compat.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H, le_plus_r.
    by apply IH.
  move => {H} H.
  have : Finite 0 = p_infty.
    rewrite -(Rbar_lim_seq_geom_p k Hk1).
    apply sym_equal.
    apply Rbar_is_lim_correct, is_lim_seq_correct.
    apply is_lim_seq_ext with (fun n => / Rabs (a N) * (Rabs (a N) * k ^ n)).
    move => n ; field ; by apply Rabs_no_R0.
    rewrite -(Rmult_0_r (/Rabs (a N))).
    apply is_lim_seq_scal.
    apply is_lim_seq_le_le with (fun _ => 0) (fun n => Rabs (a (n + N)%nat)).
    move => n ; split.
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H.
    by apply is_lim_seq_const.
    by apply Ha0.
  by [].
Qed.
