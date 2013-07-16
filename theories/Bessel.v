Require Import Reals ssreflect.
Require Import Rcomplements Rbar_theory.
Require Import Total_sup Derive Series PSeries.
Require Import AutoDerive.

(** An exemple to use power series *)

Definition Bessel1_seq (n k : nat) :=
  (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).

Lemma ex_Bessel1 (n : nat) (x : R) :
  ex_pseries (Bessel1_seq n) x.
Proof.
  have H : forall k, Bessel1_seq n k <> 0.
    move => k.
    rewrite /Bessel1_seq.
    apply Rmult_integral_contrapositive_currified.
    apply pow_nonzero, Ropp_neq_0_compat, R1_neq_R0.
    apply Rinv_neq_0_compat, Rmult_integral_contrapositive_currified ;
    apply INR_fact_neq_0.
  apply ex_series_Rabs.
  apply DAlembert_crit with 0.
  by apply H.
  move => eps.
  have H0 : 0 <= /(sqrt eps).
    apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0, eps.
  set N := nfloor (/(sqrt eps)) H0.
  exists N => k Hk.
  rewrite Rminus_0_r Rabs_Rabsolu Rabs_div.
  rewrite 2?Rabs_div ?Rabs_mult -?RPow_abs ?Rabs_Ropp ?Rabs_R1 
    ?pow1 ?(Rabs_pos_eq _ (pos_INR _)) ?H2.
  rewrite /Rdiv ?Rmult_1_l.
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
Qed.

Lemma CV_Bessel1 (n : nat) :
  CV_circle (Bessel1_seq n) = p_infty.
Proof.
  have : forall x : R, Rbar_le (Finite x) (CV_circle (Bessel1_seq n)).
  move => x ; apply Rbar_le_trans with (Finite (Rabs x)).
    by apply Rbar_finite_le, Rle_abs.
  apply Rbar_not_lt_le => Hx.
  apply CV_circle_carac_not in Hx.
  apply: Hx.
  by apply ex_series_lim_0, (ex_Bessel1 n x).
  
  rewrite /CV_circle /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ;
  case => /= [c | | ] Hc Hx.
  have: False => // ; move: (Hx (c+1)).
  apply Rbar_lt_not_le => /=.
  by apply Rlt_plus_1.
  by [].
  by case: (Hx 0).
Qed.

Definition Bessel1 (n : nat) (x : R) :=
  (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma is_derive_Bessel1 (n : nat) (x : R) :
  is_derive (Bessel1 n) x
      ((x / 2) ^ S n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2)
      + (INR n)/2 * (x / 2) ^ pred n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)).
Proof.
  rewrite /Bessel1.
  auto_derive.
  repeat split.
  apply ex_derive_PSeries.
  by rewrite CV_Bessel1.
  rewrite Derive_PSeries.
  rewrite /Rdiv ; simpl ; field.
  by rewrite CV_Bessel1.
Qed.

Lemma is_derive_2_Bessel1 (n : nat) (x : R) : 
  is_derive_n (Bessel1 n) 2 x
    (((x/2)^(S (S n)) * PSeries (PS_derive (PS_derive (Bessel1_seq n))) ((x / 2) ^ 2))
    + ((INR (2*n+1)/2) * (x/2)^n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2))
    + (INR (n * pred n) / 4 * (x / 2) ^ pred (pred n) * PSeries (Bessel1_seq n) ((x / 2) ^ 2))).
Proof.
  rewrite plus_INR ?mult_INR ; simpl INR.
  apply is_derive_ext
    with (fun x => ((x / 2) ^ S n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2)
    + (INR n)/2 * (x / 2) ^ pred n * PSeries (Bessel1_seq n) ((x / 2) ^ 2))).
  move => y ; 
  by apply sym_eq, is_derive_unique, is_derive_Bessel1.
  auto_derive.
  repeat split.
  apply ex_derive_PSeries.
  by rewrite PS_derive_circle CV_Bessel1.
  apply ex_derive_PSeries.
  by rewrite CV_Bessel1.
  
  rewrite ?Derive_PSeries.
  case: n => [ | n] ; rewrite ?S_INR /Rdiv /= ;
  simpl ; field.
  by rewrite CV_Bessel1.
  by rewrite PS_derive_circle CV_Bessel1.
Qed.

Lemma Bessel1_correct (n : nat) (x : R) :
  x^2 * Derive_n (Bessel1 n) 2 x + x * Derive (Bessel1 n) x + (x^2 - (INR n)^2) * Bessel1 n x = 0.
Proof.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) ;
  rewrite /Derive_n (is_derive_unique _ _ _ (is_derive_2_Bessel1 _ _)) ;
  rewrite /Bessel1 plus_INR ?mult_INR ; simpl INR.
  set y := x/2 ; replace x with (2 * y) by (unfold y ; field).
  
  replace ((2 * y) ^ 2 *
    (y ^ S (S n) * PSeries (PS_derive (PS_derive (Bessel1_seq n))) (y ^ 2) +
    (2 * INR n + 1) / 2 * y ^ n * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2) +
    INR n * INR (pred n) / 4 * y ^ pred (pred n) *
    PSeries (Bessel1_seq n) (y ^ 2)) +
    2 * y *
    (y ^ S n * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2) +
    INR n / 2 * y ^ pred n * PSeries (Bessel1_seq n) (y ^ 2)) +
    ((2 * y) ^ 2 - INR n ^ 2) * (y ^ n * PSeries (Bessel1_seq n) (y ^ 2)))
  with (4 * y^S (S n) * (y^2 * PSeries (PS_derive (PS_derive (Bessel1_seq n))) (y ^ 2)
    + (INR n + 1) * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2)
    + PSeries (Bessel1_seq n) (y ^ 2))).
  Focus 2.
  case: n => [ | n] ; rewrite ?S_INR ; simpl INR ; simpl pred ; simpl pow ;
  field_simplify ; rewrite -?Rdiv_1.
  field.
  case: n => [ | n] ; rewrite ?S_INR ; simpl INR ; simpl pred ; simpl pow ;
  field_simplify ; rewrite -?Rdiv_1.
  field.
  field.
  
  apply Rmult_eq_0_compat_l.
  
  rewrite -PSeries_incr_1 -PSeries_scal_l -?PSeries_plus.

  unfold PS_derive, PS_incr_1, PS_scal_l, PS_plus.
  rewrite -{2}(PSeries_const_0 (y^2)).
  apply PSeries_ext.
  case => [ | p] ; rewrite /Bessel1_seq ;
  rewrite -?plus_n_Sm ?plus_0_r /fact -/fact ?mult_INR ?S_INR ?plus_INR ; simpl INR ; simpl pow ;
  rewrite ?Rplus_0_l ?Rmult_1_l ; field.
  split ; rewrite -?S_INR ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  repeat split ; rewrite -?plus_INR -?S_INR ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  by apply (lt_INR 0), lt_O_Sn.
  by apply (lt_INR 0), lt_O_Sn.

  apply ex_series_Rabs, CV_circle_carac.
  apply Rbar_lt_le_trans with (2 := CV_circle_plus _ _).
  rewrite /Rbar_min ; case: Rbar_le_dec => _.
  by rewrite CV_circle_incr_1 ?PS_derive_circle CV_Bessel1.
  apply Rbar_lt_le_trans with (2 := CV_circle_scal_l _ _).
  by rewrite PS_derive_circle CV_Bessel1.
  by apply ex_Bessel1.
  apply ex_series_Rabs, CV_circle_carac.
  by rewrite CV_circle_incr_1 ?PS_derive_circle CV_Bessel1.
  apply ex_series_Rabs, CV_circle_carac.
  apply Rbar_lt_le_trans with (2 := CV_circle_scal_l _ _).
  by rewrite PS_derive_circle CV_Bessel1.
Qed.

Lemma Bessel1_equality_1 (n : nat) (x : R) : (0 < n)%nat -> x<>0
  -> Bessel1 (S n)%nat x + Bessel1 (pred n)%nat x = (2*INR n)/x * Bessel1 n x.
Proof.
  case: n => [ | n] Hn Hx.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl pred.
  rewrite /Bessel1 S_INR.
  replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) +
      (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)) 
    with ((x/2)^n *
      ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) +
      PSeries (Bessel1_seq n) ((x / 2) ^ 2))) 
    by (simpl ; ring).
  replace (2 * (INR n + 1) / x *
      ((x / 2) ^ S n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    with ((x/2)^n * ((INR n + 1) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    by (simpl ; field ; exact: Hx).
  apply f_equal.
  rewrite -PSeries_incr_1 -PSeries_scal_l -PSeries_plus.
Focus 2. (* ex_pseries (PS_incr_1 (Bessel1_seq (S (S n))) (S (S n))) (x / 2) *)
  by apply ex_pseries_incr_1, ex_Bessel1.
Focus 2. (* ex_pseries (PS_incr_n (Bessel1_seq n) n) (x / 2) *)
  by apply ex_Bessel1.
  apply PSeries_ext => k.
(* egalité *)
  rewrite /PS_plus /PS_scal_l /PS_incr_1 /Bessel1_seq ;
  case: k => [ | k] ;
  rewrite ?plus_0_r -?plus_n_Sm ?plus_Sn_m 
    /fact -/fact ?mult_INR ?S_INR ?plus_INR /=.
  field.
  rewrite -?S_INR ; split ;
  by [apply not_0_INR, sym_not_eq, O_S | apply INR_fact_neq_0].
  field ;
  rewrite -?plus_INR -?S_INR ; repeat split ;
  by [apply INR_fact_neq_0 | apply not_0_INR, sym_not_eq, O_S].
Qed.
Lemma Bessel1_equality_2 (n : nat) (x : R) : x <> 0
  -> Bessel1 (S n)%nat x = INR n * Bessel1 n x / x - Derive (Bessel1 n) x.
Proof.
  move => Hx.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
  set y := (x / 2).
  replace x with (2 * y) by (unfold y ; field).
  
(* Supprimer les PSeries *)
  have Hy : y <> 0.
  unfold y ; contradict Hx.
  replace x with (2 * (x/2)) by field ; rewrite Hx ; ring.
  case: n => [ | n] ; simpl ; field_simplify => // ; rewrite -Rdiv_1 -/(pow _ 2).
(* * cas n = 0 *)
  replace (- 2 * y ^ 2 * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2) / (2 * y))
    with (y * ((-1) * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2)))
    by (simpl ; unfold y ; field => //).
  apply f_equal.
  rewrite -PSeries_scal_l.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal_l /PS_derive plus_0_l.
  replace (1+k)%nat with (S k) by ring.
  rewrite /fact -/fact mult_INR /pow -/pow.
  field ; split.
  exact: INR_fact_neq_0.
  by apply not_0_INR, not_eq_sym, O_S.
(* * cas S n *)
  replace (S n + 1)%nat with (S(S n)) by ring.
  replace (-2 * y ^ 2 * y ^ n * PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2) / 2)
    with (y^2 * y^n * (((-1)* PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2))))
    by (unfold y ; field => //).
  apply f_equal.
  rewrite -PSeries_scal_l.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal_l /PS_derive -?plus_n_Sm ?plus_Sn_m.
  rewrite /pow -/pow /fact -/fact ?mult_INR ?S_INR plus_INR.
  field.
  rewrite -plus_INR -?S_INR.
  repeat split ;
  try by [exact: INR_fact_neq_0 | apply not_0_INR, not_eq_sym, O_S].
Qed.