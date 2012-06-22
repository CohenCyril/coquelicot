Require Import Reals Max Floor.
Open Scope R_scope.

(** * Markov's principle *)

Lemma Markov : forall P : nat -> Prop, (forall n, {P n}+{~P n}) ->
  {n : nat| P n} + {forall n, ~ P n}.
Proof.
  intros P H.
  set (P' := fix f (n : nat) : R := 
    match n with 
      | O => if (H O) then 1 else 0
      | S n => if (H (S n)) then 1 else (f n)
    end ).

  cut ({n : nat | P' n = 1} + {(forall n : nat, P' n = 0)}).
    intros.
    destruct H0.
    left ; destruct s as (n,H0).
    cut ({m|(m <= n)%nat /\ P m}).
      intros.
      destruct H1 as (m,H1).
      exists m.
      apply H1.
    induction n.
    simpl in H0 ; destruct (H O).
    exists O ; intuition.
    contradict H0 ; apply sym_not_eq, R1_neq_R0.
    simpl in H0 ; destruct (H (S n)).
    exists (S n) ; intuition.
    destruct (IHn H0) as (m,Hm).
    exists m ; intuition.
    right.
    intros.
    cut (forall m, (m <= n)%nat -> ~ P m).
    intros ; apply H0.
    apply le_refl.
    set (H0 := e n) ; revert H0 ; intros.
    induction n.
    simpl in H0 ; destruct (H O).
    absurd (1=0) ; [apply R1_neq_R0 | apply H0].
    rewrite <- (le_n_O_eq _ H1) ; apply n.
    destruct (le_lt_eq_dec _ _ H1).
    apply IHn.
    apply lt_n_Sm_le, l.
    rewrite e0. simpl in H0.
    generalize H0 ; clear H0 ; destruct (H (S n)).
    intro ; contradict H0 ; apply R1_neq_R0.
    intro ; apply n0.
  
  assert (P'1 : forall n, {P' n = 0} + {P' n = 1}).
    intros.
    induction n.
    destruct (H O) ; simpl ; intuition.
    unfold P' ; destruct (H (S n)) ; simpl ; intuition.
  assert (P'2 : forall n : nat, P' n <= 1).
    intros ; destruct (P'1 n) ; rewrite e ; intuition.
  assert (P'3 : forall n, P' n = 0 -> forall m, (m <= n)%nat -> P' m = 0).
    intros ; induction n.
    rewrite <- (le_n_O_eq _ H1) ; apply H0.
    destruct (le_lt_eq_dec _ _ H1).
    apply IHn.
    simpl in H0 ; destruct (H (S n)).
    contradict H0 ; apply R1_neq_R0.
    apply H0.
    apply lt_n_Sm_le, l.
    rewrite e ; apply H0.
  
  set (u := fun n => P' n * /2^n).
  assert (u0 : forall n, 0 <= u n <= /2^n).
    intros ; unfold u.
    destruct (P'1 n) ; rewrite e ; intuition ; [rewrite Rmult_0_l|rewrite Rmult_1_l] ;
    apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
  assert (u1 : forall n, 0 <= u n <= 1).
    intros ; unfold u.
    cut (0 <= P' n * / 2 ^ n <= /2^n).
    intros.
    intuition.
    apply Rle_trans with (1 := H2).
    pattern 1 at 3 ; rewrite <- Rinv_1 ; apply Rle_Rinv.
    apply Rlt_0_1.
    apply pow_lt, Rlt_R0_R2.
    pattern 1 at 1 ; rewrite <- (pow1 n).
    apply pow_incr ; split.
    apply Rle_0_1.
    pattern 1 at 1 ; rewrite <- (Rplus_0_r 1) ; apply Rplus_le_compat_l, Rle_0_1.
    apply u0.
    
  cut ({n : nat | u n > 0} + {(forall n : nat, u n = 0)}).
    intros H0 ; destruct H0.
    left ; destruct s as (n,H0).
    exists n.
    cut (P' n > 0).
      intros.
      destruct (P'1 n).
      contradict e ; apply Rgt_not_eq, H1.
      apply e.
      apply (Rmult_lt_reg_l (/ 2 ^ n)).
      apply Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
      rewrite Rmult_0_r, Rmult_comm.
      apply H0.
    right ; intros.
    apply (Rmult_eq_reg_l (/ 2 ^ n)).
    rewrite Rmult_0_r, Rmult_comm.
    apply e.
    apply Rgt_not_eq, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.

  set (E y := exists n, y = u n).
  assert (bound_E : bound E).
    exists 1 ; intros x (n,Ex) ; rewrite Ex ; clear Ex x.
    apply (u1 n).
  assert (ex_E : exists x, E x).
    exists (u O) ; exists O ; reflexivity.
  destruct (completeness E bound_E ex_E) as (l,(ub,lub)).
  destruct (Rle_lt_or_eq_dec 0 l).
    apply Rle_trans with (1 := proj1 (u1 O)).
    apply ub ; exists O ; reflexivity.
  left.
  destruct (log_x_lt_1_ex (/2) l) as (n,Hn).
  split.
  apply Rinv_0_lt_compat, Rlt_R0_R2.
  pattern 1 at 3 ; rewrite <- Rinv_1 ; apply Rinv_lt_contravar.
  rewrite Rmult_1_l ; apply Rlt_R0_R2.
  pattern 1 at 1 ; rewrite <- (Rplus_0_l 1) ; apply Rplus_lt_compat_r, Rlt_0_1.
  split.
  apply r.
  apply lub.
  intros x (n,Ex) ; rewrite Ex ; clear Ex x.
  apply (u1 n).
  exists n.
  cut (u n = l).
    intros ; rewrite H0 ; apply r.
  apply Rle_antisym.
    apply ub.
    exists n ; reflexivity.
  apply lub.
  intros x (k,Ex) ; rewrite Ex ; clear Ex x.
  
  assert (forall m, (m < n)%nat -> u m = 0).
    intros.
    unfold u.
    destruct (P'1 m) ; rewrite e.
    ring.
    destruct Hn.
    contradict H2.
    apply Rlt_not_le.
    apply Rlt_le_trans with (r2 := (/2)^m).
    repeat rewrite <- Rinv_pow.
    apply Rinv_lt_contravar.
    rewrite <- Rdef_pow_add.
    apply pow_lt, Rlt_R0_R2.
    apply Rlt_pow.
    pattern 1 at 1 ; rewrite <- (Rplus_0_l 1) ; apply Rplus_lt_compat_r, Rlt_0_1.
    apply H0.
    apply Rgt_not_eq, Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_R0_R2.
    rewrite <- (Rmult_1_l ((/ 2) ^ m)) ; pattern 1 at 1 ; rewrite <- e.
    apply ub.
    exists m ; unfold u ; rewrite Rinv_pow. 
    reflexivity.
    apply Rgt_not_eq, Rlt_R0_R2.

  destruct (lt_eq_lt_dec k n).
    destruct s.

    rewrite (H0 _ l0) ; apply (u1 n).
    rewrite e ; apply Rle_refl.
  apply Rle_trans with (r2 := /2^k).
  unfold u ; destruct (P'1 k) ; rewrite e ; intuition.
  rewrite Rmult_0_l ; apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
  unfold u ; destruct (P'1 n) ; rewrite e.
  rewrite Rmult_0_l.
  set (r0 :=proj1 Hn).
  absurd ((/ 2) ^ S n < l) ; [|apply r0].
  apply Rle_not_lt.
  apply lub.
  intros x (m,Ex) ; rewrite Ex ; clear Ex x.
  destruct (lt_eq_lt_dec m (S n)).
    destruct s.
    apply lt_n_Sm_le in l1.
    destruct (le_lt_eq_dec _ _ l1).
    rewrite (H0 _ l2).
    apply Rlt_le, pow_lt, Rinv_0_lt_compat, Rlt_R0_R2.
    unfold u ; rewrite e0, e, Rmult_0_l.
    apply Rlt_le, pow_lt, Rinv_0_lt_compat, Rlt_R0_R2.
    rewrite e0, <-Rinv_pow. apply (u0 (S n)).
    apply Rgt_not_eq, Rlt_R0_R2.
    apply Rlt_le, Rle_lt_trans with (1 := proj2 (u0 _)).
    rewrite <- Rinv_pow.
    apply Rinv_lt_contravar.
    rewrite <- Rdef_pow_add ; apply pow_lt, Rlt_R0_R2.
    apply Rlt_pow.
    pattern 1 at 1 ; rewrite <- (Rplus_0_l 1) ; apply Rplus_lt_compat_r, Rlt_0_1.
    apply l1.
    apply Rgt_not_eq, Rlt_R0_R2.
  rewrite Rmult_1_l.
  apply Rlt_le, Rinv_lt_contravar, Rlt_pow.
  rewrite <- Rdef_pow_add ; apply pow_lt, Rlt_R0_R2.
  pattern 1 at 1 ; rewrite <- (Rplus_0_l 1) ; apply Rplus_lt_compat_r, Rlt_0_1.
  apply l0.
  right ; intros.
  apply Rle_antisym.
  rewrite e ; apply ub.
  exists n ; reflexivity.
  apply (u0 n).
Qed.

Lemma Markov_cor1 : forall P : nat -> Prop, (forall n, {P n}+{~P n}) ->
  (~ forall n : nat, ~ P n) -> exists n : nat, P n.
Proof.
  intros.
  destruct (Markov P H).
  destruct s as (n,H1) ; exists n ; apply H1.
  contradict H0 ; apply n.
Qed.

Lemma Markov_cor2 : forall P : nat -> Prop, (forall n, {P n}+{~P n}) ->
  ~~ (exists n : nat, P n) -> exists n : nat, P n.
Proof.
  intros.
  apply Markov_cor1.
  apply H.
  contradict H0.
  intros (n,H1).
  contradict H1 ; apply H0.
Qed.
