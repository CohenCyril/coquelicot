Require Import Reals Even Div2 ssreflect.
Require Import Lim_seq Floor Rcomplements.

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

(** * Domain of definition *)

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

(** D'Alembert Criterion *)


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

(** * Operations *)
(** Addition of two power series *)

Definition PS_plus (a b : nat -> R) (n : nat) : R :=
  a n + b n.
Lemma is_pseries_plus a b x la lb :
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
Lemma ex_pseries_plus a b x :
  ex_pseries a x -> ex_pseries b x
    -> ex_pseries (PS_plus a b) x.
Proof.
  move => [la Ha] [lb Hb].
  exists (la + lb).
  by apply is_pseries_plus.
Qed.
Lemma PSeries_plus a b x :
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
Lemma is_pseries_scal c a x l :
  is_pseries a x l -> is_pseries (PS_scal c a) x (c * l).
Proof.
  move => Ha.
  apply is_lim_seq_ext with (fun n => c * (sum_f_R0 (fun k => a k * x ^ k) n)).
  elim => [ | n IH].
  simpl ; rewrite /PS_scal ; ring.
  simpl ; rewrite -IH /PS_scal ; ring.
  by apply is_lim_seq_scal.
Qed.
Lemma ex_pseries_scal c a x :
  ex_pseries a x -> ex_pseries (PS_scal c a) x.
Proof.
  move => [l Ha].
  exists (c * l).
  by apply is_pseries_scal.
Qed.
Lemma PSeries_scal c a x :
  PSeries (PS_scal c a) x = c * PSeries a x.
Proof.
  rewrite -Lim_seq_scal.
  apply Lim_seq_ext.
  elim => [ | n IH].
  simpl ; rewrite /PS_scal ; ring.
  simpl ; rewrite IH /PS_scal ; ring.
Qed.

(** Multiplication and division by a variable *)

Definition PS_incr (a : nat -> R) (n : nat) : R :=
  match n with
    | 0 => 0
    | S n => a n
  end.
Lemma PSeries_incr a x :
  PSeries (PS_incr a) x = x * PSeries a x.
Proof.
  rewrite -Lim_seq_scal.
  rewrite /PS_incr /PSeries /=.
  rewrite -Lim_seq_incr /=.
  apply Lim_seq_ext.
  elim => /= [ | n IH].
  ring.
  rewrite IH ; ring.
Qed.

Definition PS_decr (a : nat -> R) (n : nat) : R :=
  a (S n).
Lemma PSeries_decr (a : nat -> R) (x : R) :
  a O = 0 -> x <> 0 -> PSeries (PS_decr a) x = (PSeries a x) / x.
Proof.
  intros Ha0 Hx.
  replace (PSeries _ _) with ((x * PSeries (PS_decr a) x)/x) by (field ; auto).
  apply Rmult_eq_compat_r.
  rewrite -PSeries_incr.
  rewrite /PS_incr /PS_decr /= /PSeries.
  apply Lim_seq_ext.
  elim => [ | n IH] /=.
  by rewrite Ha0.
  by rewrite IH.
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

(* Fonctions de Bessel du premier ordre (cf: wikipédia)
  - Lire article d'Harrison
  - résoudre $J_{n+1}(x) + J_{n-1](x) = \frac{2n}{x} J_n(x)$
  - résoudre avec dérivées *)

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