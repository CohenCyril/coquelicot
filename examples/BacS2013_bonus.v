Require Import Reals ssreflect Psatz.
Require Import Hierarchy PSeries Rbar Limit.

Open Scope R_scope.

(** * Bac 2013 - Exercice 4 spécialité *)

(** 1. Exprimer v (S n) et c (S n) en fonction de v n et c n *)

Fixpoint v (n : nat) : R :=
  match n with
  | O => 7 / 10 * 250000
  | S n => 95 / 100 * v n + 1 / 100 * c n
  end
with c (n : nat) : R :=
  match n with
  | O => 3 / 10 * 250000
  | S n => 5 / 100 * v n + 99 / 100 * c n
  end.

(** 2. Définition de la matrice A *)

Definition A : matrix 2 2 :=
  ((95/100,(1/100,tt)),
   (5/100,(99/100,tt),tt)).

Definition X (n : nat) : matrix 2 1 :=
  ((v n,tt),
   (c n,tt,tt)).

Lemma Q2 : forall n, X (S n) = scal A (X n).
Proof.
  by [].
Qed.

(** 3. Matrices de changement de base *)

Definition P : matrix 2 2 :=
  ((1,(-1,tt)),
   (5,(1,tt),tt)).
Definition Q : matrix 2 2 :=
  ((1,(1,tt)),
   (-5,(1,tt),tt)).

Goal mult P Q = ((6,(0,tt)),
                 (0,(6,tt),tt)).
rewrite /mult /= /Mmult /Mone /=.
apply (coeff_mat_ext_aux 0 0).
intros i j Hi Hj.
rewrite coeff_mat_bij => //.
unfold coeff_mat, plus, mult ; simpl.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try ring) ;
(try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /= ; try ring).
Qed.

Goal mult Q P = ((6,(0,tt)),
                 (0,(6,tt),tt)).
rewrite /mult /= /Mmult /Mone /=.
apply (coeff_mat_ext_aux 0 0).
intros i j Hi Hj.
rewrite coeff_mat_bij => //.
unfold coeff_mat, plus, mult ; simpl.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try ring) ;
(try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /= ; try ring).
Qed.

Definition Q' : matrix 2 2 :=
  ((1 / 6,(1 / 6,tt)),
   (-5 / 6,(1 / 6,tt),tt)).

Lemma Q3a : mult P Q' = Mone /\ mult Q' P = Mone.
Proof.
  rewrite /mult /= /Mmult /Mone /=.
  split ;
  apply (coeff_mat_ext_aux 0 0).

  intros i j Hi Hj.
  rewrite coeff_mat_bij => //.
  unfold coeff_mat, plus, mult ; simpl.
  (destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /one /= ; try field) ;
  (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field).
  
  intros i j Hi Hj.
  rewrite coeff_mat_bij => //.
  unfold coeff_mat, plus, mult ; simpl.
  (destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /one /= ; try field) ;
  (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field).
Qed.

Definition D : matrix 2 2 := ((1,(0,tt)),
                              (0,(94 / 100,tt),tt)).

Lemma Q3b : mult Q' (mult A P) = D.
Proof.
  rewrite /mult /= /Mmult /Mone /=.
  apply (coeff_mat_ext_aux 0 0).
  intros i j Hi Hj.
  rewrite coeff_mat_bij => //.
  unfold coeff_mat, plus, mult ; simpl.
  (destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /one /=) ;
  (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field).
Qed.

Lemma Q3c : forall n, pow_n A n = mult P (mult (pow_n D n) Q').
Proof.
  elim => /= [ | n IH].
  rewrite mult_one_l.
  apply sym_eq, Q3a.
  by rewrite -{1}Q3b !mult_assoc (proj1 Q3a) mult_one_l -!mult_assoc IH.
Qed.

(** 4. Terme général et limite de la suite v n *)

Lemma Q4 : forall n, v n = 1 / 6 * (1 + 5 * (94 / 100) ^ n) * v 0
                         + 1 / 6 * (1 - (94 / 100) ^ n) * c 0.
Proof.
  intros n.
  assert (X n = scal (pow_n A n) (X 0)).
    elim: n => [ | n IH] /=.
    by rewrite scal_one.
    by rewrite -scal_assoc -IH.
  assert (pow_n D n = ((1,(0,tt)),
                       (0,((94 / 100)^n,tt),tt))).
    elim: (n) => [ | m IH] //=.
    rewrite IH.
    rewrite /mult /= /Mmult /Mone /=.
    apply (coeff_mat_ext_aux 0 0).
    intros i j Hi Hj.
    rewrite coeff_mat_bij => //.
    unfold coeff_mat, plus, mult ; simpl.
    (destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /one /=) ;
    (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field).
  rewrite Q3c H0 in H.
  apply (proj1 (coeff_mat_ext 0 _ _)) with (i := O) (j := O) in H.
  rewrite {1}/coeff_mat /= in H.
  rewrite H ; repeat (rewrite !/coeff_mat /=).
  rewrite /plus /mult /= ; field.
Qed.

Lemma lim_v : is_lim_seq v (41666 + 2 / 3).
Proof.
  eapply is_lim_seq_ext.
  intros n ; apply sym_eq, Q4.
  eapply is_lim_seq_plus.
  eapply is_lim_seq_mult.
  eapply is_lim_seq_mult.
  apply is_lim_seq_const.
  eapply is_lim_seq_plus.
  apply is_lim_seq_const.
  eapply is_lim_seq_mult.
  apply is_lim_seq_const.
  apply is_lim_seq_geom.
  rewrite Rabs_pos_eq ; lra.
  apply (f_equal (fun x => Some (Finite x))), Rmult_0_r.
  apply (f_equal (fun x => Some (Finite x))), Rplus_0_r.
  apply (f_equal (fun x => Some (Finite x))), Rmult_1_r.
  apply is_lim_seq_const.
  by [].
  eapply is_lim_seq_mult.
  eapply is_lim_seq_mult.
  apply is_lim_seq_const.
  eapply is_lim_seq_minus.
  apply is_lim_seq_const.
  apply is_lim_seq_geom.
  rewrite Rabs_pos_eq ; lra.
  apply (f_equal (fun x => Some (Finite x))), Rminus_0_r.
  apply (f_equal (fun x => Some (Finite x))), Rmult_1_r.
  apply is_lim_seq_const.
  by [].
  apply (f_equal (fun x => Some (Finite x))).
  simpl ; field.
Qed.

Lemma Q4_c : forall n, c n = 250000 - v n.
Proof.
  elim => [ | n /= ->] /= ; field.
Qed.


Lemma lim_c : is_lim_seq c (208333 + 1 / 3).
Proof.
  eapply is_lim_seq_ext.
  intros n ; apply sym_eq, Q4_c.
  eapply is_lim_seq_minus.
  apply is_lim_seq_const.
  by apply lim_v.
  apply (f_equal (fun x => Some (Finite x))).
  simpl ; field.
Qed.
