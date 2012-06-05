Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements.

Open Scope R_scope.

(** * Definitions *)

Inductive Rbar :=
  | Finite : R -> Rbar
  | p_infty : Rbar
  | m_infty : Rbar.
Definition real (x : Rbar) :=
  match x with
    | Finite x => x
    | _ => 0
  end.

(** ** Order *)

Definition Rbar_lt (x y : Rbar) : Prop :=
  match x,y with
    | p_infty, _ | _, m_infty => False
    | m_infty, _ | _, p_infty => True
    | Finite x, Finite y => Rlt x y
  end.
Definition Rbar_gt x y := (Rbar_lt y x).
Definition Rbar_le x y := (Rbar_lt x y \/ x = y).
Definition Rbar_ge x y := (Rbar_le y x).

(** ** Operations *)

Definition Rbar_opp (x : Rbar) :=
  match x with
    | Finite x => Finite (-x)
    | p_infty => m_infty
    | m_infty => p_infty
  end.
Definition Rbar_plus (x y : Rbar) :=
  match x,y with
    | p_infty, m_infty | m_infty, p_infty => Finite 0
    | p_infty, _ | _, p_infty => p_infty
    | m_infty, _ | _, m_infty => m_infty
    | Finite x', Finite y' => Finite (x'+y')
  end.
Definition Rbar_div_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x/y)
    | _ => x
  end.

(** * Compatibilities with Real numbers *)

Lemma Rbar_finite_eq (x y : R) :
  Finite x = Finite y <-> x = y.
Proof.
  split ; intros.
  apply Rle_antisym ; apply Rnot_lt_le ; intro.
  assert (Rbar_lt (Finite y) (Finite x)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; revert H1 ; apply Rlt_irrefl.
  assert (Rbar_lt (Finite x) (Finite y)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; revert H1 ; apply Rlt_irrefl.
  rewrite H ; reflexivity.
Qed.
Lemma Rbar_finite_lt (x y : R) :
  Rbar_lt (Finite x) (Finite y) <-> x < y.
Proof.
  split ; intuition.
Qed.
Lemma Rbar_finite_le (x y : R) :
  Rbar_le (Finite x) (Finite y) <-> x <= y.
Proof.
  split ; intros.
  destruct H.
  apply Rlt_le, (Rbar_finite_lt _ _), H.
  apply Req_le, (Rbar_finite_eq _ _), H.
  destruct H.
  left ; apply (Rbar_finite_lt _ _), H.
  right ; apply (Rbar_finite_eq _ _), H.
Qed.
Lemma Rbar_finite_gt (x y : R) :
  Rbar_gt (Finite x) (Finite y) <-> x > y.
Proof.
  intros.
  apply (Rbar_finite_lt y x).
Qed.
Lemma Rbar_finite_ge (x y : R) :
  Rbar_ge (Finite x) (Finite y) <-> x >= y.
Proof.
  split ; intros.
  apply Rle_ge, (Rbar_finite_le y x), H.
  destruct H.
  left ; apply (Rbar_finite_lt _ _), H.
  right ; apply sym_eq, (Rbar_finite_eq _ _), H.
Qed.

(** * Decidabilities *)

Lemma Rbar_total_order (x y : Rbar) :
  {Rbar_lt x y} + {x = y} + {Rbar_gt x y}.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  destruct (total_order_T r r0) ; intuition.
Qed.
Lemma Rbar_eq_dec (x y : Rbar) :
  {x = y} + {x <> y}.
Proof.
  intros ; destruct (Rbar_total_order x y) as [[H|H]|H].
  right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply Rbar_finite_eq in H ; try apply Rle_not_lt, Req_le ; auto.
  left ; apply H.
  right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply Rbar_finite_eq in H ; apply Rle_not_lt, Req_le ; auto.
Qed.

Lemma Rbar_lt_dec (x y : Rbar) :
  {Rbar_lt x y} + {~Rbar_lt x y}.
Proof.
  destruct (Rbar_total_order x y) as [H|H] ; [ destruct H as [H|H]|].
  left ; auto.
  right ; rewrite H ; clear H ; destruct y ; auto ; apply Rlt_irrefl ; auto.
  right ; revert H ; destruct x as [x | | ] ; destruct y as [y | | ] ; intros H ; auto ; 
  apply Rle_not_lt, Rlt_le ; auto.
Qed.
Lemma Rbar_lt_le_dec (x y : Rbar) :
  {Rbar_lt x y} + {Rbar_le y x}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left ; auto.
  right ; right ; auto.
  right ; left ; auto.
Qed.

Lemma Rbar_le_dec (x y : Rbar) :
  {Rbar_le x y} + {~Rbar_le x y}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left ; left ; auto.
  left ; rewrite H ; clear H ; destruct y as [y | | ] ; right ; auto.
  right ; revert H ; destruct x as [x | | ] ; destruct y as [y | | ] ; auto ; intros H ;
  contradict H ; destruct H as [H|H] ; auto ; [apply Rle_not_lt, Rlt_le ; auto | 
  apply Rbar_finite_eq in H ; rewrite H ; apply Rlt_irrefl | | | ].
  rewrite H ; auto.
  rewrite <- H ; auto.
  rewrite H ; auto.
Qed.
Lemma Rbar_le_lt_dec (x y : Rbar) :
  {Rbar_le x y} + {Rbar_lt y x}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left ; left ; auto.
  left ; rewrite H ; right ; auto.
  right ; auto.
Qed.

(** * Positive and negative propositions *)

Lemma Rbar_lt_not_eq (x y : Rbar) :
  Rbar_lt x y -> x<>y.
Proof.
  destruct x ; destruct y ; simpl ; try easy.
  intros H H0.
  apply Rbar_finite_eq in H0 ; revert H0 ; apply Rlt_not_eq, H.
Qed.

Lemma Rbar_not_le_lt (x y : Rbar) :
  ~ Rbar_le x y -> Rbar_lt y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  apply Rnot_le_lt. contradict H. apply (Rbar_finite_le _ _), H.
  apply H ; left ; apply I.
  apply H ; right ; reflexivity.
  apply H ; left ; apply I.
  apply H ; left ; apply I.
  apply H ; right ; reflexivity.
Qed.
Lemma Rbar_lt_not_le (x y : Rbar) :
  Rbar_lt y x -> ~ Rbar_le x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition ; 
  [ | destruct H0 | destruct H0 | destruct H0] ; try easy.
  contradict H ; apply Rle_not_lt, (Rbar_finite_le _ _), H0.
Qed.
Lemma Rbar_not_lt_le (x y : Rbar) :
  ~ Rbar_lt x y -> Rbar_le y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  apply (Rbar_finite_le _ _), (Rnot_lt_le _ _ H).
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; reflexivity.
  left ; simpl ; auto.
  right ; reflexivity.
Qed.
Lemma Rbar_le_not_lt (x y : Rbar) :
  Rbar_le y x -> ~ Rbar_lt x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition ; contradict H0.
  apply Rle_not_lt, (Rbar_finite_le _ _), H.
  now destruct H.
  now destruct H.
  now destruct H.
Qed.
Lemma Rbar_lt_le (x y : Rbar) :
  Rbar_lt x y -> Rbar_le x y.
Proof.
  intros ; left ; apply H.
Qed.


(** * Transitivity *)
Lemma Rbar_lt_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; intuition.
  apply (Rbar_finite_lt _ _), Rlt_trans with (r2 := r0).
  apply (Rbar_finite_lt _ _), H.
  apply (Rbar_finite_lt _ _), H0.
  contradict H0.
  contradict H.
Qed.
Lemma Rbar_lt_le_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_le y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  apply (Rbar_finite_lt _ _), Rlt_le_trans with (r2 := r0).
  apply (Rbar_finite_lt _ _), H.
  apply (Rbar_finite_le _ _), H0.
  now destruct H0 as [H1|H1] ; contradict H1.
  now destruct H0 as [H1|H1] ; contradict H1.
  now destruct H0 as [H1|H1] ; contradict H1.
  now destruct H0 as [H1|H1] ; contradict H1.
  now destruct H0 as [H1|H1] ; contradict H1.
Qed.
Lemma Rbar_le_lt_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  apply (Rbar_finite_lt _ _), Rle_lt_trans with (r2 := r0).
  apply (Rbar_finite_le _ _), H.
  apply H0.
  now destruct H as [H1|H1] ; contradict H1.
  now destruct H as [H1|H1] ; contradict H1.
  now destruct H as [H1|H1] ; contradict H1.
  now destruct H as [H1|H1] ; contradict H1.
  now destruct H as [H1|H1] ; contradict H1.
Qed.
Lemma Rbar_le_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_le y z -> Rbar_le x z.
Proof.
  intros ; destruct H.
  left ; apply Rbar_lt_le_trans with (1 := H), H0.
  rewrite H ; apply H0.
Qed.
Lemma Rbar_le_antisym (x y : Rbar) :
  Rbar_le x y -> Rbar_le y x -> x = y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  apply (Rbar_finite_eq _ _), Rle_antisym ; apply (Rbar_finite_le _ _) ; [apply H|apply H0].
  now destruct H0 ; contradict H0.
  now destruct H ; contradict H.
  now destruct H ; contradict H.
  now destruct H ; contradict H.
  now destruct H0 ; contradict H0.
  now destruct H0 ; contradict H0.
Qed.

(** * Proprieties on operations *)
(** ** Rbar_opp *)
Lemma Rbar_opp_involutive (x : Rbar) : (Rbar_opp (Rbar_opp x)) = x.
Proof.
  destruct x as [x| | ] ; auto ; simpl ; rewrite Ropp_involutive ; auto.
Qed.
Lemma Rbar_opp_lt (x y : Rbar) : Rbar_lt (Rbar_opp x) (Rbar_opp y) <-> Rbar_lt y x.
Proof.
  destruct x as [x | | ] ; destruct y as [y | | ] ;
  split ; auto ; intro H ; simpl ; try left.
  apply Ropp_lt_cancel ; auto.
  apply Ropp_lt_contravar ; auto.
Qed.
Lemma Rbar_opp_le (x y : Rbar) : Rbar_le (Rbar_opp x) (Rbar_opp y) <-> Rbar_le y x.
Proof.
  split ; intros H ; destruct H.
  apply Rbar_lt_le, Rbar_opp_lt, H.
  right ; rewrite <- (Rbar_opp_involutive x), H, Rbar_opp_involutive ; reflexivity.
  apply Rbar_lt_le, Rbar_opp_lt, H.
  rewrite H ; right ; intuition.
Qed.
Lemma Rbar_opp_eq (x y : Rbar) : (Rbar_opp x) = (Rbar_opp y) <-> x = y.
Proof.
  split ; intros H.
  rewrite <- (Rbar_opp_involutive x), H, Rbar_opp_involutive ; reflexivity.
  rewrite H ; reflexivity.
Qed.

Lemma Rbar_opp_real (x : Rbar) : real (Rbar_opp x) = - real x.
Proof.
  destruct x as [x | | ] ; simpl ; intuition.
Qed.
(** ** Rbar_plus *)
Lemma Rbar_plus_0_r (x : Rbar) : Rbar_plus x (Finite 0) = x.
Proof.
  case: x => //= ; intuition.
Qed.
Lemma Rbar_plus_0_l (x : Rbar) : Rbar_plus (Finite 0) x = x.
Proof.
  case: x => //= ; intuition.
Qed.

Lemma Rbar_plus_comm (x y : Rbar) : Rbar_plus x y = Rbar_plus y x.
Proof.
  case x ; case y ; intuition ; simpl ; rewrite Rplus_comm ; auto.
Qed.

Lemma Rbar_plus_lt_compat (a b c d : Rbar) : 
  Rbar_lt a b -> Rbar_lt c d -> Rbar_lt (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case: a => [a | | ] // ; case: b => [b | | ] // ;
  case: c => [c | | ] // ; case: d => [d | | ] // ;
  apply Rplus_lt_compat.
Qed.
Lemma Rbar_plus_lt_le_compat (a b c d : Rbar) : 
  Rbar_lt a b -> Rbar_le c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case: a => [a | | ] // ; case: b => [b | | ] // ;
  case: c => [c | | ] // ; case: d => [d | | ] // Hab ;
  case => Hcd // ; rewrite ?Hcd //= ; try by left.
  left ; by apply Rplus_lt_compat.
  left ; by apply Rplus_lt_compat_r.
Qed.
Lemma Rbar_plus_le_lt_compat (a b c d : Rbar) : 
  Rbar_le a b -> Rbar_lt c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof.
  move => Hab Hcd ; rewrite (Rbar_plus_comm a c) (Rbar_plus_comm b d) ;
  by apply Rbar_plus_lt_le_compat.
Qed.
Lemma Rbar_plus_le_compat (a b c d : Rbar) : 
  Rbar_le a b -> Rbar_le c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case => [Hab | ->].
  by apply Rbar_plus_lt_le_compat.
  case => [Hcd | ->] ; try by right.
  apply Rbar_plus_le_lt_compat => // ; by right.
Qed.
(** ** Rbar_div_pos *)
Lemma Rbar_div_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_div_pos x z) = (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H ; apply Rbar_finite_eq in H.
  by rewrite H.
  apply Rbar_finite_eq, (Rmult_eq_reg_r (/z)) => // ; 
  by apply Rgt_not_eq, Rinv_0_lt_compat.
Qed.

Lemma Rbar_div_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (/z)) => // ; by apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_r (/z)) => // ; by apply Rinv_0_lt_compat.
Qed.

Lemma Rbar_div_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
  split ; case => H.
  left ; by apply Rbar_div_pos_lt.
  right ; by apply Rbar_div_pos_eq.
  left ; by apply Rbar_div_pos_lt with z.
  right ; by apply Rbar_div_pos_eq with z.
Qed.
