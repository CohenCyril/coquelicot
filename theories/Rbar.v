Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Floor.

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
Coercion Finite : R >-> Rbar.

Definition is_finite (x : Rbar) := Finite (real x) = x.
Lemma is_finite_correct (x : Rbar) :
  is_finite x <-> exists y : R, x = Finite y.
Proof.
  rewrite /is_finite ;
  case: x => /= ; split => // H.
  by exists r.
  by case: H.
  by case: H.
Qed.

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
(** *** Additive *)

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
Definition is_Rbar_plus ( x y z : Rbar) : Prop :=
  match x,y, z with
    | p_infty, m_infty, _ | m_infty, p_infty, _ => False
    | p_infty, _, p_infty | _, p_infty, p_infty => True
    | m_infty, _, m_infty | _, m_infty, m_infty => True
    | Finite x, Finite y, Finite z => x + y = z
    | _, _, _ => False
  end.
Lemma Rbar_plus_correct (x y z : Rbar) :
  is_Rbar_plus x y z -> Rbar_plus x y = z.
Proof.
  case: x => [x | | ] ; case: y => [y | | ] ; case: z => [z | | ] //=.
  by move => ->.
Qed.

Definition Rbar_minus (x y : Rbar) := Rbar_plus x (Rbar_opp y).
Definition is_Rbar_minus (x y z : Rbar) : Prop :=
  is_Rbar_plus x (Rbar_opp y) z.

(** *** Multiplicative *)

Definition Rbar_inv (x : Rbar) : Rbar :=
  match x with
    | Finite x => Finite (/x)
    | _ => Finite 0
  end.

Definition Rbar_mult (x y : Rbar) : Rbar :=
  match x with
    | Finite x => match y with
      | Finite y => Finite (x*y)
      | p_infty => match (Rle_dec 0 x) with
        | left _ => p_infty
        | right _ => m_infty
      end
      | m_infty => match (Rle_dec 0 x) with
        | left _ => m_infty
        | right _ => p_infty
      end
    end
    | p_infty => match y with
      | Finite y => match (Rle_dec 0 y) with
        | left _ => p_infty
        | right _ => m_infty
      end
      | p_infty => p_infty
      | m_infty => m_infty
    end
    | m_infty => match y with
      | Finite y => match (Rle_dec 0 y) with
        | left _ => m_infty
        | right _ => p_infty
      end
      | p_infty => m_infty
      | m_infty => p_infty
    end
  end.
Definition is_Rbar_mult (x y z : Rbar) : Prop :=
  match x with
    | Finite x => match y with
      | Finite y => match z with | Finite z => x*y = z | _ => False end
      | p_infty => match z with | p_infty => 0 < x | m_infty => x < 0 | _ => False end
      | m_infty => match z with | p_infty => x < 0 | m_infty => 0 < x | _ => False end
    end
    | p_infty => match y with
      | Finite y => match z with | p_infty => 0 < y | m_infty => y < 0 | _ => False end
      | p_infty => match z with | p_infty => True | _ => False end
      | m_infty => match z with | m_infty => True | _ => False end
    end
    | m_infty => match y with
      | Finite y =>  match z with | m_infty => 0 < y | p_infty => y < 0 | _ => False end
      | p_infty => match z with | m_infty => True | _ => False end
      | m_infty => match z with | p_infty => True | _ => False end
    end
  end.
Definition Rbar_mult_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x*y)
    | _ => x
  end.

Lemma Rbar_mult_correct (x y z : Rbar) :
  is_Rbar_mult x y z -> Rbar_mult x y = z.
Proof.
  case: x => [x | | ] ; case: y => [y | | ] ; case: z => [z | | ] //= Hm ;
  try case: Rle_dec => // Hp.
  by rewrite Hm.
  contradict Hp ; by apply Rlt_le.
  by apply Rle_not_lt in Hp.
  by apply Rle_not_lt in Hp.
  contradict Hp ; by apply Rlt_le.
  contradict Hp ; by apply Rlt_le.
  by apply Rle_not_lt in Hp.
  by apply Rle_not_lt in Hp.
  contradict Hp ; by apply Rlt_le.
Qed.
Lemma Rbar_mult_pos_correct (x : Rbar) (y : posreal) (z : Rbar) :
  is_Rbar_mult x (Finite y) z -> Rbar_mult_pos x y = z.
Proof.
  case: x => [x | | ] ; case: z => [z | | ] //= Hm ;
  try case: Rle_dec => // Hp.
  by rewrite Hm.
  contradict Hm ; apply Rle_not_lt, Rlt_le, y.
  contradict Hm ; apply Rle_not_lt, Rlt_le, y.
Qed.


Definition Rbar_div (x y : Rbar) : Rbar :=
  Rbar_mult x (Rbar_inv y).
Definition is_Rbar_div (x y z : Rbar) : Prop :=
  is_Rbar_mult x (Rbar_inv y) z.
Definition Rbar_div_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x/y)
    | _ => x
  end.

(** * Compatibility with real numbers *)
(** For equality and order.
The compatibility of addition and multiplication is proved in Rbar_seq *)

Lemma Rbar_finite_eq (x y : R) :
  Finite x = Finite y <-> x = y.
Proof.
  split ; intros.
  apply Rle_antisym ; apply Rnot_lt_le ; intro.
  assert (Rbar_lt (Finite y) (Finite x)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  assert (Rbar_lt (Finite x) (Finite y)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  rewrite H ; reflexivity.
Qed.
Lemma Rbar_finite_neq (x y : R) :
  Finite x <> Finite y <-> x <> y.
Proof.
  split => H ; contradict H ; by apply Rbar_finite_eq.
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

(** * Properties of order *)
(** Many usual properties on real numbers' order are also true for extended real numbers. *)
(** ** Decidability *)

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

(** ** Positive and negative propositions *)

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

(** ** Transitivity *)

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

(** * Properties of operations *)

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

(** the predicate *)

Lemma is_Rbar_plus_comm (x y z : Rbar) :
  is_Rbar_plus x y z <-> is_Rbar_plus y x z.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //=.
  by rewrite Rplus_comm.
Qed.

Lemma is_Rbar_plus_p :
  is_Rbar_plus p_infty p_infty p_infty.
Proof.
  by simpl.
Qed.

Lemma is_Rbar_plus_p_f (x : R) :
  is_Rbar_plus p_infty (Finite x) p_infty.
Proof.
  by simpl.
Qed.
Lemma is_Rbar_plus_f_p (x : R) :
  is_Rbar_plus (Finite x) p_infty p_infty.
Proof.
  by simpl.
Qed.

Lemma is_Rbar_plus_0_r (x : Rbar) :
  is_Rbar_plus x (Finite 0) x.
Proof.
  case: x => [x | | ] //=.
  by apply Rplus_0_r.
Qed.

Lemma is_Rbar_plus_0_l (y : Rbar) :
  is_Rbar_plus (Finite 0) y y.
Proof.
  rewrite is_Rbar_plus_comm ; by apply is_Rbar_plus_0_r.
Qed.

Lemma is_Rbar_plus_opp (x y z : Rbar) :
  is_Rbar_plus (Rbar_opp x) (Rbar_opp y) (Rbar_opp z)
    <-> is_Rbar_plus x y z.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //=.
  rewrite -Ropp_plus_distr ; split => H.
  by rewrite -(Ropp_involutive z) -H Ropp_involutive.
  by rewrite H.
Qed.

(** the function *)

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

(** ** Rbar_minus *)

(** the predicate *)

Lemma is_Rbar_minus_f_p (x : R) :
  is_Rbar_minus (Finite x) p_infty m_infty.
Proof.
  by simpl.
Qed.

Lemma is_Rbar_minus_0_r (x : Rbar) :
  is_Rbar_minus x (Finite 0) x.
Proof.
  case: x => [x | | ] //=.
  apply Rminus_0_r.
Qed.
Lemma is_Rbar_minus_0_l (x : Rbar) :
  is_Rbar_minus (Finite 0) x (Rbar_opp x).
Proof.
  case: x => [x | | ] //=.
  apply Rminus_0_l.
Qed.


(** ** Rbar_mult *)

(** the predicate *)

Lemma is_Rbar_mult_comm (x y z : Rbar) :
  is_Rbar_mult x y z <-> is_Rbar_mult y x z.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //=.
  by rewrite Rmult_comm.
Qed.

Lemma is_Rbar_mult_pos_p (x : Rbar) :
  Rbar_lt (Finite 0) x -> is_Rbar_mult x p_infty p_infty.
Proof.
  case: x => [x | | ] //=.
Qed.

Lemma is_Rbar_mult_opp_l (x y z : Rbar) :
  is_Rbar_mult x (Rbar_opp y) (Rbar_opp z) <-> is_Rbar_mult x y z.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //=.
  rewrite Ropp_mult_distr_r_reverse ; split => H.
  by rewrite -(Ropp_involutive z) -H Ropp_involutive.
  by rewrite H.
  split => H ; apply Ropp_lt_cancel ;
  by rewrite Ropp_0 1?Ropp_involutive.
  split => H ; apply Ropp_lt_cancel ;
  by rewrite Ropp_0 1?Ropp_involutive.
  split => H ; apply Ropp_lt_cancel ;
  by rewrite Ropp_0 1?Ropp_involutive.
  split => H ; apply Ropp_lt_cancel ;
  by rewrite Ropp_0 1?Ropp_involutive.
Qed.
Lemma is_Rbar_mult_opp_r (x y z : Rbar) :
  is_Rbar_mult (Rbar_opp x) y (Rbar_opp z) <-> is_Rbar_mult x y z.
Proof.
  rewrite ?(is_Rbar_mult_comm _ y).
  by apply is_Rbar_mult_opp_l.
Qed.
Lemma is_Rbar_mult_opp (x y z : Rbar) :
  is_Rbar_mult (Rbar_opp x) (Rbar_opp y) z <-> is_Rbar_mult x y z.
Proof.
  by rewrite -is_Rbar_mult_opp_l Rbar_opp_involutive is_Rbar_mult_opp_r.
Qed.

(** ** Rbar_div *)

(** the predicate *)

Lemma is_Rbar_div_f (x y : R) :
  is_Rbar_div (Finite x) (Finite y) (Finite (x/y)).
Proof.
  by simpl.
Qed.
Lemma is_Rbar_div_f_p (x : R) :
  is_Rbar_div (Finite x) p_infty (Finite 0).
Proof.
  simpl ; ring.
Qed.
Lemma is_Rbar_div_f_m (x : R) :
  is_Rbar_div (Finite x) m_infty (Finite 0).
Proof.
  simpl ; ring.
Qed.

(** Rbar_div_pos *)

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

(** ** Rbar_mult_pos *)

Lemma Rbar_mult_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_mult_pos x z) = (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H ; apply Rbar_finite_eq in H.
  by rewrite H.
  apply Rbar_finite_eq, (Rmult_eq_reg_r (z)) => // ; 
  by apply Rgt_not_eq.
Qed.

Lemma Rbar_mult_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (z)) => //.
  apply (Rmult_lt_reg_r (z)) => //.
Qed.

Lemma Rbar_mult_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
  split ; case => H.
  left ; by apply Rbar_mult_pos_lt.
  right ; by apply Rbar_mult_pos_eq.
  left ; by apply Rbar_mult_pos_lt with z.
  right ; by apply Rbar_mult_pos_eq with z.
Qed.

(** * Complements *)

(** ** Rbar_min *)

Definition Rbar_min (x y : Rbar) :=
  match (Rbar_le_dec x y) with
    | left _ => x
    | right _ => y
  end.

(** ** Rbar_abs *)

Definition Rbar_abs (x : Rbar) :=
  match x with
    | Finite x => Finite (Rabs x)
    | _ => p_infty
  end.

Lemma Rbar_abs_lt_between (x y : Rbar) : 
  Rbar_lt (Rbar_abs x) y <-> (Rbar_lt (Rbar_opp y) x /\ Rbar_lt x y).
Proof.
  case: x => [x | | ] ; case: y => [y | | ] /= ; try by intuition.
  by apply Rabs_lt_between.
Qed.

(** ** Rbar_locally *)

Definition Rbar_locally (P : R -> Prop) (a : Rbar) :=
  match a with
    | Finite a => exists delta : posreal, forall x, Rabs (x-a) < delta -> P x
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.

Lemma Rbar_locally_forall (P : R -> Prop) (a : Rbar) :
  (forall x, P x) -> Rbar_locally P a.
Proof.
  case: a => [a | | ] H ;
  exists (mkposreal _ Rlt_0_1) => /= x _ ; by apply H.
Qed.

Lemma Rbar_locally_imply (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally (fun x => P x -> Q x) a -> Rbar_locally P a
    -> Rbar_locally Q a.
Proof.
  case: a => /= [a | | ] [d0 Hpq] [d1 Hp].
  have Hd : 0 < Rmin d0 d1.
    apply Rmin_case ; [by apply d0 | by apply d1].
  exists (mkposreal (Rmin d0 d1) Hd) => /= x H.
  apply: Hpq.
  apply Rlt_le_trans with (1 := H), Rmin_l.
  apply: Hp.
  apply Rlt_le_trans with (1 := H), Rmin_r.
  exists (Rmax d0 d1) => /= x H.
  apply: Hpq.
  apply Rle_lt_trans with (2 := H), Rmax_l.
  apply: Hp.
  apply Rle_lt_trans with (2 := H), Rmax_r.
  exists (Rmin d0 d1) => /= x H.
  apply: Hpq.
  apply Rlt_le_trans with (1 := H), Rmin_l.
  apply: Hp.
  apply Rlt_le_trans with (1 := H), Rmin_r.
Qed.

Lemma Rbar_locally_and (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally P a -> Rbar_locally Q a
    -> Rbar_locally (fun x => P x /\ Q x) a.
Proof.
  case: a => /= [a | | ] [d0 Hp] [d1 Hq].
  have Hd : 0 < Rmin d0 d1.
    apply Rmin_case ; [by apply d0 | by apply d1].
  exists (mkposreal (Rmin d0 d1) Hd) => /= x H ; split.
  apply: Hp.
  apply Rlt_le_trans with (1 := H), Rmin_l.
  apply: Hq.
  apply Rlt_le_trans with (1 := H), Rmin_r.
  exists (Rmax d0 d1) => /= x H ; split.
  apply: Hp.
  apply Rle_lt_trans with (2 := H), Rmax_l.
  apply: Hq.
  apply Rle_lt_trans with (2 := H), Rmax_r.
  exists (Rmin d0 d1) => /= x H ; split.
  apply: Hp.
  apply Rlt_le_trans with (1 := H), Rmin_l.
  apply: Hq.
  apply Rlt_le_trans with (1 := H), Rmin_r.
Qed.

Lemma Rbar_locally_and_1 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally (fun x => P x /\ Q x) a 
    -> Rbar_locally P a.
Proof.
  case: a => /= [a | | ] [d0 Hp] ;
  exists d0 => H ; by apply Hp.
Qed.

Lemma Rbar_locally_and_2 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally (fun x => P x /\ Q x) a 
    -> Rbar_locally Q a.
Proof.
  case: a => /= [a | | ] [d0 Hp] ;
  exists d0 => H ; by apply Hp.
Qed.

Lemma Rbar_locally_or_1 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally P a -> Rbar_locally (fun x => P x \/ Q x) a.
Proof.
  apply Rbar_locally_imply, Rbar_locally_forall => x Hx.
  by left.
Qed.

Lemma Rbar_locally_or_2 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally Q a -> Rbar_locally (fun x => P x \/ Q x) a.
Proof.
  apply Rbar_locally_imply, Rbar_locally_forall => x Hx.
  by right.
Qed.

(** ** A particular subsequence *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + / (INR n + 1)
    | p_infty => INR n
    | m_infty => - INR n
  end.

Lemma Rbar_loc_seq_carac (P : R -> Prop) (x : Rbar) :
  Rbar_locally P x 
    -> (exists N, forall n, (N <= n)%nat -> P (Rbar_loc_seq x n)).
Proof.
  case: x => /= [x | | ] [delta Hp].
(* x \in R *)
  case: (nfloor_ex (/delta)) => [ | N [_ HN]].
  by apply Rlt_le, Rinv_0_lt_compat, delta.
  exists N => n Hn.
  apply Hp.
  ring_simplify (x + / (INR n + 1) - x).
  rewrite Rabs_pos_eq.
  rewrite -(Rinv_involutive delta).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  by apply delta.
  exact: INRp1_pos.
  apply Rlt_le_trans with (1 := HN).
  by apply Rplus_le_compat_r, le_INR.
  by apply Rgt_not_eq, delta.
  by apply Rlt_le, RinvN_pos.
(* x = p_infty *)
  case: (nfloor_ex (Rmax 0 delta)) => [ | N [_ HN]].
  by apply Rmax_l.
  exists (S N) => n Hn.
  apply Hp.
  apply Rle_lt_trans with (1 := Rmax_r 0 _).
  apply Rlt_le_trans with (1 := HN).
  rewrite -S_INR ; by apply le_INR.
(* x = m_infty *)
  case: (nfloor_ex (Rmax 0 (-delta))) => [ | N [_ HN]].
  by apply Rmax_l.
  exists (S N) => n Hn.
  apply Hp.
  rewrite -(Ropp_involutive delta).
  apply Ropp_lt_contravar.
  apply Rle_lt_trans with (1 := Rmax_r 0 _).
  apply Rlt_le_trans with (1 := HN).
  rewrite -S_INR ; by apply le_INR.
Qed.