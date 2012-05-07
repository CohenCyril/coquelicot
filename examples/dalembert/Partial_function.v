Require Import Reals.

Require Import Arithmetique Function1.

Open Scope R_scope.

(** * Partial value *)

Record partial_val := Pval {
  pdom : Type;
  pval : pdom -> R;
  pHeq : forall d1 d2, pval d1 = pval d2
}.

(** * Relations on partial values and partial functions *)

Definition Pval_equal v1 v2 :=
  prod (prod (pdom v2 -> pdom v1) (pdom v1 -> pdom v2)) (forall d1 d2, pval v1 d1 = pval v2 d2).

Definition Pval_extension v1 v2 :=
  prod (pdom v2 -> pdom v1) (forall d1 d2, pval v1 d1 = pval v2 d2).

Definition Pfun_equal (f1 f2 : R -> partial_val) :=
  forall x, Pval_equal (f1 x) (f2 x).

Definition Pfun_extension (f1 f2 : R -> partial_val) :=
  forall x, Pval_extension (f1 x) (f2 x).

(** Pfun_equal is an equivalence relation *)

Lemma Pfun_equal_refl : forall f, Pfun_equal f f.
Proof.
  intros f x ; destruct (f x) as (dom,val,eq).
  split ; [split|]; simpl ; auto.
Qed.

Lemma Pfun_equal_sym : forall f1 f2, Pfun_equal f1 f2 -> Pfun_equal f2 f1.
Proof.
  intros f1 f2 H x.
  split ; [split|]; simpl.
  apply (H x).
  apply (H x).
  intros ; apply sym_equal, (H x).
Qed.

Lemma Pfun_equal_trans : forall f1 f2 f3,
  Pfun_equal f1 f2 -> Pfun_equal f2 f3 -> Pfun_equal f1 f3.
Proof.
  intros f1 f2 f3 H1 H2.
  intro.
  split ; [split|] ; intros.
  apply (H1 x), (H2 x), X.
  apply (H2 x), (H1 x), X.
  rewrite <- ((snd (H2 x)) (fst (fst (H2 x)) d2)).
  apply (H1 x).
Qed.

(** Pfun_extension is an order relation *)

Lemma Pfun_equal_extension : forall f1 f2,
  Pfun_equal f1 f2 -> Pfun_extension f1 f2.
Proof.
  intros f1 f2 H x.
  split ; apply (H x).
Qed.

Lemma Pfun_extension_refl : forall f, Pfun_extension f f.
Proof.
  intros f x.
  split ; simpl ; auto.
  apply (f x).
Qed.

Lemma Pfun_extension_anti_sym : forall f1 f2,
  Pfun_extension f1 f2 -> Pfun_extension f2 f1 -> Pfun_equal f1 f2.
Proof.
  intros f1 f2 H1 H2.
  split ; [split|].
  apply (H1 x).
  apply (H2 x).
  apply (H1 x).
Qed.

Lemma Pfun_extension_trans : forall f1 f2 f3,
  Pfun_extension f1 f2 -> Pfun_extension f2 f3 -> Pfun_extension f1 f3.
Proof.
  intros f1 f2 f3 H1 H2.
  split ; intros.
  apply (H1 x), (H2 x), X.
  rewrite <- ((snd (H2 x)) (fst (H2 x) d2)).
  apply (H1 x).
Qed.

(** * Definition of basics operations on partial functions *)

(** Partial and total functions *)

Definition Pfun_eval_a_b (f : R -> partial_val) (a b : R)
  (pr : forall y, Rmin a b <= y <= Rmax a b -> pdom (f y)) x :=
  match (Rle_dec (Rmin a b) x) with
    | left Ha =>
    match (Rle_dec x (Rmax a b)) with
      | left Hb => pval (f x) (pr x (Rle_le _ _ _ Ha Hb))
      | _ => pval (f (Rmax a b))
        (pr (Rmax a b) (Rle_le _ _ _ (Rmin_Rmax a b) (Rle_refl (Rmax a b))))
    end
    | _ => pval (f (Rmin a b))
        (pr (Rmin a b) (Rle_le _ _ _ (Rle_refl (Rmin a b)) (Rmin_Rmax a b)))
  end.

Definition Pval_val (v : R) : partial_val := Pval True (fun _ => v) (fun _ _ => refl_equal v).

Definition Pfun_fun (f : R -> R) x : partial_val := Pval_val (f x).

(** Basic functions and operations on partial_var *)

Definition Pval_plus v1 v2 :=
  Pval (prod (pdom v1) (pdom v2)) (fun d => pval v1 (fst d) + pval v2 (snd d))
    (fun d1 d2 => Rplus_eq_compat _ _ _ _ (pHeq v1 (fst d1) (fst d2)) (pHeq v2 (snd d1) (snd d2))).

Definition Pval_opp v :=
  Pval (pdom v) (fun d => - pval v d) (fun d1 d2 => Ropp_eq_compat _ _ (pHeq v d1 d2)).

Definition Pval_minus v1 v2 :=
  Pval_plus v1 (Pval_opp v2).

Definition Pval_mult v1 v2 :=
  Pval (prod (pdom v1) (pdom v2)) (fun d => pval v1 (fst d) * pval v2 (snd d))
    (fun d1 d2 => Rmult_eq_compat _ _ _ _ (pHeq v1 (fst d1) (fst d2)) (pHeq v2 (snd d1) (snd d2))).

Definition Pval_scal (a : R) v :=
  Pval_mult (Pval_val a) v.

Lemma Pfun_app_Heq :
  forall f x (d1 d2 : { d : pdom x & pdom (f (pval x d)) }),
  pval (f (pval x (projT1 d1))) (projT2 d1) = pval (f (pval x (projT1 d2))) (projT2 d2).
Proof.
intros f (xdom, xval, xHeq).
simpl.
intros (d1, H1) (d2, H2).
simpl.
revert H1 H2.
rewrite (xHeq d1 d2).
intros H1 H2.
now rewrite (pHeq (f (xval d2)) H1 H2).
Qed.
Definition Pfun_app f x :=
  Pval { d : pdom x & pdom (f (pval x d)) } (fun d => pval (f (pval x (projT1 d))) (projT2 d))
    (Pfun_app_Heq f x).

(** * Continuity *)

Definition Pfun_continuity_pt (f : R -> partial_val) (x : R) :=
  { pr_x : pdom (f x) |
    forall eps : posreal, exists delta : posreal,
    forall (y : R), Rabs (y - x) < delta -> exists pr_y : pdom (f y),
    Rabs (pval (f y) pr_y - pval (f x) pr_x) < eps }.

Definition Pfun_continuity f := forall x:R, Pfun_continuity_pt f x.

(* Si on a le temps de rajouter la dérivée des intégrales à paramètre
(** Uniform continuity *)

Definition Pfun_unif_cont (f : R -> partial_val) (dom : R -> Type) :=
  forall eps : posreal, exists delta : posreal, forall (x y : R), 
    dom x -> dom y -> Rabs (y - x) < delta -> 
    { pr_x : pdom (f x) | exists pr_y : pdom (f y),
      Rabs (pval (f y) pr_y - pval (f x) pr_x) < eps}. *)
(** Extension and equality *)

Lemma Pfun_continuity_pt_extension : forall (f1 f2 : R -> partial_val) (x : R),
  Pfun_extension f1 f2 -> Pfun_continuity_pt f2 x -> Pfun_continuity_pt f1 x.
Proof.
  intros f1 f2 x H Cf2.
  destruct Cf2 as (pr2_x, Cf2).
  exists (fst (H x) pr2_x) ; intros.
  elim (Cf2 eps) ; clear Cf2 ; intros delta Cf2.
  exists delta.
  intros y Hy.
  elim (Cf2 y Hy) ; clear Cf2 ; intros pr2_y Cf2.
  exists (fst (H y) pr2_y).
  rewrite (snd (H x) _ pr2_x).
  rewrite (snd (H y) _ pr2_y).
  apply Cf2.
Qed.

Lemma Pfun_continuity_pt_equal : forall (f1 f2 : R -> partial_val) (x : R),
  Pfun_equal f1 f2 ->
    (Pfun_continuity_pt f2 x -> Pfun_continuity_pt f1 x).
Proof.
  intros.
  apply (Pfun_continuity_pt_extension f1 f2).
  apply Pfun_equal_extension.
  apply X.
  apply X0.
Qed.

(** Partial and total functions *)

Lemma Pfun_continuity_pt_fun_0 (f : R -> R) (x : R) :
  continuity_pt f x -> Pfun_continuity_pt (Pfun_fun f) x.
Proof.
  intros.
  apply equiv_cont_pt in H.
  unfold Pfun_fun.
  unfold Pfun_continuity_pt.
  exists I.
  simpl ; intros.
  elim (H eps) ; clear H ; intros delta Cf.
  exists delta.
  intros.
  exists I ; intros.
  apply Cf.
  apply H.
Qed.
Lemma Pfun_continuity_pt_fun_1 (f : R -> R) (x : R) :
  Pfun_continuity_pt (Pfun_fun f) x -> continuity_pt f x.
Proof.
  intros (dom_x,Cf).
  apply (equiv_cont_pt f x).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  elim (Cf y H) ; clear Cf ; intros Df' Cf.
  apply Cf.
Qed.
Lemma Pfun_continuity_pt_fun (f : R -> R) (x : R) :
  prod (continuity_pt f x -> Pfun_continuity_pt (Pfun_fun f) x)
    (Pfun_continuity_pt (Pfun_fun f) x -> continuity_pt f x).
Proof.
  split ; intros Cf.
  apply (Pfun_continuity_pt_fun_0 f x Cf).
  apply (Pfun_continuity_pt_fun_1 f x Cf).
Qed.

Lemma Pfun_continuity_pt_eval_a_b_0 : forall f a b x pr,
  Rmin a b <= x <= Rmax a b -> Pfun_continuity_pt f x ->
  continuity_pt (Pfun_eval_a_b f a b pr) x.
Proof.
  intros f a0 b0 x.
  set (a := Rmin a0 b0) ; set (b := Rmax a0 b0).
  intros pr Hx (pr_x,Cf).
  apply (equiv_cont_pt _ x).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  unfold Pfun_eval_a_b ; fold a b.
  exists delta ; intros.
  destruct (Rle_dec a x).
  destruct (Rle_dec x b).
  rewrite (pHeq _ _ pr_x).
  destruct (Rle_dec a y).
  destruct (Rle_dec y b).
  elim (Cf _ H) ; clear Cf ; intros pr_y Cf.
  rewrite (pHeq _ _ pr_y).
  apply Cf.
  assert (Rabs (b-x) < delta).
    apply Rnot_le_lt in n.
    apply (Rle_lt_trans _ (Rabs (y-x))).
    repeat rewrite Rabs_right.
    unfold Rminus ; apply Rplus_le_compat_r ; apply Rlt_le ; apply n.
    apply Rge_minus ; apply Rle_ge ; apply Rlt_le ;
    apply (Rle_lt_trans _ _ _ r0 n).
    apply Rge_minus ; apply Rle_ge ; apply r0.
    apply H.
  elim (Cf _ H0) ; clear Cf ; intros pr_b Cf.
  rewrite (pHeq _ _ pr_b).
  apply Cf.
  assert (Rabs (a-x) < delta).
    apply Rnot_le_lt in n.
    apply (Rle_lt_trans _ (Rabs (y-x))).
    repeat rewrite Rabs_left1.
    apply Ropp_le_contravar ;
    unfold Rminus ; apply Rplus_le_compat_r ; apply Rlt_le ; apply n.
    apply Rle_minus ; apply Rlt_le ;
    apply (Rlt_le_trans _ _ _ n r).
    apply Rle_minus ; apply r.
    apply H.
  elim (Cf _ H0) ; clear Cf ; intros pr_a Cf.
  rewrite (pHeq _ _ pr_a).
  apply Cf.
  elim n ; apply Hx.
  elim n ; apply Hx.
Qed.
Lemma Pfun_continuity_pt_eval_a_b_1 : forall f a b x,
  forall pr,
  Rmin a b < x < Rmax a b -> continuity_pt (Pfun_eval_a_b f a b pr) x
   -> Pfun_continuity_pt f x.
Proof.
  intros f a0 b0 x.
  set (a := Rmin a0 b0) ; set (b := Rmax a0 b0).
  intros pr H Cf.
  apply equiv_cont_pt in Cf.
  assert (pr_x : pdom (f x)).
    apply pr.
    split ; apply Rlt_le ; apply H.
  exists pr_x ; intros.
  elim (Cf eps) ; clear Cf ; intros d0 Cf.
  assert (Hd : 0 < Rmin d0 (Rmin (x-a) (b-x))).
    apply Rmin_pos ; [apply d0 |
    apply Rmin_pos ; apply Rlt_Rminus ; apply H].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (a <= y <= b).
    split ; apply Rlt_le.
    apply Ropp_lt_cancel ; apply (Rplus_lt_reg_r x).
    apply (Rle_lt_trans _ (Rabs (y-x))).
    rewrite <- Ropp_minus_distr', Rabs_Ropp.
    apply Rabs_maj1.
    apply (Rlt_le_trans _ (Rmin (x-a) (b-x))).
    apply (Rlt_le_trans _ delta).
    apply H0.
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_l.
    apply (Rplus_lt_reg_r (-x)) ; repeat rewrite (Rplus_comm (-x)).
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj1.
    apply (Rlt_le_trans _ (Rmin (x-a) (b-x))).
    apply (Rlt_le_trans _ delta).
    apply H0.
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_r.
  assert (pr_y : pdom (f y)).
    apply pr.
    apply H1.
  exists pr_y.
  assert (Pfun_eval_a_b f a0 b0 pr y = pval (f y) pr_y).
    unfold Pfun_eval_a_b.
    fold a b.
    destruct (Rle_dec a y).
    destruct (Rle_dec y b).
    apply (pHeq (f y)).
    elim n ; apply H1.
    elim n ; apply H1.
    rewrite <- H2 ; clear H2.
  assert (Pfun_eval_a_b f a0 b0 pr x = pval (f x) pr_x).
    unfold Pfun_eval_a_b.
    fold a b.
    destruct (Rle_dec a x).
    destruct (Rle_dec x b).
    apply (pHeq (f x)).
    elim n ; apply Rlt_le ; apply H.
    elim n ; apply Rlt_le ; apply H.
    rewrite <- H2 ; clear H2.
  apply Cf.
  apply (Rlt_le_trans _ _ _ H0).
    unfold delta ; simpl ; apply Rmin_l.
Qed.
Lemma Pfun_continuity_pt_eval_a_b : forall f a b x,
  forall pr,
  Rmin a b < x < Rmax a b ->
  prod (Pfun_continuity_pt f x -> continuity_pt (Pfun_eval_a_b f a b pr) x)
    (continuity_pt (Pfun_eval_a_b f a b pr) x -> Pfun_continuity_pt f x).
Proof.
  split.
  apply Pfun_continuity_pt_eval_a_b_0.
    split ; apply Rlt_le ; apply H.
  apply Pfun_continuity_pt_eval_a_b_1.
    apply H.
Qed.

Lemma Pfun_continuity_eval_a_b : forall f a b,
  forall pr,
  (forall y, Rmin a b <= y <= Rmax a b -> Pfun_continuity_pt f y)
  -> continuity (Pfun_eval_a_b f a b pr).
Proof.
  intros f a0 b0 ; set (a := Rmin a0 b0) ; set (b := Rmax a0 b0).
  intros ; intro x.
  destruct (Rle_lt_dec a x).
  destruct (Rle_lt_dec x b).
    apply Pfun_continuity_pt_eval_a_b_0.
    split ; [apply r | apply r0].
    apply X.
    split ; [apply r | apply r0]. 

  apply (equiv_cont_pt _ x).
  unfold Pfun_eval_a_b ; fold a b.
  elim (X b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) ;
    clear X ; intros pr_b Cf.
  intros eps ; elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  rewrite (pHeq _ _ pr_b).
  destruct (Rle_dec a x).
  destruct (Rle_dec x b). 

  apply Rlt_not_le in r0 ; elim r0 ; apply r2. 

  destruct (Rle_dec a y).
  destruct (Rle_dec y b).
  assert (Rabs (y-b) < delta).
    apply (Rlt_trans _ (Rabs (y-x))).
    rewrite Rabs_left1. rewrite Rabs_left.
    repeat rewrite Ropp_minus_distr'.
    unfold Rminus ; apply Rplus_lt_compat_r.
    apply r0.
    apply Rlt_minus ; apply (Rle_lt_trans _ b _ r3 r0).
    apply Rle_minus ; apply r3.
    apply H.
  elim (Cf _ H0) ; clear Cf ; intros pr_y Cf.
  rewrite (pHeq _ _ pr_y).
  apply Cf.
  rewrite Rminus_eq0, Rabs_R0 ; apply eps.
  assert (Rabs (a-b) < delta).
    apply (Rlt_trans _ (Rabs (y-x))).
    rewrite Rabs_left1. rewrite Rabs_left.
    repeat rewrite Ropp_minus_distr'.
    unfold Rminus ; apply Rplus_lt_compat.
    apply r0.
    apply Ropp_lt_contravar.
    apply Rnot_le_lt in n0 ; apply n0.
    apply Rlt_minus ; apply (Rlt_le_trans _ a) ;
    [apply Rnot_le_lt in n0 ; apply n0| apply r1].
    apply Rle_minus ; apply Rmin_Rmax.
    apply H.
  elim (Cf _ H0) ; clear Cf ; intros pr_a Cf.
  rewrite (pHeq _ _ pr_a) ; apply Cf. 

  elim n ; apply r.

  apply (equiv_cont_pt _ x).
  unfold Pfun_eval_a_b ; fold a b.
  elim (X a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) ;
    clear X ; intros pr_a Cf.
  intros eps ; elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  rewrite (pHeq _ _ pr_a).
  destruct (Rle_dec a x).
  destruct (Rle_dec x b). 

  assert (~ a <= x).
    apply Rlt_not_le.
    apply r.
    elim H0 ; apply r0. 

  assert (~ a <= x).
    apply Rlt_not_le.
    apply r.
    elim H0 ; apply r0. 

  destruct (Rle_dec a y).
  destruct (Rle_dec y b).
  assert (Rabs (y-a) < delta).
    apply (Rlt_trans _ (Rabs (y-x))).
    rewrite Rabs_right. rewrite Rabs_right.
    unfold Rminus ; apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply r.
    apply Rge_minus ; apply Rle_ge ; apply Rlt_le ; apply (Rlt_le_trans _ a _ r r0).
    apply Rge_minus ; apply Rle_ge ; apply r0.
    apply H.
  elim (Cf _ H0) ; clear Cf ; intros pr_y Cf.
  rewrite (pHeq _ _ pr_y).
  apply Cf.
  assert (Rabs (b-a) < delta).
    apply (Rlt_trans _ (Rabs (y-x))).
    rewrite Rabs_right. rewrite Rabs_right.
    unfold Rminus ; apply Rplus_lt_compat.
    apply Rnot_le_lt in n0 ; apply n0.
    apply Ropp_lt_contravar.
    apply r.
    apply Rge_minus ; apply Rle_ge, Rlt_le ; apply (Rlt_le_trans _ a) ;
    [apply Rnot_le_lt in n0 ; apply r| apply r0].
    apply Rge_minus, Rle_ge ; apply Rmin_Rmax.
    apply H.
  elim (Cf _ H0) ; clear Cf ; intros pr_b Cf.
  rewrite (pHeq _ _ pr_b) ; apply Cf.
  rewrite Rminus_eq0, Rabs_R0 ; apply eps.
Qed.

(** Basic functions ans operations *)

Lemma Pfun_continuity_pt_const : forall (a : R) (x : R),
  Pfun_continuity_pt (Pfun_fun (fct_cte a)) x.
Proof.
  intros.
  apply (Pfun_continuity_pt_fun _ x).
  apply continuity_pt_const.
  unfold constant, fct_cte ;
  intros _ _ ; ring.
Qed.

Lemma Pfun_continuity_pt_id : forall x, Pfun_continuity_pt (Pfun_fun id) x.
Proof.
  intros.
  apply (Pfun_continuity_pt_fun _ x).
  apply continuity_pt_id.
Qed.

Lemma Pfun_continuity_pt_expr : forall (f g : R -> partial_val) (x : R) (d : posreal),
  (forall y, Rabs (y-x) < d -> {pr_f : pdom (f y) & { pr_g : pdom (g y)|
    pval _ pr_f = pval _ pr_g}}) -> Pfun_continuity_pt f x
    -> Pfun_continuity_pt g x.
Proof.
  intros.
  destruct X0 as (pr_x,Cf).
  assert ({pr_x' : pdom (g x)| pval _ pr_x = pval _ pr_x'}).
    assert (Rabs (x-x) < d).
    rewrite Rminus_eq0, Rabs_R0 ;
    apply d.
    elim (X x H) ; clear H ; intros pr_f (pr_g,H).
    exists pr_g.
    rewrite <- H ; apply (pHeq (f x)).
  exists (proj1_sig X0) ; intros.
  elim (Cf eps) ; clear Cf ; intros d0 Cf.
  assert (Hd : 0 < Rmin d d0).
    apply Rmin_pos ; [apply d | apply d0].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (y-x) < d0).
    apply (Rlt_le_trans _ _ _ H).
    unfold delta ; simpl ; apply Rmin_r.
  elim (Cf _ H0) ; clear H0 Cf ; intros pr_y Cf.
  assert ({pr_y' : (pdom (g y))| pval _ pr_y = pval _ pr_y'}).
    assert (Rabs (y-x) < d).
    apply (Rlt_le_trans _ _ _ H).
    unfold delta ; simpl ; apply Rmin_l.
    elim (X _ H0) ; clear X ; intros pr_f (pr_g,X).
    exists pr_g.
    rewrite <- X ; apply (pHeq (f y)).
  exists (proj1_sig X1).
  rewrite <- (proj2_sig X1).
  rewrite <- (proj2_sig X0).
  apply Cf.
Qed.

Lemma Pfun_continuity_pt_plus : forall (f1 f2 : R -> partial_val) (x : R),
  Pfun_continuity_pt f1 x -> Pfun_continuity_pt f2 x
    -> Pfun_continuity_pt (fun x => Pval_plus (f1 x) (f2 x)) x.
Proof.
  intros f1 f2 x (pr1_x,Cf1) (pr2_x,Cf2).
  exists (pr1_x,pr2_x).
  intros.
  assert (Heps2 : 0 < eps/2).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rlt_R0_R2.
    set (eps2 := mkposreal _ Heps2).
  elim (Cf1 eps2) ; clear Cf1 ; intros delta1 Cf1.
  elim (Cf2 eps2) ; clear Cf2 ; intros delta2 Cf2.
  assert (Hdelta : 0 < Rmin delta1 delta2).
    apply Rmin_pos ;
    [ apply delta1 |
    apply delta2].
    set (delta := mkposreal _ Hdelta).
  exists delta.
  intros.
  assert (Rabs (y - x) < delta1).
    apply (Rlt_le_trans _ _ _ H).
    unfold delta ; simpl ; apply Rmin_l.
  elim (Cf1 y H0) ; clear Cf1 H0 ; intros pr1_y Cf1.
  assert (Rabs (y - x) < delta2).
    apply (Rlt_le_trans _ _ _ H).
    unfold delta ; simpl ; apply Rmin_r.
  elim (Cf2 y H0) ; clear Cf2 H0 ; intros pr2_y Cf2.
  exists (pr1_y,pr2_y) ; simpl.
  apply (Rle_lt_trans _ (Rabs (pval _ pr1_y - pval _ pr1_x) +
    Rabs ((pval _ pr2_y - pval _ pr2_x)))).
    assert ((pval (f1 y) pr1_y + pval (f2 y) pr2_y -
      (pval (f1 x) pr1_x + pval (f2 x) pr2_x)) =
      (pval (f1 y) pr1_y - pval (f1 x) pr1_x) +
      (pval (f2 y) pr2_y - pval (f2 x) pr2_x)).
      ring.
      rewrite H0 ; clear H0.
    apply Rabs_triang.
  rewrite (double_var eps).
  apply Rplus_lt_compat.
  apply Cf1.
  apply Cf2.
Qed.

Lemma Pfun_continuity_pt_opp : forall (f : R -> partial_val) (x : R),
  Pfun_continuity_pt f x -> Pfun_continuity_pt (fun x => Pval_opp (f x)) x.
Proof.
  intros f x (pr_x,Cf).
  exists pr_x ; intros.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta.
  intros.
  elim (Cf y H) ; clear Cf ; intros pr_y Cf.
  exists pr_y ; simpl ; intros.
  assert ((- pval _ pr_y - - pval _ pr_x) = -(pval _ pr_y - pval _ pr_x)).
    ring.
    rewrite H0 ; clear H0.
  rewrite Rabs_Ropp.
  apply Cf.
Qed.

Lemma Pfun_continuity_pt_minus : forall (f1 f2 : R -> partial_val) (x : R),
  Pfun_continuity_pt f1 x -> Pfun_continuity_pt f2 x
    ->Pfun_continuity_pt (fun x => Pval_minus (f1 x) (f2 x)) x.
Proof.
  intros.
  apply Pfun_continuity_pt_plus.
  apply X.
  apply Pfun_continuity_pt_opp.
  apply X0.
Qed.

Lemma Pfun_continuity_pt_mult : forall (f1 f2 : R -> partial_val) (x : R),
  Pfun_continuity_pt f1 x -> Pfun_continuity_pt f2 x
    -> Pfun_continuity_pt (fun x => Pval_mult (f1 x) (f2 x)) x.
Proof.
  intros f1 f2 x (pr1_x,Cf1) (pr2_x,Cf2).
  exists (pr1_x,pr2_x).
  intros.
  assert (Heps1 : 0 < Rmin (eps/(2*(Rabs (pval _ pr2_x) + eps))) eps).
    apply Rmin_pos.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    rewrite Rplus_comm.
    apply Rplus_lt_le_0_compat.
    apply eps.
    apply Rabs_pos.
    apply eps.
    set (eps1 := mkposreal _ Heps1).
  elim (Cf1 eps1) ; clear Cf1 ; intros delta1 Cf1.
  assert (Heps2 : 0 < Rmin (eps/(2*(Rabs (pval _ pr1_x) + eps))) eps).
    apply Rmin_pos.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    rewrite Rplus_comm.
    apply Rplus_lt_le_0_compat.
    apply eps.
    apply Rabs_pos.
    apply eps.
    set (eps2 := mkposreal _ Heps2).
  elim (Cf2 eps2) ; clear Cf2 ; intros delta2 Cf2.
  assert (Hdelta : 0 < Rmin delta1 delta2).
    apply Rmin_pos.
    apply delta1.
    apply delta2.
    set (delta := mkposreal _ Hdelta).
  exists delta ;
  intros.
  assert (Rabs (y - x) < delta1).
    apply (Rlt_le_trans _ _ _ H).
    unfold delta ; simpl ; apply Rmin_l.
  elim (Cf1 y H0) ; clear Cf1 H0 ; intros pr1_y Cf1.
  assert (Rabs (y - x) < delta2).
    apply (Rlt_le_trans _ _ _ H).
    unfold delta ; simpl ; apply Rmin_r.
  elim (Cf2 y H0) ; clear Cf2 H0 ; intros pr2_y Cf2.
  exists (pr1_y,pr2_y) ; simpl.
  apply (Rle_lt_trans _ (Rabs (pval _ pr1_y *
    (pval _ pr2_y - pval _ pr2_x)) + Rabs (
    pval _ pr2_x * (pval _ pr1_y - pval _ pr1_x)))).
    assert ((pval (f1 y) pr1_y * pval (f2 y) pr2_y -
      pval (f1 x) pr1_x * pval (f2 x) pr2_x) =
      (pval (f1 y) pr1_y * (pval (f2 y) pr2_y - pval (f2 x) pr2_x)) +
      (pval (f2 x) pr2_x * (pval (f1 y) pr1_y - pval (f1 x) pr1_x))).
      ring.
      rewrite H0 ; clear H0.
    apply Rabs_triang.
  rewrite (double_var eps).
  apply Rplus_lt_compat ;

  rewrite Rabs_mult.
  apply (Rlt_le_trans _ ((Rabs (pval _ pr1_x) + eps)*eps2)).
  apply Rmult_le_0_lt_compat.
  apply Rabs_pos.
  apply Rabs_pos.
  rewrite Rplus_comm.
  rewrite <- (Rplus_0_r (Rabs (pval _ pr1_y))).
  rewrite <- (Rplus_opp_l (Rabs (pval _ pr1_x))).
  rewrite <- Rplus_assoc.
  apply Rplus_lt_compat_r.
  apply (Rle_lt_trans _ (Rabs (pval _ pr1_y - pval _ pr1_x))).
  apply Rabs_triang_inv.
  apply (Rlt_le_trans _ eps1).
  apply Cf1.
  unfold eps1 ; simpl ; apply Rmin_r.
  apply Cf2.
  rewrite Rmult_comm ; apply (Rle_div2 _ _ _).
  apply Rlt_gt ; apply Rplus_le_lt_0_compat.
  apply Rabs_pos.
  apply eps.
  unfold Rdiv ; rewrite Rmult_assoc ; rewrite <- Rinv_mult_distr.
  unfold eps2 ; simpl ; apply Rmin_l.
  apply sym_not_eq ; apply Rlt_not_eq ; apply Rlt_R0_R2.
  apply sym_not_eq ; apply Rlt_not_eq ; apply Rplus_le_lt_0_compat.
  apply Rabs_pos.
  apply eps.

  apply (Rlt_le_trans _ ((Rabs (pval _ pr2_x) + eps)*(eps / (2 * (Rabs (pval _ pr2_x) + eps))))).
  apply Rmult_le_0_lt_compat.
  apply Rabs_pos.
  apply Rabs_pos.
  rewrite <- (Rplus_0_r (Rabs (pval _ pr2_x))).
  apply Rplus_le_lt_compat.
  apply Req_le ; ring.
  apply eps.
  apply (Rlt_le_trans _ (eps1)).
  apply Cf1.
  unfold eps1 ; simpl ; apply Rmin_l.
  apply Req_le.
  field.
  apply Rgt_not_eq.
  apply Rlt_gt.
  rewrite Rplus_comm.
  apply Rplus_lt_le_0_compat.
  apply eps.
  apply Rabs_pos.
Qed.

Lemma Pfun_continuity_pt_scal : forall (a:R) (f : R -> partial_val) (x : R),
  Pfun_continuity_pt f x -> Pfun_continuity_pt (fun x => Pval_scal a (f x)) x.
Proof.
  intros.
  apply Pfun_continuity_pt_mult.
  apply Pfun_continuity_pt_const.
  apply X.
Qed.

Lemma Pfun_continuity_pt_comp : forall (f1 f2 : R -> partial_val) (x : R),
  Pfun_continuity_pt f2 x -> (forall d, Pfun_continuity_pt f1 (pval (f2 x) d)) ->
    Pfun_continuity_pt (fun x => Pfun_app f1 (f2 x)) x.
Proof.
  intros f1 f2 x (pr2_x,Cf2) Cf1.
  elim (Cf1 pr2_x) ; clear Cf1 ; intros pr1_x Cf1.
  assert (pr_x : {d : pdom (f2 x) &  pdom (f1 (pval (f2 x) d))}).
    exists pr2_x.
    apply pr1_x.
  exists pr_x ; simpl ; intros.
  elim (Cf1 eps) ; clear Cf1 ; intros delta Cf1.
  elim (Cf2 delta) ; clear Cf2 ; intros delta' Cf2.
  exists delta'.
  intros.
  elim (Cf2 y H) ; clear Cf2 H ; intros pr2_y Cf2.
  assert (Rabs (pval _ pr2_y - pval _ pr2_x) < delta).
    apply Cf2.
  elim (Cf1 (pval _ pr2_y) H) ; clear Cf1 H ; intros pr1_y Cf1.
  assert (pr_y : {d : pdom (f2 y) &  pdom (f1 (pval (f2 y) d))}).
    exists pr2_y.
    apply pr1_y.
    exists pr_y.
  assert (pval _ (projT2 pr_y) = pval _ pr1_y).
    destruct pr_y as (pr2'_y,pr1'_y) ; simpl.
    revert pr1'_y.
    rewrite (pHeq _ _ pr2_y).
    intros ; apply (pHeq _ _ pr1_y).
    rewrite H ; clear H.
  assert (pval _ (projT2 pr_x) = pval _ pr1_x).
    destruct pr_x as (pr2'_x,pr1'_x) ; simpl.
    revert pr1'_x.
    rewrite (pHeq _ _ pr2_x).
    intros ; apply (pHeq _ _ pr1_x).
    rewrite H ; clear H.
  apply Cf1.
Qed.

(** * Differentiability in R *)

(** First derivative *)

Definition Pfun_derivable_pt_lim (f : R -> partial_val) (x l : R) :=
  { pr_x : pdom (f x) |
    forall eps : posreal, exists delta : posreal,
    forall y, Rabs (y-x) < delta -> exists pr_y : pdom (f y),
    Rabs ((pval (f y) pr_y - pval (f x) pr_x) - l * (y-x)) <= eps * Rabs (y-x) }.

Lemma Pfun_derive_unique :
  forall (f : R -> partial_val) (x l1 l2:R),
    Pfun_derivable_pt_lim f x l1 -> Pfun_derivable_pt_lim f x l2 -> l1 = l2.
Proof.
  intros f x l1 l2 (pr_x,Df1) (pr'_x,Df2).
  destruct (f x) as (fx_dom,fx_val,fx_eq).
  simpl in *.
  apply Req_le_aux.
  intros.
  rewrite (fx_eq _ pr_x) in Df2 ; clear pr'_x.
  assert (Heps' : 0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (eps' := mkposreal _ Heps').
  elim (Df1 eps') ; clear Df1 ; intros delta1 Df1.
  elim (Df2 eps') ; clear Df2 ; intros delta2 Df2.
  assert (Hdelta : 0 < Rmin delta1 delta2).
    apply Rmin_pos ; [apply delta1 | apply delta2].
    set (delta := mkposreal _ Hdelta).
    set (y := x + delta/2).
  assert (Rabs (y - x) < delta1).
    assert (Rabs (y-x) = delta/2).
      assert ((y-x) = delta/2).
        unfold y ; ring.
        rewrite H.
      apply Rabs_right.
      apply Rgt_ge ; apply Rlt_gt ; apply Rdiv_lt_0_compat ;
      [apply delta | apply Rlt_R0_R2].
      rewrite H.
      apply (Rlt_le_trans _ delta) ; [| unfold delta ; simpl ; apply Rmin_l].
      rewrite <- (Rplus_0_r (delta/2)).
      rewrite (double_var delta).
      apply Rplus_le_lt_compat.
      apply Req_le ; field.
      apply Rdiv_lt_0_compat ; [apply delta | apply Rlt_R0_R2].
  elim (Df1 y H) ; clear Df1 H ; intros pr_y Df1.
  assert (Rabs (y - x) < delta2).
    assert (Rabs (y-x) = delta/2).
      assert ((y-x) = delta/2).
        unfold y ; ring.
        rewrite H.
      apply Rabs_right.
      apply Rgt_ge ; apply Rlt_gt ; apply Rdiv_lt_0_compat ;
      [apply delta | apply Rlt_R0_R2].
      rewrite H.
      apply (Rlt_le_trans _ delta) ; [| unfold delta ; simpl ; apply Rmin_r].
      rewrite <- (Rplus_0_r (delta/2)).
      rewrite (double_var delta).
      apply Rplus_le_lt_compat.
      apply Req_le ; field.
      apply Rdiv_lt_0_compat ; [apply delta | apply Rlt_R0_R2].
  elim (Df2 y H) ; clear Df2 H ; intros pr_y' Df2.
  destruct (f y) as (fy_dom,fy_val,fy_eq).
  simpl in *.
  rewrite (fy_eq _ pr_y) in Df2 ; clear pr_y'.
  apply (Rmult_le_reg_r (Rabs (y-x))).
    assert (Rabs (y-x) = delta/2).
      assert ((y-x) = delta/2).
        unfold y ; simpl ; ring.
        rewrite H.
      apply Rabs_right.
      apply Rgt_ge ; apply Rlt_gt ; apply Rdiv_lt_0_compat ;
      [apply delta | apply Rlt_R0_R2].
      rewrite H.
      apply Rdiv_lt_0_compat ; [apply delta | apply Rlt_R0_R2].
  apply (Rle_trans _ (Rabs (fy_val pr_y - fx_val pr_x - l1 * (y - x))
    + Rabs (fy_val pr_y - fx_val pr_x - l2 * (y - x)))).
    rewrite <- Rabs_mult.
    rewrite <- (Rabs_Ropp (fy_val pr_y - fx_val pr_x - l1 * (y - x))).
    assert (((l1 - l2) * (y - x)) =
      (- (fy_val pr_y - fx_val pr_x - l1 * (y - x))) +
      (fy_val pr_y - fx_val pr_x - l2 * (y - x))).
      ring.
      rewrite H ; clear H.
      apply Rabs_triang.
  assert (eps * Rabs (y - x) = eps' * Rabs (y - x) + eps' * Rabs (y - x)).
    unfold eps'. simpl. field.
    rewrite H ; clear H.
    apply Rplus_le_compat.
    apply Df1.
    apply Df2.
Qed.

Definition Pfun_derivable_pt (f : R -> partial_val) (x : R) :=
  {l : R & Pfun_derivable_pt_lim f x l}.

Definition Pfun_derive_pt (f : R -> partial_val) (x : R) (pr : Pfun_derivable_pt f x) :=
  projT1 pr.

Definition Pfun_derivable (f : R -> partial_val) :=
  forall x, pdom (f x) -> Pfun_derivable_pt f x.

Lemma Pfun_derive_Heq : forall (f : R -> partial_val),
  forall x d1 d2, Pfun_derive_pt f x d1 = Pfun_derive_pt f x d2.
Proof.
  intros.
  destruct d1 as (l1,d1).
  destruct d2 as (l2,d2).
  simpl.
  apply (Pfun_derive_unique f x l1 l2).
  apply d1.
  apply d2.
Qed.
Definition Pfun_derive (f : R -> partial_val) x : partial_val :=
  Pval (Pfun_derivable_pt f x) (fun pr => Pfun_derive_pt f x pr) (Pfun_derive_Heq f x).

Lemma Pfun_derivable_derive : forall f x l pr,
  prod (Pfun_derivable_pt_lim f x l -> Pfun_derive_pt f x pr = l)
    (Pfun_derive_pt f x pr = l -> Pfun_derivable_pt_lim f x l).
Proof.
  intros f x l (l',Df).
  simpl.
  split.
  intros.
  apply (Pfun_derive_unique f x).
  apply Df.
  apply X.
  intros H.
  now rewrite <- H.
Qed.

Lemma Pfun_derivable_continuous_pt : forall f x,
  Pfun_derivable_pt f x -> Pfun_continuity_pt f x.
Proof.
  intros.
  cut { pr_x : pdom (f x) |
    forall eps : posreal, exists delta : posreal,
    forall y : R, Rabs (y - x) < delta ->
    exists pr_y : pdom (f y), Rabs (pval _ pr_y - pval _ pr_x) <= eps }.
  intros (pr_x,Cf).
  exists pr_x.
  intros eps.
  assert (He : 0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (eps2 := mkposreal _ He).
    elim (Cf eps2) ; clear Cf ; intros delta Cf.
    exists delta ; intros.
    elim (Cf _ H) ; clear Cf ; intros pr_y Cf.
    exists pr_y.
    apply (Rle_lt_trans _ _ _ Cf).
    rewrite <- (Rplus_0_r eps2) ; rewrite (double_var eps) ;
    apply Rplus_lt_compat_l.
    apply He.

  destruct X as (l,(pr_x,Df)).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  assert (Hdelta : 0 < Rmin delta (eps/(Rabs l + eps))).
    apply Rmin_pos.
    apply delta.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rplus_le_lt_0_compat.
    apply Rabs_pos.
    apply eps.
    set (delta' := mkposreal _ Hdelta).
  exists delta'.
  intros.
  assert (Rabs (y - x) < delta).
    apply (Rlt_le_trans _ delta').
    apply H.
    unfold delta' ; simpl ; apply Rmin_l.
  elim (Df y H0) ; clear Df H0 ; intros pr_y Df.
  exists pr_y.
  apply (Rle_trans _ ((Rabs l+eps) * Rabs (y-x))).
  rewrite Rmult_plus_distr_r.
  rewrite Rplus_comm.
  rewrite <- (Rplus_0_r (Rabs (pval _ pr_y - pval _ pr_x))) ;
  rewrite <- (Rplus_opp_l (Rabs l * Rabs (y - x))) ;
  rewrite <- Rplus_assoc ;
  apply Rplus_le_compat_r.
  rewrite <- Rabs_mult.
  apply (Rle_trans _ (Rabs (pval _ pr_y - pval _ pr_x - l * (y - x)))).
  apply Rabs_triang_inv.
  apply Df.
  apply (Rle_trans _ ((Rabs l + eps) * delta')).
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat.
  apply Rabs_pos.
  apply Rlt_le ;
  apply eps.
  apply Rlt_le ; apply H.
  apply (Rle_trans _ ((Rabs l + eps) * (eps / (Rabs l + eps)))).
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat.
  apply Rabs_pos.
  apply Rlt_le.
  apply eps.
  unfold delta' ; simpl ; apply Rmin_r.
  apply Req_le.
  field.
  apply Rgt_not_eq.
  apply Rlt_gt.
  apply Rplus_le_lt_0_compat.
  apply Rabs_pos.
  apply eps.
Qed.

(** Extention and equality *)

Lemma Pfun_derivable_pt_lim_extension : forall (f1 f2 : R -> partial_val) x l,
  Pfun_extension f1 f2 ->
  Pfun_derivable_pt_lim f2 x l -> Pfun_derivable_pt_lim f1 x l.
Proof.
  intros f1 f2 x l H_prol (pr_x,Df2).
  exists (fst (H_prol x) pr_x) ; intros.
  elim (Df2 eps) ; clear Df2 ; intros delta Df2.
  exists delta.
  intros.
  elim (Df2 y H) ; clear Df2 H ; intros pr_y Df2.
  exists (fst (H_prol y) pr_y).
  rewrite (snd (H_prol x) (fst (H_prol x) pr_x) pr_x).
  rewrite (snd (H_prol y) (fst (H_prol y) pr_y) pr_y).
  apply Df2.
Qed.
Lemma Pfun_derivable_pt_extension : forall (f1 f2 : R -> partial_val) x,
  Pfun_extension f1 f2 -> Pfun_derivable_pt f2 x -> Pfun_derivable_pt f1 x.
Proof.
  intros f1 f2 x Ext (l,Df2).
  exists l.
  apply (Pfun_derivable_pt_lim_extension f1 f2 x l Ext Df2).
Qed.
Lemma Pfun_derive_pt_extension : forall (f1 f2 : R -> partial_val) x pr1 pr2,
  Pfun_extension f1 f2 -> Pfun_derive_pt f1 x pr1 = Pfun_derive_pt f2 x pr2.
Proof.
  intros f1 f2 x (l1,Df1) (l2,Df2) Ext ; simpl.
  apply (Pfun_derive_unique f1 x).
  apply Df1.
  apply (Pfun_derivable_pt_lim_extension _ f2 _ _ Ext Df2).
Qed.
Lemma Pfun_derive_extension : forall (f1 f2 : R -> partial_val),
  Pfun_extension f1 f2 -> Pfun_extension (Pfun_derive f1) (Pfun_derive f2).
Proof.
  intros f1 f2 Ext.
  split.
  intros ; apply (Pfun_derivable_pt_extension f1 f2 x Ext X).
  intros ; apply (Pfun_derive_pt_extension f1 f2 x d1 d2 Ext).
Qed.

Lemma Pfun_derivable_pt_lim_equal : forall (f1 f2 : R -> partial_val) x l,
  Pfun_equal f1 f2 ->
    prod (Pfun_derivable_pt_lim f1 x l -> Pfun_derivable_pt_lim f2 x l)
      (Pfun_derivable_pt_lim f2 x l -> Pfun_derivable_pt_lim f1 x l).
Proof.
  split ; intros.
  apply (Pfun_derivable_pt_lim_extension f2 f1).
  apply Pfun_equal_extension.
  apply Pfun_equal_sym.
  apply X.
  apply X0.
  apply (Pfun_derivable_pt_lim_extension f1 f2).
  apply Pfun_equal_extension.
  apply X.
  apply X0.
Qed.
Lemma Pfun_derivable_pt_equal : forall (f1 f2 : R -> partial_val) x,
  Pfun_equal f1 f2 ->
    prod (Pfun_derivable_pt f1 x -> Pfun_derivable_pt f2 x)
      (Pfun_derivable_pt f2 x -> Pfun_derivable_pt f1 x).
Proof.
  intros f1 f2 x Heq ;
  split ; intros (l,Df) ;
  exists l ;
  apply (Pfun_derivable_pt_lim_equal _ _ _ _ Heq) ;
  apply Df.
Qed.
Lemma Pfun_derive_pt_equal : forall (f1 f2 : R -> partial_val) x pr1 pr2,
  Pfun_equal f1 f2 ->
    Pfun_derive_pt f2 x pr2 = Pfun_derive_pt f1 x pr1.
Proof.
  intros f1 f2 x (l1,Df1) (l2,Df2) Heq ; simpl.
  apply (Pfun_derive_unique f1 x).
  apply (Pfun_derivable_pt_lim_equal f1 f2 x l2 Heq), Df2.
  apply Df1.
Qed.

(** Partial and total function *)

Lemma Pfun_derivable_pt_lim_fun_0 : forall (f : R -> R) x l ,
  derivable_pt_lim f x l -> Pfun_derivable_pt_lim (Pfun_fun f) x l.
Proof.
  unfold Pfun_fun, Pval_val, Pfun_derivable_pt_lim.
  simpl.
  intros f x l Df.
  exists I ;
  intros.
  apply (equiv_deriv_pt_lim_0 f x l) in Df.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta.
  intros.
  exists I.
  apply Df.
  apply H.
Qed.
Lemma Pfun_derivable_pt_lim_fun_1 : forall (f : R -> R) x l ,
  Pfun_derivable_pt_lim (Pfun_fun f) x l -> derivable_pt_lim f x l.
Proof.
  unfold Pfun_fun, Pval_val, Pfun_derivable_pt_lim.
  simpl.
  intros f x l (_,Df).
  apply (equiv_deriv_pt_lim f x l).
  intros eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta.
  intros.
  elim (Df _ H) ; clear Df ; intros _ Df.
  apply Df.
Qed.
Lemma Pfun_derivable_pt_lim_fun : forall (f : R -> R) x l ,
  prod (derivable_pt_lim f x l -> Pfun_derivable_pt_lim (Pfun_fun f) x l)
    (Pfun_derivable_pt_lim (Pfun_fun f) x l -> derivable_pt_lim f x l).
Proof.
  split.
  apply Pfun_derivable_pt_lim_fun_0.
  apply Pfun_derivable_pt_lim_fun_1.
Qed.

Lemma Pfun_derivable_pt_fun : forall (f : R -> R) x ,
  prod (derivable_pt f x -> Pfun_derivable_pt (Pfun_fun f) x)
    (Pfun_derivable_pt (Pfun_fun f) x -> derivable_pt f x).
Proof.
  split.
  intros Df.
  destruct Df as (l,Df).
  exists l.
  apply (Pfun_derivable_pt_lim_fun f x l).
  apply Df.

  intros Df.
  destruct Df as (l,Df).
  exists l.
  apply (Pfun_derivable_pt_lim_fun f x l).
  apply Df.
Qed.

Lemma Pfun_derivable_fun : forall (f : R -> R) ,
  prod (derivable f -> Pfun_derivable (Pfun_fun f))
    (Pfun_derivable (Pfun_fun f) -> derivable f).
Proof.
  split.
  intros Df x _.
  apply (Pfun_derivable_pt_fun f x).
  apply Df.

  intros Df x.
  apply (Pfun_derivable_pt_fun f x).
  apply Df, I.
Qed.

Lemma Pfun_derive_pt_fun : forall (f : R -> R) x pr1 pr2,
  Pfun_derive_pt (Pfun_fun f) x pr1 = derive_pt f x pr2.
Proof.
  intros.
  destruct pr1 as (d1,Df1).
  destruct pr2 as (d2, Df2).
  simpl.
  apply (Pfun_derive_unique (Pfun_fun f) x).
  apply Df1.
  apply (Pfun_derivable_pt_lim_fun f x d2).
  apply Df2.
Qed.

Lemma Pfun_derive_fun : forall (f : R -> R),
  Pfun_equal (Pfun_derive (Pfun_fun f))
    (fun x => Pval (derivable_pt f x) (fun d => derive_pt f x d) (fun d1 d2 => pr_nu f x d1 d2)).
Proof.
  intros f.
  split ; [split |] ; simpl in *|-* ; intros.
  apply (Pfun_derivable_pt_fun _ _) ; apply H.
  apply (Pfun_derivable_pt_fun _ _) ; apply X.
  apply Pfun_derive_pt_fun.
Qed.

Lemma Pfun_derivable_pt_lim_eval_a_b_0 : forall (f : R -> partial_val) (a b x l : R),
  forall pr, Rmin a b < x < Rmax a b ->
    Pfun_derivable_pt_lim f x l -> derivable_pt_lim (Pfun_eval_a_b f a b pr) x l.
Proof.
  intros f a0 b0 x l ;
  set (a := Rmin a0 b0) ;
  set (b := Rmax a0 b0) ;
  intros pr Hx (pr_x,Df) ;
  apply (equiv_deriv_pt_lim _ x l) ;
  intro eps.
  elim (Df eps) ; clear Df ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (Rmin (x-a) (b-x))).
    apply Rmin_pos ;
    [apply d0 | apply Rmin_pos ; apply Rlt_Rminus, Hx].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (y - x) < d0).
    apply (Rlt_le_trans _ _ _ H) ;
    simpl ;
    apply Rmin_l.
  elim (Df y H0) ; clear Df ; intros pr_y Df.
  assert (Pfun_eval_a_b f a0 b0 pr x = pval (f x) pr_x).
    unfold Pfun_eval_a_b ; fold a b.
    destruct (Rle_dec a x) ; [|elim n ; apply Rlt_le, Hx].
    destruct (Rle_dec x b) ; [|elim n ; apply Rlt_le, Hx].
    apply pHeq.
    rewrite H1 ; clear H1.
  assert (Pfun_eval_a_b f a0 b0 pr y = pval (f y) pr_y).
    assert (a < y < b).
      split.
      apply Ropp_lt_cancel ;
      apply (Rplus_lt_reg_r x) ;
      apply (Rle_lt_trans _ (Rabs (y-x))).
      assert (x + - y = -(y-x)).
        ring.
      rewrite H1 ; clear H1.
      apply Rabs_maj2.
      apply (Rlt_le_trans _ _ _ H) ; simpl ;
      apply (Rle_trans _ (Rmin (x-a) (b-x))).
      apply Rmin_r.
      apply Rmin_l.
      apply (Rplus_lt_reg_r (-x)) ;
      repeat rewrite (Rplus_comm (-x)) ;
      apply (Rle_lt_trans _ (Rabs (y-x))).
      apply Rabs_maj1.
      apply (Rlt_le_trans _ _ _ H) ; simpl ;
      apply (Rle_trans _ (Rmin (x-a) (b-x))).
      apply Rmin_r.
      apply Rmin_r.
    unfold Pfun_eval_a_b ; fold a b.
    destruct (Rle_dec a y) ; [|elim n ; apply Rlt_le, H1].
    destruct (Rle_dec y b) ; [|elim n ; apply Rlt_le, H1].
    apply pHeq.
    rewrite H1 ; clear H1.
  apply Df.
Qed.
Lemma Pfun_derivable_pt_lim_eval_a_b_1 : forall (f : R -> partial_val) (a b x l : R),
  forall pr, Rmin a b < x < Rmax a b ->
    derivable_pt_lim (Pfun_eval_a_b f a b pr) x l -> Pfun_derivable_pt_lim f x l.
Proof.
  intros f a0 b0 x l ;
  set (a := Rmin a0 b0) ;
  set (b := Rmax a0 b0) ;
  intros pr Hx Df ;
  apply (equiv_deriv_pt_lim _ x l) in Df.
  assert (pr_x : pdom (f x)).
    apply pr ;
    split ;
    apply Rlt_le, Hx.
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (Rmin (x-a) (b-x))).
    apply Rmin_pos ;
    [apply d0 | apply Rmin_pos ; apply Rlt_Rminus, Hx].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (a < y < b).
    split.
    apply Ropp_lt_cancel ;
    apply (Rplus_lt_reg_r x) ;
    apply (Rle_lt_trans _ (Rabs (y-x))).
    assert (x + - y = -(y-x)).
      ring.
    rewrite H0 ; clear H0.
    apply Rabs_maj2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ (Rmin (x-a) (b-x))).
    apply Rmin_r.
    apply Rmin_l.
    apply (Rplus_lt_reg_r (-x)) ;
    repeat rewrite (Rplus_comm (-x)) ;
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj1.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ (Rmin (x-a) (b-x))).
    apply Rmin_r.
    apply Rmin_r.
  assert (pr_y : pdom (f y)).
    apply pr ;
    split ;
    apply Rlt_le, H0.
  exists pr_y.
  assert (pval (f x) pr_x = Pfun_eval_a_b f a0 b0 pr x).
    unfold Pfun_eval_a_b ; fold a b.
    destruct (Rle_dec a x) ; [|elim n ; apply Rlt_le, Hx].
    destruct (Rle_dec x b) ; [|elim n ; apply Rlt_le, Hx].
    apply pHeq.
    rewrite H1 ; clear H1.
  assert (pval (f y) pr_y = Pfun_eval_a_b f a0 b0 pr y).
    unfold Pfun_eval_a_b ; fold a b.
    destruct (Rle_dec a y) ; [|elim n ; apply Rlt_le, H0].
    destruct (Rle_dec y b) ; [|elim n ; apply Rlt_le, H0].
    apply pHeq.
    rewrite H1 ; clear H1.
  apply Df.
  apply (Rlt_le_trans _ _ _ H) ;
    simpl ;
    apply Rmin_l.
Qed.
Lemma Pfun_derivable_pt_lim_eval_a_b : forall (f : R -> partial_val) (a b x l : R),
  forall pr, Rmin a b < x < Rmax a b ->
  prod (Pfun_derivable_pt_lim f x l -> derivable_pt_lim (Pfun_eval_a_b f a b pr) x l)
    (derivable_pt_lim (Pfun_eval_a_b f a b pr) x l -> Pfun_derivable_pt_lim f x l).
Proof.
  split.
  apply Pfun_derivable_pt_lim_eval_a_b_0, H.
  apply Pfun_derivable_pt_lim_eval_a_b_1, H.
Qed.

Lemma Pfun_derivable_pt_eval_a_b : forall (f : R -> partial_val) (a b x : R),
  forall pr, Rmin a b < x < Rmax a b ->
  prod (Pfun_derivable_pt f x -> derivable_pt (Pfun_eval_a_b f a b pr) x)
    (derivable_pt (Pfun_eval_a_b f a b pr) x -> Pfun_derivable_pt f x).
Proof.
  simpl ; split ; intros (l,Df) ;
  exists l ;
  apply (Pfun_derivable_pt_lim_eval_a_b f a b x l pr H), Df.
Qed.

Lemma Pfun_derive_pt_eval_a_b : forall (f : R -> partial_val) (a b x : R),
  forall pr pr1 pr2, Rmin a b < x < Rmax a b ->
  Pfun_derive_pt f x pr1 = derive_pt (Pfun_eval_a_b f a b pr) x pr2.
Proof.
  intros f a b x pr (l1,Df1) (l2, Df2) Hx ; simpl.
  apply (Pfun_derive_unique f x).
  apply Df1.
  apply (Pfun_derivable_pt_lim_eval_a_b_1 f a b x l2 pr Hx Df2).
Qed.

(** A second function eval *)

Lemma Pfun_derivable_definie_a_b : forall (f : R -> partial_val) (a b : R),
  (forall x : R, Rmin a b <= x <= Rmax a b ->  Pfun_derivable_pt f x) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> pdom (f x)).
Proof.
  intros f a b Df x Hx.
  elim (Df x Hx) ; clear Df ; intros _ (pr_x,_).
  apply pr_x.
Qed.

Definition Pfun_C1_eval_a_b (f : R -> partial_val) (a b : R)
  (def : forall y : R, Rmin a b <= y <= Rmax a b -> pdom (f y))
  (Df_a : Pfun_derivable_pt f (Rmin a b))
  (Df_b : Pfun_derivable_pt f (Rmax a b)) x :=
  match (Rle_dec (Rmin a b) x) with
    | left Ha =>
    match (Rle_dec x (Rmax a b)) with
      | left Hb => pval _ (def _ (Rle_le _ _ _ Ha Hb))
      | _ => pval _ (def _ (Rle_le _ _ _ (Rmin_Rmax a b) (Rle_refl (Rmax a b))))
        + Pfun_derive_pt f (Rmax a b) Df_b * (x - (Rmax a b))
    end
    | _ => pval _ (def _ (Rle_le _ _ _ (Rle_refl (Rmin a b)) (Rmin_Rmax a b)))
      + Pfun_derive_pt f (Rmin a b) Df_a * (x - (Rmin a b))
  end.

Lemma Pfun_derivable_pt_lim_C1_eval_a_b_0 :
 forall (f : R -> partial_val) (a b x l : R),
  forall def Df_a Df_b, Rmin a b <= x <= Rmax a b -> Pfun_derivable_pt_lim f x l
    -> derivable_pt_lim (Pfun_C1_eval_a_b f a b def Df_a Df_b) x l.
Proof.
  intros f a0 b0 x l ;
  set (a := Rmin a0 b0) ;
  set (b := Rmax a0 b0) ;
  intros def Df_a Df_b Hx Df ; simpl.
  assert (dec : {a < x < b} + {x=a} + {x=b}).
    destruct (total_order_T x a) ; [ destruct s | ].
    apply Rlt_not_le in r ; elim r ; apply Hx.
    left ; right ; apply e.
    destruct (total_order_T x b) ; [ destruct s | ].
    left ; left ; split ; [apply r|apply r0].
    right ; apply e.
    apply Rlt_not_le in r0 ; elim r0 ; apply Hx.
  apply (equiv_deriv_pt_lim _ _ _).
  destruct dec ; [ destruct s | ].
  intros eps.
  destruct Df as (pr_x,Df).
  elim (Df eps) ; clear Df ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (Rmin (x-a) (b-x))).
    apply Rmin_pos ; [apply d0 | apply Rmin_pos ; apply Rlt_Rminus, a1].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (y-x) < d0).
    apply (Rlt_le_trans _ _ _ H) ;
    simpl ; apply Rmin_l.
  elim (Df _ H0) ; clear Df H0 ; intros pr_y Df.
  assert (a < y < b).
    split.
    apply Ropp_lt_cancel ;
    apply (Rplus_lt_reg_r x) ;
    apply (Rle_lt_trans _ (Rabs (y-x))).
    assert (x + - y = -(y-x)).
      ring.
    rewrite H0 ; clear H0.
    apply Rabs_maj2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ (Rmin (x-a) (b-x))).
    apply Rmin_r.
    apply Rmin_l.
    apply (Rplus_lt_reg_r (-x)) ;
    repeat rewrite (Rplus_comm (-x)) ;
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj1.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ (Rmin (x-a) (b-x))).
    apply Rmin_r.
    apply Rmin_r.
  assert (Pfun_C1_eval_a_b f a0 b0 def Df_a Df_b x = pval (f x) pr_x).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a x) ; [ | elim n ; apply Hx].
    destruct (Rle_dec x b) ; [ | elim n ; apply Hx].
    apply pHeq.
    rewrite H1.
  assert (Pfun_C1_eval_a_b f a0 b0 def Df_a Df_b y = pval (f y) pr_y).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a y) ; [ | elim n ; apply Rlt_le, H0].
    destruct (Rle_dec y b) ; [ | elim n ; apply Rlt_le, H0].
    apply pHeq.
    rewrite H2.
  apply Df.
    
  destruct Df_a as (l_a,Df_a).
  rewrite e in *|-* ; clear e.
  assert (l = l_a).
    apply (Pfun_derive_unique f a).
    apply Df.
    apply Df_a.
  rewrite H in *|-* ; clear H.
  assert (dec : {a < b} + {a = b}).
    destruct (total_order_T a b) ; [destruct s | ].
    left ; apply r.
    right ; apply e.
    apply Rlt_not_le in r ; elim r ; simpl ; apply Rmin_Rmax.
  destruct dec.
  intros eps.
  destruct Df as (pr_x,Df).
  elim (Df eps) ; clear Df ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (b-a)).
    apply Rmin_pos ; [apply d0 | apply Rlt_Rminus, r].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (y - a) < d0).
    apply (Rlt_le_trans _ _ _ H) ; simpl ; apply Rmin_l.
  elim (Df _ H0) ; clear Df ; intros pr_y Df.
  assert (Pfun_C1_eval_a_b f a0 b0 def (existT (fun l0 : R => Pfun_derivable_pt_lim f a l0) l_a Df_a) Df_b a = pval (f a) pr_x).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a a) ; [|elim n ; apply Hx].
    destruct (Rle_dec a b) ; [|elim n ; apply Hx].
    apply pHeq.
  rewrite H1 ; clear H1.
  destruct (Rle_lt_dec a y).
  assert (Pfun_C1_eval_a_b f a0 b0 def (existT (fun l0 : R => Pfun_derivable_pt_lim f a l0) l_a Df_a) Df_b y = pval (f y) pr_y).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a y).
    destruct (Rle_dec y b).
    apply pHeq.
    elim n ; apply Rlt_le ;
    apply (Rplus_lt_reg_r (-a)) ;
    repeat rewrite (Rplus_comm (-a)) ;
    apply (Rle_lt_trans _ (Rabs (y-a))).
    apply Rabs_maj1.
    apply (Rlt_le_trans _ _ _ H).
    simpl ; apply Rmin_r.
    elim n ; apply r0.
  rewrite H1 ; clear H1 ; apply Df.
  assert (Pfun_C1_eval_a_b f a0 b0 def (existT (fun l0 : R => Pfun_derivable_pt_lim f a l0) l_a Df_a) Df_b y = 
    pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
       l_a * (y - a)).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a y).
    apply Rlt_not_le in r0 ; elim r0 ; apply r1.
    reflexivity.
  rewrite H1 ; clear H1.
  assert (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
    l_a * (y - a) - pval (f a) pr_x - l_a * (y - a) = 0).
    rewrite (pHeq (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) pr_x).
    ring.
  rewrite H1, Rabs_R0.
  apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
  intros eps ; exists eps ; intros.
  unfold Pfun_C1_eval_a_b ; fold a b ; simpl.
  destruct (Rle_dec a a) ; [|elim n ; apply Hx].
  destruct (Rle_dec a b) ; [|elim n ; apply Hx].
  destruct (Rle_dec a y).
  destruct (Rle_dec y b).
  assert (y = a).
    apply Rle_antisym.
    rewrite e ; apply r2.
    apply r1.
  assert (pval (f y) (def y (Rle_le a y b r1 r2)) -
    pval (f a) (def a (Rle_le a a b r r0)) - l_a * (y - a) = 0).
    assert (pval (f y) (def y (Rle_le a y b r1 r2)) = pval (f a) (def a (Rle_le a a b r r0))).
    set (pr_y := (def y (Rle_le a y b r1 r2))).
    generalize pr_y ; rewrite H0 ; intros ; apply pHeq.
    rewrite H1, H0 ; clear H1 ; ring.
  rewrite H1, Rabs_R0 ; apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
  set (pr_b := (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b)))).
  set (pr_a := (def a (Rle_le a a b r r0))).
  generalize Df_b pr_b pr_a ; clear Df_b pr_b pr_a ; rewrite <- e.
  intros.
  assert (pval (f a) pr_b + Pfun_derive_pt f a Df_b * (y - a) - pval (f a) pr_a -
   l_a * (y - a) = 0).
   rewrite (pHeq (f a) pr_b pr_a).
   rewrite (fst (Pfun_derivable_derive f a l_a Df_b) Df_a).
   ring.
   rewrite H0, Rabs_R0 ; clear H0.
   apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
   assert (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
   l_a * (y - a) - pval (f a) (def a (Rle_le a a b r r0)) - l_a * (y - a) = 0).
   rewrite (pHeq (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) (def a (Rle_le a a b r r0))).
   ring.
   rewrite H0, Rabs_R0 ; clear H0.
   apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].

  destruct Df_b as (l_b,Df_b).
  rewrite e in *|-* ; clear e.
  assert (l = l_b).
    apply (Pfun_derive_unique f b).
    apply Df.
    apply Df_b.
  rewrite H in *|-* ; clear H.
  assert (dec : {a < b} + {a = b}).
    destruct (total_order_T a b) ; [destruct s | ].
    left ; apply r.
    right ; apply e.
    apply Rlt_not_le in r ; elim r ; simpl ; apply Rmin_Rmax.
  destruct dec.
  intros eps.
  destruct Df as (pr_x,Df).
  elim (Df eps) ; clear Df ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (b-a)).
    apply Rmin_pos ; [apply d0 | apply Rlt_Rminus, r].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (y - b) < d0).
    apply (Rlt_le_trans _ _ _ H) ; simpl ; apply Rmin_l.
  elim (Df _ H0) ; clear Df ; intros pr_y Df.
  assert (Pfun_C1_eval_a_b f a0 b0 def Df_a
     (existT (fun l0 : R => Pfun_derivable_pt_lim f b l0) l_b Df_b) b = pval (f b) pr_x).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a b) ; [|elim n ; apply Hx].
    destruct (Rle_dec b b) ; [|elim n ; apply Hx].
    apply pHeq.
  rewrite H1 ; clear H1.
  destruct (Rle_lt_dec a y).
  destruct (Rle_lt_dec y b).
  assert (Pfun_C1_eval_a_b f a0 b0 def Df_a
     (existT (fun l0 : R => Pfun_derivable_pt_lim f b l0) l_b Df_b) y = pval (f y) pr_y).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a y).
    destruct (Rle_dec y b).
    apply pHeq.
    elim n ; apply r1.
    elim n ; apply r0.
  rewrite H1 ; clear H1 ; apply Df.
  assert (Pfun_C1_eval_a_b f a0 b0 def Df_a
     (existT (fun l0 : R => Pfun_derivable_pt_lim f b l0) l_b Df_b) y = 
    pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
           l_b * (y - b)).
    unfold Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a y).
    destruct (Rle_dec y b).
    apply Rlt_not_le in r1 ; elim r1 ; apply r3.
    simpl ; reflexivity.
    elim n ; apply r0.
    rewrite H1 ; clear H1.
  assert (pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
   l_b * (y - b) - pval (f b) pr_x - l_b * (y - b) = 0).
   rewrite (pHeq (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) pr_x).
   ring.
   rewrite H1, Rabs_R0 ;
  apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
  apply Rlt_not_le in r0 ; elim r0 ; apply Rlt_le.
  apply Ropp_lt_cancel, (Rplus_lt_reg_r b).
  assert (b + - y = -(y-b)).
    ring.
  rewrite H1 ; clear H1.
  apply (Rle_lt_trans _ _ _ (Rabs_maj2 _)).
  apply (Rlt_le_trans _ _ _ H).
  simpl ; apply Rmin_r.
  intros eps ; exists eps ; intros.
  unfold Pfun_C1_eval_a_b ; fold a b ; simpl.
  destruct (Rle_dec a b) ; [|elim n ; apply Hx].
  destruct (Rle_dec b b) ; [|elim n ; apply Hx].
  destruct (Rle_dec a y).
  destruct (Rle_dec y b).
  assert (y = b).
    apply Rle_antisym.
    apply r2.
    rewrite <- e ; apply r1.
  assert (pval (f y) (def y (Rle_le a y b r1 r2)) -
    pval (f b) (def b (Rle_le a b b r r0)) - l_b * (y - b) = 0).
    assert (pval (f y) (def y (Rle_le a y b r1 r2)) = pval (f b) (def b (Rle_le a b b r r0))).
    set (pr_y := (def y (Rle_le a y b r1 r2))).
    generalize pr_y ; rewrite H0 ; intros ; apply pHeq.
    rewrite H1, H0 ; clear H1 ; ring.
  rewrite H1, Rabs_R0 ; apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
  assert (pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
   l_b * (y - b) - pval (f b) (def b (Rle_le a b b r r0)) - l_b * (y - b) = 0).
   rewrite (pHeq (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) (def b (Rle_le a b b r r0))).
   ring.
   rewrite H0, Rabs_R0 ; clear H0.
   apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
  assert (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
   Pfun_derive_pt f a Df_a * (y - a) - pval (f b) (def b (Rle_le a b b r r0)) -
   l_b * (y - b) = 0).
   set (pr_a := (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0)))).
   set (pr_b := (def b (Rle_le a b b r r0))).
   generalize pr_a pr_b ; clear pr_a pr_b ; revert Df_a.
   rewrite e ; intros.
   rewrite (pHeq (f b) pr_a pr_b).
   rewrite (fst (Pfun_derivable_derive f b l_b Df_a) Df_b).
   ring.
   rewrite H0, Rabs_R0 ; clear H0.
   apply Rmult_le_pos ; [apply Rlt_le, eps | apply Rabs_pos].
Qed.
Lemma Pfun_derivable_pt_lim_C1_eval_a_b_1 :
 forall (f : R -> partial_val) (a b x l : R),
  forall def Df_a Df_b, Rmin a b <= x <= Rmax a b 
    -> derivable_pt_lim (Pfun_C1_eval_a_b f a b def Df_a Df_b) x l 
    -> Pfun_derivable_pt_lim f x l.
Proof.
  intros f a0 b0 x l ;
  set (a := Rmin a0 b0) ;
  set (b := Rmax a0 b0) ;
  intros.
  assert (dec : {a < x < b} + {x = a} + {x = b}).
    destruct (total_order_T a x) ; [destruct s|].
    destruct (total_order_T x b) ; [destruct s|].
    left ; left ; split ; [apply r|apply r0].
    right ; apply e.
    apply Rlt_not_le in r0 ; elim r0 ; apply H.
    left ; right ; apply sym_equal, e.
    apply Rlt_not_le in r ; elim r ; apply H.
  destruct dec ; [destruct s|].
  apply equiv_deriv_pt_lim in H0.
  assert (pr_x : pdom (f x)).
    apply def.
    split ; apply H.
  exists pr_x ; simpl ; intros.
  elim (H0 eps) ; clear H0 ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (Rmin (x-a) (b-x))).
    apply Rmin_pos.
    apply d0.
    apply Rmin_pos ;
    apply Rlt_Rminus ;
    apply a1.
  set (delta := mkposreal _ Hd) ; 
  exists delta ; intros.
  assert (a < y < b).
    split.
    apply Ropp_lt_cancel ; apply (Rplus_lt_reg_r x).
    apply (Rle_lt_trans _ (Rabs (y-x))).
    rewrite <- Ropp_minus_distr', Rabs_Ropp.
    apply Rabs_maj1.
    apply (Rlt_le_trans _ (Rmin (x-a) (b-x))).
    apply (Rlt_le_trans _ delta).
    apply H0.
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_l.
    apply (Rplus_lt_reg_r (-x)) ; repeat rewrite (Rplus_comm (-x)).
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj1.
    apply (Rlt_le_trans _ (Rmin (x-a) (b-x))).
    apply (Rlt_le_trans _ delta).
    apply H0.
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_r.
  unfold Pfun_C1_eval_a_b in Df ; fold a b in Df.
  assert (Rabs (y - x) < d0).
    apply (Rlt_le_trans _ _ _ H0).
    simpl ; apply Rmin_l.
  assert (pr_y : pdom (f y)).
    apply def.
    split ; apply Rlt_le, H1.
  exists pr_y.
  set (Df_aux := Df _ H2).
  destruct (Rle_dec a x) ; 
    [destruct (Rle_dec x b) ; 
    [|elim n ; apply H]
    |elim n ; apply H].
  generalize Df_aux ; clear Df_aux.
  destruct (Rle_dec a y) ; 
    [destruct (Rle_dec y b) ; 
    [|elim n ; apply Rlt_le, H1]
    |elim n ; apply Rlt_le, H1] ;
    clear Df ; intros Df.
  rewrite (pHeq _ _ pr_y), (pHeq _ _ pr_x) in Df.
  apply Df.
  
  rewrite e in *|-* ;
  apply (Pfun_derivable_derive _ _ _ Df_a) ;
  apply (uniqueness_limite (Pfun_C1_eval_a_b f a0 b0 def Df_a Df_b) a) ; 
  [| apply H0].
  apply Pfun_derivable_pt_lim_C1_eval_a_b_0 ; fold a b.
  apply H.
  apply (Pfun_derivable_derive _ _ _ Df_a) ; reflexivity.
  
  rewrite e in *|-* ;
  apply (Pfun_derivable_derive _ _ _ Df_b) ;
  apply (uniqueness_limite (Pfun_C1_eval_a_b f a0 b0 def Df_a Df_b) b) ; 
  [| apply H0].
  apply Pfun_derivable_pt_lim_C1_eval_a_b_0 ; fold a b.
  apply H.
  apply (Pfun_derivable_derive _ _ _ Df_b) ; reflexivity.
Qed.
Lemma Pfun_derivable_pt_lim_C1_eval_a_b :
  forall (f : R -> partial_val) (a b x l : R),
  forall def df_a df_b, Rmin a b <= x <= Rmax a b ->
  prod (Pfun_derivable_pt_lim f x l
    -> derivable_pt_lim (Pfun_C1_eval_a_b f a b def df_a df_b) x l)
    (derivable_pt_lim (Pfun_C1_eval_a_b f a b def df_a df_b) x l
     -> Pfun_derivable_pt_lim f x l).
Proof.
  split.
  apply Pfun_derivable_pt_lim_C1_eval_a_b_0 ;
  apply H.
  apply Pfun_derivable_pt_lim_C1_eval_a_b_1 ;
  apply H.
Qed.

Lemma Pfun_derivable_pt_C1_eval_a_b :
  forall (f : R -> partial_val) (a b x : R),
  forall def df_a df_b, Rmin a b <= x <= Rmax a b ->
  prod (Pfun_derivable_pt f x
    -> derivable_pt (Pfun_C1_eval_a_b f a b def df_a df_b) x)
    (derivable_pt (Pfun_C1_eval_a_b f a b def df_a df_b) x
     -> Pfun_derivable_pt f x).
Proof.
  split ; intros Df ; destruct Df as (l,Df) ; exists l ;
  apply (Pfun_derivable_pt_lim_C1_eval_a_b f a b _ _
  def df_a df_b) ; try apply H.
  apply Df.
  apply Df.
Qed.

Lemma Pfun_derive_pt_C1_eval_a_b :
  forall (f : R -> partial_val) (a b x : R),
  forall def df_a df_b pr1 pr2, Rmin a b <= x <= Rmax a b ->
  Pfun_derive_pt f x pr1 =
    derive_pt (Pfun_C1_eval_a_b f a b def df_a df_b) x pr2.
Proof.
  simpl ; intros.
  apply (Pfun_derive_unique f x).
    destruct pr1 as (l,Df1) ; simpl.
    apply Df1.
  apply (Pfun_derivable_pt_lim_C1_eval_a_b f a b
    _ _ def df_a df_b).
    apply H.
    destruct pr2 as (l,Df2) ; simpl.
    apply Df2.
Qed.

Lemma Pfun_derivable_C1_eval_a_b :
  forall (f : R -> partial_val) (a b : R),
  forall def df_a df_b,
  (forall y, Rmin a b <= y <= Rmax a b -> Pfun_derivable_pt f y)
    -> derivable (Pfun_C1_eval_a_b f a b def df_a df_b).
Proof.
  intros f a0 b0 ; set (a := Rmin a0 b0) ; set (b := Rmax a0 b0) ; intros.
  intro.
  destruct (Rle_lt_dec a x).
  destruct (Rle_lt_dec x b).

  apply (Pfun_derivable_pt_C1_eval_a_b f a0 b0 x def df_a df_b).
  apply (Rle_le _ _ _ r r0).
  apply X.
  apply (Rle_le _ _ _ r r0).

  exists (Pfun_derive_pt _ _ df_b).
  apply (equiv_deriv_pt_lim _ _ _).
  intro.
  assert (Hd : 0 < x-b).
  apply Rlt_Rminus ; apply r0.
  set (delta := mkposreal _ Hd).
  exists delta ; intros.
  unfold Pfun_C1_eval_a_b ; fold a b.
  destruct (Rle_dec a x) ; [| elim n ; apply r].
  destruct (Rle_dec x b) ; [apply Rlt_not_le in r0 ; elim r0 ; apply r2|].
  assert (b < y).
    apply (Rplus_lt_reg_r (-x)) ; repeat rewrite (Rplus_comm (-x)).
    apply Ropp_lt_cancel.
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj2.
    apply (Rlt_le_trans _ _ _ H).
    apply Req_le ; unfold delta ; simpl ; ring.
  assert (a <= y).
    apply (Rle_trans _ _ _ (Rmin_Rmax _ _) (Rlt_le _ _ H0)).
  destruct (Rle_dec a y) ; [| elim n0 ; apply H1].
  destruct (Rle_dec y b) ; [apply Rlt_not_le in H0 ; elim H0 ; apply r3|].
  assert (pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
   Pfun_derive_pt f b df_b * (y - b) -
   (pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
    Pfun_derive_pt f b df_b * (x - b)) - Pfun_derive_pt f b df_b * (y - x) = 0)  .
   ring.
   rewrite H2, Rabs_R0 ; clear H2.
   apply Rmult_le_pos.
   apply Rlt_le ; apply eps.
   apply Rabs_pos.

  exists (Pfun_derive_pt _ _ df_a).
  apply (equiv_deriv_pt_lim _ _ _).
  intro.
  assert (Hd : 0 < a-x).
  apply Rlt_Rminus ; apply r.
  set (delta := mkposreal _ Hd).
  exists delta ; intros.
  unfold Pfun_C1_eval_a_b ; fold a b.
  destruct (Rle_dec a x) ; [apply Rlt_not_le in r ; elim r ; apply r0|].
  assert (y < a).
    apply (Rplus_lt_reg_r (-x)) ; repeat rewrite (Rplus_comm (-x)).
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj1.
    apply H.
  destruct (Rle_dec a y) ; [apply Rlt_not_le in H0 ; elim H0 ; apply r0|].
  assert (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
   Pfun_derive_pt f a df_a * (y - a) -
   (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
    Pfun_derive_pt f a df_a * (x - a)) - Pfun_derive_pt f a df_a * (y - x) = 0).
   ring.
   rewrite H1, Rabs_R0 ; clear H1.
   apply Rmult_le_pos.
   apply Rlt_le ; apply eps.
   apply Rabs_pos.
Qed.

Lemma Pfun_derive_C1_eval_a_b :
  forall (f : R -> partial_val) (a b : R),
  forall def df_a df_b,
  forall (def' : forall y, Rmin a b <= y <= Rmax a b -> Pfun_derivable_pt f y) pr,
    forall x, derive (Pfun_C1_eval_a_b f a b def df_a df_b) pr x = Pfun_eval_a_b (Pfun_derive f) a b def' x.
Proof.
  intros f a0 b0 ; set (a := Rmin a0 b0) ; set (b := Rmax a0 b0) ; intros.
  apply (derive_pt_eq (Pfun_C1_eval_a_b f a0 b0 def df_a df_b) _ _ (pr _)).
  unfold Pfun_eval_a_b ; fold a b.
  destruct (Rle_dec a x) ; 
  [destruct (Rle_dec x b)|].
  apply Pfun_derivable_pt_lim_C1_eval_a_b_0.
  fold a b ; split ; [apply r|apply r0].
  apply (Pfun_derivable_derive _ _ _ (def' x (Rle_le a x b r r0))) ;
  simpl ; reflexivity.
  
  apply (equiv_deriv_pt_lim _ _ _).
  intro.
  assert (Hd : 0 < x-b).
  apply Rnot_le_lt in n ; apply Rlt_Rminus, n.
  set (delta := mkposreal _ Hd).
  exists delta ; intros.
  unfold Pfun_C1_eval_a_b ; fold a b.
  destruct (Rle_dec a x) ; [| elim n0 ; apply r].
  destruct (Rle_dec x b) ; [elim n ; apply r1|].
  assert (b < y).
    apply (Rplus_lt_reg_r (-x)) ; repeat rewrite (Rplus_comm (-x)).
    apply Ropp_lt_cancel.
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj2.
    apply (Rlt_le_trans _ _ _ H).
    apply Req_le ; unfold delta ; simpl ; ring.
  assert (a <= y).
    apply (Rle_trans _ _ _ (Rmin_Rmax _ _) (Rlt_le _ _ H0)).
  destruct (Rle_dec a y) ; [| elim n1 ; apply H1].
  destruct (Rle_dec y b) ; [apply Rlt_not_le in H0 ; elim H0 ; apply r2|].
  assert (pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
   Pfun_derive_pt f b df_b * (y - b) -
   (pval (f b) (def b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) +
    Pfun_derive_pt f b df_b * (x - b)) -
   pval (Pfun_derive f b)
     (def' b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) * (y - x) = 0)  .
   simpl ; rewrite (Pfun_derive_Heq _ _ (def' b (Rle_le a b b (Rmin_Rmax a0 b0) (Rle_refl b))) df_b); ring.
   rewrite H2, Rabs_R0 ; clear H2.
   apply Rmult_le_pos.
   apply Rlt_le ; apply eps.
   apply Rabs_pos.

  apply (equiv_deriv_pt_lim _ _ _).
  intro.
  assert (Hd : 0 < a-x).
  apply Rnot_le_lt in n ; apply Rlt_Rminus, n.
  set (delta := mkposreal _ Hd).
  exists delta ; intros.
  unfold Pfun_C1_eval_a_b ; fold a b.
  destruct (Rle_dec a x) ; [elim n ; apply r|].
  assert (y < a).
    apply (Rplus_lt_reg_r (-x)) ; repeat rewrite (Rplus_comm (-x)).
    apply (Rle_lt_trans _ (Rabs (y-x))).
    apply Rabs_maj1.
    apply H.
  destruct (Rle_dec a y) ; [apply Rlt_not_le in H0 ; elim H0 ; apply r|].
  assert (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
   Pfun_derive_pt f a df_a * (y - a) -
   (pval (f a) (def a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) +
    Pfun_derive_pt f a df_a * (x - a)) -
   pval (Pfun_derive f a)
     (def' a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) * (y - x) = 0).
   simpl ; rewrite (Pfun_derive_Heq _ _ (def' a (Rle_le a a b (Rle_refl a) (Rmin_Rmax a0 b0))) df_a); ring.
   rewrite H1, Rabs_R0 ; clear H1.
   apply Rmult_le_pos.
   apply Rlt_le ; apply eps.
   apply Rabs_pos.
Qed.

(** Basic functions and operations *)

Lemma Pfun_derivable_pt_lim_const : forall (a x : R),
  Pfun_derivable_pt_lim (fun _ => Pval_val a) x 0.
Proof.
  intros.
  apply (Pfun_derivable_pt_lim_fun (fun x => a) x 0).
  apply derivable_pt_lim_const.
Qed.

Lemma Pfun_derivable_pt_lim_id : forall x : R,
  Pfun_derivable_pt_lim (Pfun_fun (fun x => x)) x 1.
Proof.
  intros.
  apply (Pfun_derivable_pt_lim_fun id x 1).
  apply derivable_pt_lim_id.
Qed.

Lemma Pfun_derivable_pt_lim_plus : forall (f1 f2 : R -> partial_val) (x l1 l2 : R),
  Pfun_derivable_pt_lim f1 x l1 -> Pfun_derivable_pt_lim f2 x l2
    -> Pfun_derivable_pt_lim (fun x => Pval_plus (f1 x) (f2 x)) x (l1+l2).
Proof.
  simpl ; intros.
  elim X ; clear X ; intros pr1_x Df1.
  elim X0 ; clear X0 ; intros pr2_x Df2.
  exists (pr1_x, pr2_x) ; intros.
  assert (Heps2 : 0 < eps/2).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rlt_R0_R2.
  elim (Df1 (mkposreal _ Heps2)) ; clear Df1 ; intros delta1 Df1.
  elim (Df2 (mkposreal _ Heps2)) ; clear Df2 ; intros delta2 Df2.
  assert (Hdelta : 0 < Rmin delta1 delta2).
    apply Rmin_pos.
    apply delta1.
    apply delta2.
  exists (mkposreal _ Hdelta).
  intros.
  assert (Rabs (y - x) < delta1).
    apply (Rlt_le_trans _ (Rmin delta1 delta2)).
    apply H.
    apply Rmin_l.
    elim (Df1 _ H0) ; clear Df1 H0 ; intros pr1_y Df1.
  assert (Rabs (y - x) < delta2).
    apply (Rlt_le_trans _ (Rmin delta1 delta2)).
    apply H.
    apply Rmin_r.
    elim (Df2 _ H0) ; clear Df2 H0 ; intros pr2_y Df2.
  exists (pr1_y, pr2_y).
  unfold Pval_plus ; simpl.
  assert ((pval (f1 y) pr1_y + pval (f2 y) pr2_y -
   (pval (f1 x) pr1_x + pval (f2 x) pr2_x) - (l1 + l2) * (y - x)) =
    (pval (f1 y) pr1_y - pval (f1 x) pr1_x - l1 * (y-x)) +
    (pval (f2 y) pr2_y - pval (f2 x) pr2_x - l2 * (y-x))).
    ring.
    rewrite H0 ; clear H0.
  apply (Rle_trans _ (Rabs
  (pval (f1 y) pr1_y - pval (f1 x) pr1_x - l1*(y-x)) + Rabs (
   (pval (f2 y) pr2_y - pval (f2 x) pr2_x - l2*(y-x))))).
  apply Rabs_triang.
  rewrite (double_var eps).
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  apply Df1.
  apply Df2.
Qed.

Lemma Pfun_derivable_pt_lim_opp : forall f x l,
  Pfun_derivable_pt_lim f x l -> Pfun_derivable_pt_lim (fun x => Pval_opp (f x)) x (-l).
Proof.
  unfold Pfun_derivable_pt_lim, Pval_opp.
  simpl.
  intros f x l (pr_x, Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta.
  intros.
  elim (Df _ H) ; clear Df H ; intros pr_y Df.
  exists pr_y.
  unfold Rminus.
  rewrite <- 2!Ropp_plus_distr, Ropp_mult_distr_l_reverse.
  rewrite Rabs_Ropp.
  apply Df.
Qed.

Lemma Pfun_derivable_pt_lim_minus : forall f1 f2 x l1 l2,
  Pfun_derivable_pt_lim f1 x l1 -> Pfun_derivable_pt_lim f2 x l2 ->
  Pfun_derivable_pt_lim (fun x => Pval_minus (f1 x) (f2 x)) x (l1 - l2).
Proof.
  intros.
  apply Pfun_derivable_pt_lim_plus.
  apply X.
  apply Pfun_derivable_pt_lim_opp.
  apply X0.
Qed.

Lemma Pfun_derivable_pt_lim_mult :
  forall f1 f2 x l1 l2 d1 d2,
  Pfun_derivable_pt_lim f1 x l1 -> Pfun_derivable_pt_lim f2 x l2 ->
  Pfun_derivable_pt_lim (fun x => Pval_mult (f1 x) (f2 x)) x (l1 * pval (f2 x) d2 + pval (f1 x) d1 * l2).
Proof.
  intros f1 f2 x l1 l2 d1 d2 Df1 Df2.
  assert (Cf2 : Pfun_continuity_pt f2 x).
    apply Pfun_derivable_continuous_pt.
    exists l2.
    apply Df2.
    simpl in Cf2.
  elim Df1 ; clear Df1 ; intros pr1_x Df1.
  elim Df2 ; clear Df2 ; intros pr2_x Df2.
  elim Cf2 ; clear Cf2 ; intros pr2_x' Cf2.
  rewrite (pHeq _ _ pr2_x) in Cf2 ; clear pr2_x'.
  exists (pr1_x, pr2_x).
  intros.
  assert (Heps2 : 0 < Rmin (eps/(2*Rmax (Rabs l1) 1)) eps).
    apply Rmin_pos.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    apply (Rlt_le_trans 0 1).
    apply Rlt_0_1.
    apply RmaxLess2.
    apply eps.
  elim (Cf2 (mkposreal _ Heps2)) ; clear Cf2 ; intros delta_Cf2 Cf2.
  assert (Heps1a : 0 < eps/(2*2* (Rabs (pval _ pr2_x) + eps))).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    apply Rlt_R0_R2.
    apply Rplus_le_lt_0_compat.
    apply Rabs_pos.
    apply eps.
  elim (Df1 (mkposreal _ Heps1a)) ; clear Df1 ; intros delta_Df1 Df1.
  assert (Heps1b : 0 < (eps/(2*2*Rmax (Rabs (pval _ pr1_x)) 1))).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    apply Rlt_R0_R2.
    apply (Rlt_le_trans 0 1).
    apply Rlt_0_1.
    apply RmaxLess2.
  elim (Df2 (mkposreal _ Heps1b)) ; clear Df2 ; intros delta_Df2 Df2.
  assert (Hdelta : 0 < Rmin (Rmin delta_Df1 delta_Df2) delta_Cf2).
    apply Rmin_pos.
    apply Rmin_pos.
    apply delta_Df1.
    apply delta_Df2.
    apply delta_Cf2.
  exists (mkposreal _ Hdelta).

  intros.
  assert (Rabs (y - x) < delta_Cf2).
    apply (Rlt_le_trans _ (Rmin (Rmin delta_Df1 delta_Df2) delta_Cf2)).
    simpl in H ; apply H.
    apply Rmin_r.
  elim (Cf2 _ H0) ; clear Cf2 H0 ; intros pr2_y Cf2.
  assert (Rabs (y - x) < delta_Df1).
    apply (Rlt_le_trans _ (Rmin delta_Df1 delta_Df2)).
    apply (Rlt_le_trans _ (Rmin (Rmin delta_Df1 delta_Df2) delta_Cf2)).
    simpl in H ; apply H.
    apply Rmin_l.
    apply Rmin_l.
  elim (Df1 _ H0) ; clear Df1 H0 ; intros pr1_y Df1.
  assert (Rabs (y - x) < delta_Df2).
    apply (Rlt_le_trans _ (Rmin delta_Df1 delta_Df2)).
    apply (Rlt_le_trans _ (Rmin (Rmin delta_Df1 delta_Df2) delta_Cf2)).
    apply H.
    apply Rmin_l.
    apply Rmin_r.
  elim (Df2 _ H0) ; clear Df2 H0 ; intros pr2_y' Df2.
  exists (pr1_y, pr2_y).
  assert (eps * Rabs (y - x) = (eps/4 * Rabs (y-x) + eps/4 * Rabs (y-x)) + eps/2 * Rabs (y-x)).
    field.
    rewrite H0 ; clear H0.
  rewrite (pHeq _ d1 pr1_x).
  rewrite (pHeq _ d2 pr2_x).
  simpl.
  replace (pval _ pr1_y * pval _ pr2_y - pval _ pr1_x * pval _ pr2_x -
    (l1 * pval _ pr2_x + pval _ pr1_x * l2) * (y - x)) with
    ((pval _ pr1_y - pval _ pr1_x - l1 * (y - x)) * pval _ pr2_y + pval _ pr1_x * (pval _ pr2_y - pval _ pr2_x - l2 * (y - x)) +
    (l1 * (pval _ pr2_y - pval _ pr2_x) * (y - x))) by ring.
  apply (Rle_trans _ (
    Rabs ((pval _ pr1_y - pval _ pr1_x - l1 * (y - x)) * pval _ pr2_y +
          pval _ pr1_x * (pval _ pr2_y - pval _ pr2_x - l2 * (y - x))) +
    Rabs (l1 * (pval _ pr2_y - pval _ pr2_x) * (y - x)))).
  apply Rabs_triang.
  apply Rplus_le_compat.
  apply (Rle_trans _ (
    Rabs ((pval _ pr1_y - pval _ pr1_x - l1 * (y - x)) * pval _ pr2_y) +
    Rabs (pval _ pr1_x * (pval _ pr2_y - pval _ pr2_x - l2 * (y - x))))).
  apply Rabs_triang.
  apply Rplus_le_compat.

  rewrite Rabs_mult.
  apply (Rle_trans _ ((eps / (4 * (Rabs (pval _ pr2_x) + eps))) * Rabs (y-x) * Rabs (pval _ pr2_y))).
    apply Rmult_le_compat_r.
    apply Rabs_pos.
    apply Df1.
  rewrite <- (Rmult_1_r (eps / 4 * Rabs (y - x))).
  assert (eps / (4 * (Rabs (pval _ pr2_x) + eps)) * Rabs (y - x) *
    Rabs (pval _ pr2_y) = (eps / 4 * Rabs (y - x)) * (Rabs (pval _ pr2_y) / (Rabs (pval _ pr2_x) + eps))).
  field.
  apply Rgt_not_eq.
  apply Rlt_gt.
  apply Rplus_le_lt_0_compat.
  apply Rabs_pos.
  apply eps.
  rewrite H0 ; clear H0.
  apply Rmult_le_compat_l.
  apply Rmult_le_pos.
  apply Rdiv_le_pos.
  apply Rlt_le.
  apply eps.
  apply Rmult_lt_0_compat.
  apply Rlt_R0_R2.
  apply Rlt_R0_R2.
  apply Rabs_pos.
  apply (Rdiv_le_1 (Rabs (pval _ pr2_y)) (Rabs (pval _ pr2_x) + eps)).
  apply Rplus_le_lt_0_compat.
  apply Rabs_pos.
  apply eps.
  rewrite Rplus_comm.
  apply (Rle_minus2 (Rabs (pval _ pr2_y)) eps (Rabs (pval _ pr2_x))).
  apply (Rle_trans _ (Rabs (pval _ pr2_y - pval _ pr2_x))).
  apply Rabs_triang_inv.
  apply (Rle_trans _ (Rmin (eps / (2 * Rmax (Rabs l1) 1)) eps)).
  simpl in Cf2 ; apply Rlt_le ; apply Cf2.
  apply Rmin_r.

  rewrite Rabs_mult.
  assert (eps / 4 * Rabs (y - x) = Rmax (Rabs (pval _ pr1_x)) 1 * (eps / (4 * Rmax (Rabs (pval _ pr1_x)) 1) * Rabs (y - x))).
    field.
    apply Rgt_not_eq.
    apply Rlt_gt.
    apply (Rlt_le_trans _ 1).
    apply Rlt_0_1.
    apply RmaxLess2.
    rewrite H0 ; clear H0.
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rabs_pos.
  apply RmaxLess1.
  rewrite (pHeq _ pr2_y' pr2_y) in Df2.
  apply Df2.

  rewrite Rabs_mult.
  rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  assert (eps / 2 = Rmax (Rabs l1) 1 * (eps / (2 * Rmax (Rabs l1) 1))).
    field.
    apply Rgt_not_eq.
    apply Rlt_gt.
    apply (Rlt_le_trans _ 1).
    apply Rlt_0_1.
    apply RmaxLess2.
    rewrite H0 ; clear H0.
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rabs_pos.
  apply RmaxLess1.
  apply (Rle_trans _ (Rmin (eps / (2 * Rmax (Rabs l1) 1)) eps)).
  apply Rlt_le ; apply Cf2.
  apply Rmin_l.
Qed.

Lemma Pfun_derivable_pt_lim_scal : forall a f x l,
  Pfun_derivable_pt_lim f x l -> Pfun_derivable_pt_lim (fun x => Pval_scal a (f x)) x (a * l).
Proof.
  intros.
  unfold Pfun_derivable_pt_lim.
  simpl.
  elim X ; intros pr_x Df.
  destruct (Pfun_derivable_pt_lim_mult (fun _ => Pval_val a) f x 0 l I pr_x
    (Pfun_derivable_pt_lim_const a x) X) as (d,H).
  exists (I, snd d).
  intros.
  replace (a*l) with (0 * pval _ pr_x + a*l) by ring.
  apply H.
Qed.

Lemma Pfun_derivable_pt_lim_comp : forall f1 f2 x l1 l2 d,
  Pfun_derivable_pt_lim f2 x l2 -> Pfun_derivable_pt_lim f1 (pval (f2 x) d) l1 ->
  Pfun_derivable_pt_lim (fun x => Pfun_app f1 (f2 x)) x (l1*l2).
Proof.
  intros f1 f2 x l1 l2 d Df2 Df1.
  assert (Cf2 : Pfun_continuity_pt f2 x).
    apply Pfun_derivable_continuous_pt.
    exists l2.
    apply Df2.
  elim Df2 ; clear Df2 ; intros pr2_x Df2.
  elim Df1 ; clear Df1 ; intros pr1_x Df1.
  elim Cf2 ; clear Cf2 ; intros pr2'_x Cf2.
  exists (existT _ d pr1_x) ; intros.
  assert (Heps1 : 0 < eps/(2*Rmax (Rabs l2) 1)).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    apply (Rlt_le_trans _ 1).
    apply Rlt_0_1.
    apply RmaxLess2.
  elim (Df1 (mkposreal _ Heps1)) ; clear Df1 ; intros eps_c2 Df1.
  elim (Cf2 eps_c2) ; clear Cf2 ; intros delta1 Cf2.
  assert (Heps2 : 0 < eps/ (2 * (Rabs l1 + (eps / (2 * Rmax (Rabs l2) 1))))).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rlt_R0_R2.
    apply Rplus_le_lt_0_compat.
    apply Rabs_pos.
    apply Heps1.
  elim (Df2 (mkposreal _ Heps2)) ; clear Df2 ; intros delta2 Df2.
  assert (Hdelta : 0 < Rmin delta1 delta2).
    apply Rmin_pos.
    apply delta1.
    apply delta2.
  exists (mkposreal _ Hdelta).
  intros.
  assert (Rabs (y - x) < delta2).
    apply (Rlt_le_trans _ (Rmin delta1 delta2)).
    apply H.
    apply Rmin_r.
  elim (Df2 _ H0) ; clear Df2 H0 ; intros pr2_y Df2.
  assert (Rabs (y - x) < delta1).
    apply (Rlt_le_trans _ (Rmin delta1 delta2)).
    apply H.
    apply Rmin_l.
  elim (Cf2 _ H0) ; clear Cf2 H0 ; intros pr2'_y Cf2.
  rewrite (pHeq _ _ d) in Cf2.
  elim (Df1 _ Cf2) ; clear Df1 Cf2 ; intros pr1_y Df1.
  exists (existT _ pr2'_y pr1_y).
  simpl.
  replace (pval _ pr1_y - pval _ pr1_x - l1 * l2 * (y - x))
    with (pval _ pr1_y - pval _ pr1_x - l1 * (pval _ pr2_y - pval _ pr2_x)
      + l1 * (pval _ pr2_y - pval _ pr2_x - l2 * (y - x))) by ring.
  refine (Rle_trans _ _ _ (Rabs_triang _ _) _).
  apply (Rle_trans _ ((eps / (2 * Rmax (Rabs l2) 1)) * Rabs (pval _ pr2_y - pval _ pr2_x) +
    Rabs (l1 * (pval _ pr2_y - pval _ pr2_x - l2 * (y - x))))).
  apply Rplus_le_compat_r.
  rewrite (pHeq _ pr2_y pr2'_y), (pHeq _ pr2_x d).
  apply Df1.
  rewrite Rabs_mult.
  apply (Rle_trans _ (((eps / (2 * Rmax (Rabs l2) 1)) + Rabs l1) *
    Rabs (pval _ pr2_y - pval _ pr2_x - l2 * (y - x))
    + (eps / (2 * Rmax (Rabs l2) 1)) * Rabs l2 * Rabs (y-x))).
  rewrite (Rmult_plus_distr_r (eps / (2 * Rmax (Rabs l2) 1)) (Rabs l1)).
  rewrite Rplus_assoc.
  rewrite (Rplus_comm _ ((eps / (2 * Rmax (Rabs l2) 1)) * Rabs l2 * Rabs (y - x))).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  rewrite Rmult_assoc.
  rewrite <- (Rmult_plus_distr_l (eps / (2 * Rmax (Rabs l2) 1))).
  apply Rmult_le_compat_l.
  apply Rlt_le.
  apply Heps1.
  rewrite <- Rabs_mult.
  refine (Rle_trans _ _ _ _ (Rabs_triang _ _)).
  right ; apply f_equal ; ring.
  assert (eps * Rabs (y - x) = (eps/2 * Rabs (y-x)) + (eps/2 * Rabs (y-x))).
    field.
    rewrite H0 ; clear H0.
  apply Rplus_le_compat.
  assert (eps / 2 * Rabs (y - x) = ((mkposreal _ Heps1) + Rabs l1) * (eps / (2 * (Rabs l1 + (mkposreal _ Heps1))) * Rabs (y-x))).
    field.
    apply Rgt_not_eq.
    apply Rlt_gt.
    apply Rplus_le_lt_0_compat.
    apply Rabs_pos.
    apply (mkposreal _ Heps1).
    rewrite H0 ; clear H0.
  apply Rmult_le_compat_l.
  apply Rlt_le.
  apply Rplus_lt_le_0_compat.
  apply (mkposreal _ Heps1).
  apply Rabs_pos.
  simpl ; simpl in Df2 ; apply Df2.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  unfold Rmax.
  destruct (Rle_dec (Rabs l2) 1).
  rewrite <- (Rmult_1_r (eps/2)).
  apply Rmult_le_compat.
  apply Rlt_le.
  apply Rdiv_lt_0_compat.
  apply eps.
  rewrite Rmult_1_r.
  apply Rlt_R0_R2.
  apply Rabs_pos.
  apply Req_le.
  field.
  apply r.
  apply Req_le.
  field.
  apply Rnot_le_gt in n.
  apply Rgt_not_eq.
  apply (Rlt_trans _ 1).
  apply Rlt_0_1.
  apply n.
Qed.

Lemma Pfun_derive_pt_fun1 : forall f x pr1 pr2 pr2',
  Pfun_derive_pt (Pfun_fun (derive f pr1)) x pr2 = derive2 f pr2' x.
Proof.
  intros.
  rewrite (Pfun_derive_pt_fun _ _ _ ((derivable_derive _ _ pr2') x)),
  (derive_pt_derive _ _ _ _ (pr2' x)).
  reflexivity.
Qed.
(* Si intégrale à paramètre
(** * Value theorem *)


Lemma Pfun_Value_theorem : forall (f : partial_fun) (a b : R),
  let (f_dom,f_val,f_eq) := f in
  forall (der : forall y, Rmin a b <= y  <= Rmax a b -> Pfun_derivable_pt (Pfun f_dom f_val f_eq) y),
  exists c, forall (pr_c : Rmin a b <= c <= Rmax a b),
  f_val b (Pfun_derivable_definie_a_b (Pfun f_dom f_val f_eq) a b der _ (Rmin_Rmax_r a b))
  - f_val a (Pfun_derivable_definie_a_b (Pfun f_dom f_val f_eq) a b der _ (Rmin_Rmax_l _ _))
    = (Pfun_derive_pt (Pfun f_dom f_val f_eq) c (der c pr_c)) * (b-a).
Proof.
  destruct f as (f_dom, f_val, f_eq).
  intros a0 b0 ; set (a := Rmin a0 b0) ; set (b := Rmax a0 b0) ; intros.

  assert (def : forall y : R, a <= y <= b -> f_dom y).
    intros ; apply (Pfun_derivable_definie_a_b (Pfun f_dom f_val f_eq) a0 b0).
    apply der.
    apply H.
  assert (df_a : Pfun_derivable_pt (Pfun f_dom f_val f_eq) a).
    apply der.
    split ;
    [apply Rle_refl | apply Rmin_Rmax].
  assert (df_b : Pfun_derivable_pt (Pfun f_dom f_val f_eq) b).
    apply der.
    split ;
    [apply Rmin_Rmax | apply Rle_refl].

  set (f := Pfun_C1_eval_a_b f_dom f_val f_eq a0 b0 def df_a df_b).
  assert (Df : derivable f).
    apply (Pfun_derivable_C1_eval_a_b (Pfun f_dom f_val f_eq)).
    apply der.
  assert (f_val b0
    (Pfun_derivable_definie_a_b (Pfun f_dom f_val f_eq) a0 b0 der b0
       (Rmin_Rmax_r a0 b0)) = f b0).
    unfold f, Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a b0).
    destruct (Rle_dec b0 b).
    apply f_eq.
    elim n ; apply RmaxLess2.
    elim n ; apply Rmin_r.
    rewrite H ; clear H.
  assert (f_val a0
    (Pfun_derivable_definie_a_b (Pfun f_dom f_val f_eq) a0 b0 der a0
       (Rmin_Rmax_l a0 b0)) = f a0).
    unfold f, Pfun_C1_eval_a_b ; fold a b.
    destruct (Rle_dec a a0).
    destruct (Rle_dec a0 b).
    apply f_eq.
    elim n ; apply RmaxLess1.
    elim n ; apply Rmin_l.
    rewrite H ; clear H.

  assert (MVT : exists c : R, f b0 - f a0 = derive_pt f c (Df c) * (b0 - a0)
    /\ a <= c <= b).
    apply Value_theorem.
  destruct MVT as (c,(MVT,Hc)).
  exists c.
  intros.
  rewrite MVT.
  apply sym_equal.
  apply Rmult_eq_compat_r.
  apply (Pfun_derive_pt_C1_eval_a_b (Pfun f_dom f_val f_eq)).
  apply pr_c.
Qed.
*)

(** * Riemann integral *)

Definition Pval_Riemann_integrable (f : R -> partial_val) a b :=
  { pr : (forall y, Rmin a b <= y <= Rmax a b -> pdom (f y)) &
    Riemann_integrable (Pfun_eval_a_b f a b pr) a b }.

Definition Pval_RiemannInt (f : R -> partial_val) a b
  (pr :  Pval_Riemann_integrable f a b) := RiemannInt (projT2 pr).

(** Exchange of bounds *)

Lemma Pval_Riemann_integrable_bounds : forall f a b,
  Pval_Riemann_integrable f a b -> Pval_Riemann_integrable f b a.
Proof.
  intros f a b (pr_ab,Ri_ab).
  assert (pr_ba : forall y : R, Rmin b a <= y <= Rmax b a -> pdom (f y)).
    intros.
    apply pr_ab.
    rewrite Rmin_comm, Rmax_comm.
    apply H.
  exists pr_ba.
  apply RiemannInt_P1.
  apply (Riemann_integrable_expr (Pfun_eval_a_b f a b pr_ab)).
    intros.
    unfold Pfun_eval_a_b.
    destruct (Rle_dec (Rmin a b) x).
    destruct (Rle_dec x (Rmax a b)).
    destruct (Rle_dec (Rmin b a) x).
    destruct (Rle_dec x (Rmax b a)).
    apply pHeq.
    elim n ; rewrite Rmax_comm ; apply H.
    elim n ; rewrite Rmin_comm ; apply H.
    elim n ; apply H.
    elim n ; apply H.
  apply Ri_ab.
Qed.

Lemma Pval_RiemannInt_bounds : forall f a b,
  forall (pr_ab : Pval_Riemann_integrable f a b)
    (pr_ba : Pval_Riemann_integrable f b a),
    Pval_RiemannInt _ _ _ pr_ab = - Pval_RiemannInt _ _ _ pr_ba.
Proof.
  intros.
  unfold Pval_RiemannInt.
  assert (pr2 : Riemann_integrable
                  (Pfun_eval_a_b f b a (projT1 pr_ba)) a b).
    apply RiemannInt_P1.
    apply (projT2 pr_ba).
  rewrite (RiemannInt_expr (Pfun_eval_a_b f a b (projT1 pr_ab)) (Pfun_eval_a_b f b a (projT1 pr_ba)) a b _ pr2).
  apply RiemannInt_P8.
  intros.
  unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x).
    destruct (Rle_dec x (Rmax a b)).
    destruct (Rle_dec (Rmin b a) x).
    destruct (Rle_dec x (Rmax b a)).
    apply pHeq.
    elim n ; rewrite Rmax_comm  ; apply H.
    elim n ; rewrite Rmin_comm  ; apply H.
    elim n  ; apply H.
    elim n  ; apply H.
Qed.

(** The Chasles relation *)

Lemma Pval_Riemann_integrable_Chasles_0 : forall f a b c,
  Pval_Riemann_integrable f a b ->
  Pval_Riemann_integrable f b c ->
  a <= b <= c -> Pval_Riemann_integrable f a c.
Proof.
  intros f a b c (def_ab,Rint_ab) (def_bc,Rint_bc) Hc.
  assert (def_ac : forall y : R, Rmin a c <= y <= Rmax a c -> pdom (f y)).
    rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))).
    rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))).
    intros.
    destruct (Rle_lt_dec y b).
    apply def_ab.
    rewrite (Rmin_eq_l _ _ (proj1 Hc)), (Rmax_eq_l _ _ (proj1 Hc)).
    split ; [apply H | apply r].
    apply def_bc.
    rewrite (Rmin_eq_l _ _ (proj2 Hc)), (Rmax_eq_l _ _ (proj2 Hc)).
    split ; [apply Rlt_le ; apply r | apply H].
    exists def_ac.
    apply (@RiemannInt_P21 _ a b c) ; [apply Hc|apply Hc | | ].
    apply (Riemann_integrable_expr (Pfun_eval_a_b f a b def_ab)).
      rewrite (Rmin_eq_l _ _ (proj1 Hc)), (Rmax_eq_l _ _ (proj1 Hc)) ; intros ;
      unfold Pfun_eval_a_b.
      destruct (Rle_dec (Rmin a b) x) ; [ |
      rewrite (Rmin_eq_l _ _ (proj1 Hc)) in n ; elim n ; apply H].
      destruct (Rle_dec x (Rmax a b)) ; [ |
      rewrite (Rmax_eq_l _ _ (proj1 Hc)) in n ; elim n ; apply H].
      destruct (Rle_dec (Rmin a c) x) ; [ |
      rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) in n ;
      elim n ; apply H].
      destruct (Rle_dec x (Rmax a c)) ; [ |
      rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) in n ;
      elim n ; apply (Rle_trans _ b) ; [apply H | apply Hc]].
      apply pHeq.
      apply Rint_ab.
    apply (Riemann_integrable_expr (Pfun_eval_a_b f b c def_bc)).
      rewrite (Rmin_eq_l _ _ (proj2 Hc)), (Rmax_eq_l _ _ (proj2 Hc)) ; intros ;
      unfold Pfun_eval_a_b.
      destruct (Rle_dec (Rmin b c) x) ; [ |
      rewrite (Rmin_eq_l _ _ (proj2 Hc)) in n ; elim n ; apply H].
      destruct (Rle_dec x (Rmax b c)) ; [ |
      rewrite (Rmax_eq_l _ _ (proj2 Hc)) in n ; elim n ; apply H].
      destruct (Rle_dec (Rmin a c) x) ; [ |
      rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) in n ;
      elim n ; apply (Rle_trans _ b) ; [apply Hc | apply H]].
      destruct (Rle_dec x (Rmax a c)) ; [ |
      rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) in n ;
      elim n ; apply H].
      apply pHeq.
      apply Rint_bc.
Qed.

Lemma Pval_Riemann_integrable_Chasles_1 : forall f a b c,
  Pval_Riemann_integrable f a b ->
  a <= c <= b -> Pval_Riemann_integrable f a c.
Proof.
  intros f a b c (def_ab,Rint_ab) Hc.
  assert (def_ac : forall y : R, Rmin a c <= y <= Rmax a c -> pdom (f y)).
    rewrite (Rmin_eq_l _ _ (proj1 Hc)), (Rmax_eq_l _ _ (proj1 Hc)) ; intros.
    apply def_ab.
    rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))).
    rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))).
    split ; [apply H | apply (Rle_trans _ c) ; [apply H | apply Hc]].
  exists def_ac.
  apply (Riemann_integrable_expr (Pfun_eval_a_b f a b def_ab)).
  rewrite (Rmin_eq_l _ _ (proj1 Hc)).
  rewrite (Rmax_eq_l _ _ (proj1 Hc)).
  intros.
  unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x) ; [| elim n ;
    rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) ;
    apply H].
  destruct (Rle_dec x (Rmax a b)) ; [| elim n ;
    rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) ;
    apply (Rle_trans _ c) ; [apply H | apply Hc]].
  destruct (Rle_dec (Rmin a c) x) ; [| elim n ;
    rewrite (Rmin_eq_l _ _ (proj1 Hc)) ;
    apply H].
  destruct (Rle_dec x (Rmax a c)) ; [| elim n ;
    rewrite (Rmax_eq_l _ _ (proj1 Hc)) ;
    apply H].
  apply pHeq.
  apply (RiemannInt_P22 Rint_ab Hc).
Qed.

Lemma Pval_Riemann_integrable_Chasles_2 : forall f a b c,
  Pval_Riemann_integrable f a b ->
  a <= c <= b -> Pval_Riemann_integrable f c b.
Proof.
  intros f a b c (def_ab,Rint_ab) Hc.
  assert (def_cb : forall y : R, Rmin c b <= y <= Rmax c b -> pdom (f y)).
    rewrite (Rmin_eq_l _ _ (proj2 Hc)), (Rmax_eq_l _ _ (proj2 Hc)) ; intros.
    apply def_ab.
    rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))).
    rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))).
    split ; [apply (Rle_trans _ c) ; [apply Hc | apply H]|apply H].
  exists def_cb.
  apply (Riemann_integrable_expr (Pfun_eval_a_b f a b def_ab)).
  rewrite (Rmin_eq_l _ _ (proj2 Hc)).
  rewrite (Rmax_eq_l _ _ (proj2 Hc)).
  intros.
  unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x) ; [| elim n ;
    rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) ;
    apply (Rle_trans _ c) ; [apply Hc | apply H]].
  destruct (Rle_dec x (Rmax a b)) ; [| elim n ;
    rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Hc) (proj2 Hc))) ;
    apply H].
  destruct (Rle_dec (Rmin c b) x) ; [| elim n ;
    rewrite (Rmin_eq_l _ _ (proj2 Hc)) ;
    apply H].
  destruct (Rle_dec x (Rmax c b)) ; [| elim n ;
    rewrite (Rmax_eq_l _ _ (proj2 Hc)) ;
    apply H].
  apply pHeq.
  apply (RiemannInt_P23 Rint_ab Hc).
Qed.

Lemma Pval_Riemann_integrable_Chasles : forall f a b c,
  Pval_Riemann_integrable f a b ->
  Pval_Riemann_integrable f b c ->
  Pval_Riemann_integrable f a c.
Proof.
  intros f a b c Rint_ab Rint_bc.
  destruct (Rle_lt_dec a b) ;
  destruct (Rle_lt_dec b c) ;
  destruct (Rle_lt_dec a c).
  apply (Pval_Riemann_integrable_Chasles_0 f _ _ _ Rint_ab Rint_bc).
    split ; [apply r | apply r0].
  apply (Rlt_not_le) in r1.
  elim r1.
  apply (Rle_trans _ _ _ r r0).
  apply (Pval_Riemann_integrable_Chasles_1 f _ _ _ Rint_ab).
    split ; [apply r1 | apply Rlt_le ; apply r0].
  apply Pval_Riemann_integrable_bounds in Rint_bc.
  apply Pval_Riemann_integrable_bounds.
  apply (Pval_Riemann_integrable_Chasles_1 f _ _ _ Rint_bc).
    split ; [apply Rlt_le ; apply r1 | apply r].
  apply (Pval_Riemann_integrable_Chasles_2 f _ _ _ Rint_bc).
    split ; [apply Rlt_le ; apply r | apply r1].
  apply Pval_Riemann_integrable_bounds in Rint_ab.
  apply Pval_Riemann_integrable_bounds.
  apply (Pval_Riemann_integrable_Chasles_2 f _ _ _ Rint_ab).
    split ; [apply r0 | apply Rlt_le ; apply r1].
  apply Rle_not_lt in r1.
  elim r1.
  apply (Rlt_trans _ _ _ r0 r).
  apply Pval_Riemann_integrable_bounds in Rint_ab.
  apply Pval_Riemann_integrable_bounds in Rint_bc.
  apply Pval_Riemann_integrable_bounds.
  apply (Pval_Riemann_integrable_Chasles_0 f _ _ _ Rint_bc Rint_ab).
    split ; apply Rlt_le ; [apply r0 | apply r].
Qed.

Lemma Pval_RiemannInt_Chasles_0 : forall f a b c,
  forall pr_ab pr_bc pr_ac, a <= b <= c ->
  Pval_RiemannInt f a b pr_ab + Pval_RiemannInt f b c pr_bc
    = Pval_RiemannInt f a c pr_ac.
Proof.
  intros f a b c (def_ab,Rint_ab) (def_bc,Rint_bc) (def_ac,Rint_ac) Habc.
  unfold Pval_RiemannInt ; simpl.
  assert (pr_ab : Riemann_integrable (Pfun_eval_a_b f a c def_ac) a b).
    apply (RiemannInt_P22 Rint_ac).
    apply Habc.
  rewrite (RiemannInt_expr (Pfun_eval_a_b f a b def_ab)
    (Pfun_eval_a_b f a c def_ac) a b _ pr_ab).
  assert (pr_bc : Riemann_integrable (Pfun_eval_a_b f a c def_ac) b c).
    apply (RiemannInt_P23 Rint_ac).
    apply Habc.
  rewrite (RiemannInt_expr (Pfun_eval_a_b f b c def_bc)
    (Pfun_eval_a_b f a c def_ac) b c _ pr_bc).
  apply RiemannInt_P25.
  apply Habc.
  apply Habc.

  rewrite (Rmin_eq_l _ _ (proj2 Habc)), (Rmax_eq_l _ _ (proj2 Habc)) ; intros.
  unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin b c) x) ;
  [ | elim n ; rewrite (Rmin_eq_l _ _ (proj2 Habc)) ; apply H].
  destruct (Rle_dec x (Rmax b c)) ;
  [ | elim n ; rewrite (Rmax_eq_l _ _ (proj2 Habc)) ; apply H].
  destruct (Rle_dec (Rmin a c) x) ;
  [ | elim n ; rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Habc) (proj2 Habc))) ;
  apply (Rle_trans _ b) ; [apply Habc | apply H]].
  destruct (Rle_dec x (Rmax a c)) ;
  [ | elim n ; rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Habc) (proj2 Habc))) ;
  apply H].
  apply pHeq.

  rewrite (Rmin_eq_l _ _ (proj1 Habc)), (Rmax_eq_l _ _ (proj1 Habc)) ; intros.
  unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x) ;
  [ | elim n ; rewrite (Rmin_eq_l _ _ (proj1 Habc)) ; apply H].
  destruct (Rle_dec x (Rmax a b)) ;
  [ | elim n ; rewrite (Rmax_eq_l _ _ (proj1 Habc)) ; apply H].
  destruct (Rle_dec (Rmin a c) x) ;
  [ | elim n ; rewrite (Rmin_eq_l _ _ (Rle_trans _ _ _ (proj1 Habc) (proj2 Habc))) ;
  apply H].
  destruct (Rle_dec x (Rmax a c)) ;
  [ | elim n ; rewrite (Rmax_eq_l _ _ (Rle_trans _ _ _ (proj1 Habc) (proj2 Habc))) ;
  apply (Rle_trans _ b) ; [apply H | apply Habc]].
  apply pHeq.
Qed.

Lemma Pval_RiemannInt_Chasles : forall f a b c,
  forall pr_ab pr_bc pr_ac,
  Pval_RiemannInt f a b pr_ab + Pval_RiemannInt f b c pr_bc
    = Pval_RiemannInt f a c pr_ac.
Proof.
  intros f a b c Rint_ab Rint_bc Rint_ac.
  destruct (Rle_lt_dec a b) ;
  destruct (Rle_lt_dec b c) ;
  destruct (Rle_lt_dec a c).

  apply Pval_RiemannInt_Chasles_0.
    split ; [apply r|apply r0].
  apply Rlt_not_le in r1 ; elim r1 ; apply (Rle_trans _ _ _ r r0).

  assert (pr_cb : Pval_Riemann_integrable f c b).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_bc).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_cb).
  rewrite <- (Pval_RiemannInt_Chasles_0 f a c b Rint_ac pr_cb).
  ring.
  split ; [apply r1 | apply Rlt_le ; apply r0].

  assert (pr_ca : Pval_Riemann_integrable f c a).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_ac).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_ca).
  assert (pr_cb : Pval_Riemann_integrable f c b).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_bc).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_cb).
  rewrite <- (Pval_RiemannInt_Chasles_0 f c a b pr_ca Rint_ab).
  ring.
  split ; [apply Rlt_le ; apply r1 | apply r].

  assert (pr_ba : Pval_Riemann_integrable f b a).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_ab).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_ba).
  rewrite <- (Pval_RiemannInt_Chasles_0 f b a c pr_ba Rint_ac).
  ring.
  split ; [apply Rlt_le ; apply r | apply r1].

  assert (pr_ba : Pval_Riemann_integrable f b a).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_ab).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_ba).
  assert (pr_ca : Pval_Riemann_integrable f c a).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_ac).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_ca).
  rewrite <- (Pval_RiemannInt_Chasles_0 f b c a Rint_bc pr_ca).
  ring.
  split ; [apply r0 | apply Rlt_le ; apply r1].

  apply Rle_not_lt in r1 ; elim r1 ; apply (Rlt_trans _ _ _ r0 r).

  assert (pr_ba : Pval_Riemann_integrable f b a).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_ab).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_ba).
  assert (pr_ca : Pval_Riemann_integrable f c a).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_ac).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_ca).
  assert (pr_cb : Pval_Riemann_integrable f c b).
    apply (Pval_Riemann_integrable_bounds f _ _ Rint_bc).
  rewrite (Pval_RiemannInt_bounds f _ _ _ pr_cb).
  rewrite <- (Pval_RiemannInt_Chasles_0 f c b a pr_cb pr_ba).
  ring.
  split ; apply Rlt_le ; [apply r0 | apply r].
Qed.

(** Rieman integral of a total function *)

Lemma Pval_Riemann_integrable_fun : forall (f : R -> R) a b,
  Riemann_integrable f a b -> Pval_Riemann_integrable (fun x => Pval_val (f x)) a b.
Proof.
  intros.
  unfold Pval_Riemann_integrable.
  assert (pr : forall y : R, Rmin a b <= y <= Rmax a b -> True).
    intuition.
  exists pr.
  apply (Riemann_integrable_expr f).
  intros ; unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x) ; [| elim n ; apply H].
  destruct (Rle_dec x (Rmax a b)) ; [| elim n ; apply H].
  reflexivity.
  apply X.
Qed.

Lemma Pval_RiemannInt_fun : forall (f : R -> R) a b pr_t pr_p,
  Pval_RiemannInt (Pfun_fun f) a b pr_p = @RiemannInt f a b pr_t.
Proof.
  intros.
  unfold Pval_RiemannInt.
  apply RiemannInt_expr.
  intros ; unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x) ; [| elim n ; apply H].
  destruct (Rle_dec x (Rmax a b)) ; [| elim n ; apply H].
  reflexivity.
Qed.

(** Continuity implies Riemann-integrable *)

Lemma Pfun_cont_impl_Rint : forall f a b,
  (forall y, Rmin a b <= y <= Rmax a b -> Pfun_continuity_pt f y) ->
  Pval_Riemann_integrable f a b.
Proof.
  intros f a b Cf.
  assert (def_ab : forall y, Rmin a b <= y <= Rmax a b -> pdom (f y)).
    intros.
    elim (Cf _ H) ; clear Cf ; intros pr_y Cf.
    apply pr_y.
  unfold Rmin, Rmax in Cf ; destruct (Rle_dec a b).
  exists def_ab.
  apply continuity_implies_RiemannInt.
  apply r.
  intros ; apply Pfun_continuity_pt_eval_a_b_0.
  rewrite (Rmin_eq_l _ _ r)  , (Rmax_eq_l _ _ r) ; apply H.
  apply (Cf _ H).

  apply Pval_Riemann_integrable_bounds.
  rewrite Rmin_comm, Rmax_comm in def_ab ; exists def_ab.
  apply continuity_implies_RiemannInt.
  apply Rlt_le ; apply Rnot_le_lt in n ; apply n.
  intros ; apply Pfun_continuity_pt_eval_a_b_0.
  rewrite Rmin_comm, Rmax_comm ; apply Rnot_le_lt in n ;
  rewrite (Rmin_eq_r _ _ n)  , (Rmax_eq_r _ _ n) ; apply H.
  apply (Cf _ H).
Qed.