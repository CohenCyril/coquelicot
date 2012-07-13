Require Import Reals.

Require Import Rcomplements Function1.

Open Local Scope R_scope.

(** * Basic functions *)

Definition Fct2_const (a x y:R) : R := a.
Definition Fct2_Var1 (x y:R) := x.
Definition Fct2_Var2 (x y : R) := y.

Definition Fct2_proj1 (f : R -> R) (x y : R) := f x.
Definition Fct2_proj2 (f : R -> R) (x y : R) := f y.
Definition Fct2_opp f (x y : R) := - f x y.
Definition Fct2_plus f g (x y : R) := f x y + g x y.
Definition Fct2_minus f g (x y : R) := f x y - g x y.
Definition Fct2_mult f g (x y : R) := f x y * g x y.

Definition Fct2_comp1 (f1 : R -> R) (f2 : R -> R -> R) (x y : R) :=
  f1 (f2 x y).
Definition Fct2_comp2 (f1 : R -> R -> R) (f2 : R -> R -> R) (f3 : R -> R -> R)
  (x y : R) := f1 (f2 x y) (f3 x y).
Definition Fct_comp2 (f1 : R -> R -> R) (f2 : R -> R) (f3 : R -> R)
  (x : R) := f1 (f2 x) (f3 x).

(** * Partial derivatives *)

(** First variable *)
Definition derivable10_pt_lim (f : R -> R -> R) (x y l : R) :=
  derivable_pt_lim (fun x => f x y) x l.
Definition derivable10_pt (f : R -> R -> R) (x y : R) :=
  derivable_pt (fun x => f x y) x.
Definition derive10_pt (f : R -> R -> R) (x y : R) (pr : derivable10_pt f x y) :=
  derive_pt (fun x => f x y) x pr.
Definition derivable10 (f : R -> R -> R) :=
  forall x y, derivable_pt (fun x => f x y) x.
Definition derive10 (f : R -> R -> R) (pr : derivable10 f) :=
  (fun x y => derive_pt (fun x => f x y) x (pr x y)).

Lemma derivable10_derive10_0 : forall (f : R -> R -> R) (x y l : R) (pr10 : derivable10_pt f x y),
  derivable10_pt_lim f x y l -> derive10_pt f x y pr10 = l.
Proof.
  intros.
  apply derive_pt_eq_0 ; apply H.
Qed.
Lemma derivable10_derive10_1 : forall (f : R -> R -> R) (x y l : R) (pr10 : derivable10_pt f x y),
  derive10_pt f x y pr10 = l -> derivable10_pt_lim f x y l.
Proof.
  intros.
  apply (derive_pt_eq_1 _ _ _ pr10) ; apply H.
Qed.
Lemma derivable10_derive10 : forall (f : R -> R -> R) (x y l : R) (pr10 : derivable10_pt f x y),
  derive10_pt f x y pr10 = l <-> derivable10_pt_lim f x y l.
Proof.
  intros.
  apply derive_pt_eq.
Qed.

Lemma Corresp_d10 : forall f x y pr,
  derivable10_pt_lim f x y (derive10_pt f x y pr).
Proof.
  intros.
  apply (derivable10_derive10 _ _ _ _ pr).
  reflexivity.
Qed.

(** Second variable *)

Definition derivable01_pt_lim (f : R -> R -> R) (x y l : R) :=
  derivable_pt_lim (fun y => f x y) y l.
Definition derivable01_pt (f : R -> R -> R) (x y : R) :=
  derivable_pt (fun y => f x y) y.
Definition derive01_pt (f : R -> R -> R) (x y : R) (pr : derivable01_pt f x y) :=
  derive_pt (fun y => f x y) y pr.
Definition derivable01 (f : R -> R -> R) :=
  forall x y, derivable_pt (fun y => f x y) y.
Definition derive01 (f : R -> R -> R) (pr : derivable01 f) :=
  (fun x y => derive_pt (fun y => f x y) y (pr x y)).

Lemma derivable01_derive01_0 : forall (f : R -> R -> R) (x y l : R) (pr01 : derivable01_pt f x y),
  derivable01_pt_lim f x y l -> derive01_pt f x y pr01 = l.
Proof.
  intros.
  apply derive_pt_eq_0 ; apply H.
Qed.
Lemma derivable01_derive01_1 : forall (f : R -> R -> R) (x y l : R) (pr01 : derivable01_pt f x y),
  derive01_pt f x y pr01 = l -> derivable01_pt_lim f x y l.
Proof.
  intros.
  apply (derive_pt_eq_1 _ _ _ pr01) ; apply H.
Qed.
Lemma derivable01_derive01 : forall (f : R -> R -> R) (x y l : R) (pr01 : derivable01_pt f x y),
  derive01_pt f x y pr01 = l <-> derivable01_pt_lim f x y l.
Proof.
  intros.
  apply derive_pt_eq.
Qed.

Lemma Corresp_d01 : forall f x y pr,
  derivable01_pt_lim f x y (derive01_pt f x y pr).
Proof.
  intros.
  apply (derivable01_derive01 _ _ _ _ pr).
  reflexivity.
Qed.

(** * Second partial derivative *)

(** First variable *)

Definition derivable20_pt_lim (f : R -> R -> R) (x y l : R) :=
  derivable2_pt_lim (fun x => f x y) x l.
Definition derivable20_pt (f : R -> R -> R) (x y : R) :=
  derivable2_pt (fun x => f x y) x.
Definition derive20_pt (f : R -> R -> R) (x y : R) (pr : derivable20_pt f x y) :=
  derive2_pt (fun x => f x y) x pr.
Definition derivable20 (f : R -> R -> R) :=
  forall x y, derivable2_pt (fun x => f x y) x.
Definition derive20 (f : R -> R -> R) (pr : derivable20 f) :=
  (fun x y => derive2_pt (fun x => f x y) x (pr x y)).

Lemma d20_pt_impl_d10_pt : forall (f : R -> R -> R) (x y : R),
  derivable20_pt f x y -> derivable10_pt f x y.
Proof.
  intros f x y (l,(f',(pr_10,pr_20))).
  exists (f' x).
  apply pr_10.
Qed.
Lemma d20_impl_d10 : forall (f : R -> R -> R),
  derivable20 f -> derivable10 f.
Proof.
  intros f d20 x y.
  apply d20_pt_impl_d10_pt.
  apply d20.
Qed.

Lemma derivable20_derive20_0 : forall (f : R -> R -> R) (x y l : R) (pr20 : derivable20_pt f x y),
  derivable20_pt_lim f x y l -> derive20_pt f x y pr20 = l.
Proof.
  intros.
  apply derivable2_derive2_0 ; apply H.
Qed.
Lemma derivable20_derive20_1 : forall (f : R -> R -> R) (x y l : R) (pr20 : derivable20_pt f x y),
  derive20_pt f x y pr20 = l -> derivable20_pt_lim f x y l.
Proof.
  intros.
  apply (derivable2_derive2_1 _ _ _ pr20) ; apply H.
Qed.
Lemma derivable20_derive20 : forall (f : R -> R -> R) (x y l : R) (pr20 : derivable20_pt f x y),
  prod (derive20_pt f x y pr20 = l -> derivable20_pt_lim f x y l)
    (derivable20_pt_lim f x y l -> derive20_pt f x y pr20 = l).
Proof.
  split.
  apply derivable20_derive20_1.
  apply derivable20_derive20_0.
Qed.

Lemma Corresp_d20 : forall f x y pr,
  derivable20_pt_lim f x y (derive20_pt f x y pr).
Proof.
  intros.
  apply (derivable20_derive20 _ _ _ _ pr).
  reflexivity.
Qed.
Lemma Corresp_d20_d10 : forall f x y pr1 pr2,
  derivable20_pt_lim f x y (derive10_pt (derive10 f pr1) x y pr2).
Proof.
  intros.
  exists (fun x => derive10 f pr1 x y) ; split.
  intros ; apply (derive_pt_eq_1 _ _ _ (pr1 x0 y)) ; reflexivity.
  apply Corresp_d10.
Qed.
Lemma Corresp_d10_d20 : forall f x y pr1 pr2,
  derivable10_pt_lim (derive10 f pr1) x y
    (derive20_pt f x y pr2).
Proof.
  intros.
  assert (derivable10_pt (derive10 f pr1) x y).
    destruct pr2 as (l,(f',(pr,pr'))).
    exists l.
    apply (derivable_pt_lim_expr f').
      intros ; apply sym_equal, derivable10_derive10_0, pr.
    apply pr'.
  apply (derivable10_derive10 _ _ _ _ H).
  apply sym_equal, (derivable20_derive20 _ _ _ _ pr2).
  apply Corresp_d20_d10.
Qed.

Lemma derivable20_10_pt_lim :
  forall f' f x t l,
  (forall x, derivable10_pt_lim f x t (f' x)) ->
  derivable_pt_lim f' x l ->
  derivable20_pt_lim f x t l.
Proof.
  intros f' f x t l H H'.
  apply derivable2_pt_lim_derivable_pt_lim with (1 := H) (2 := H').
Qed.

(** Second variable *)

Definition derivable02_pt_lim (f : R -> R -> R) (x y l : R) :=
  derivable2_pt_lim (fun y => f x y) y l.
Definition derivable02_pt (f : R -> R -> R) (x y : R) :=
  derivable2_pt (fun y => f x y) y.
Definition derive02_pt (f : R -> R -> R) (x y : R) (pr : derivable02_pt f x y) :=
  derive2_pt (fun y => f x y) y pr.
Definition derivable02 (f : R -> R -> R) :=
  forall x y, derivable2_pt (fun y => f x y) y.
Definition derive02 (f : R -> R -> R) (pr : derivable02 f) :=
  (fun x y => derive2_pt (fun y => f x y) y (pr x y)).

Lemma d02_pt_impl_d01_pt : forall (f : R -> R -> R) (x y : R),
  derivable02_pt f x y -> derivable01_pt f x y.
Proof.
  intros f x y (l,(f',(pr_01,pr_02))).
  exists (f' y).
  apply pr_01.
Qed.
Lemma d02_impl_d01 : forall (f : R -> R -> R),
  derivable02 f -> derivable01 f.
Proof.
  intros f d02 x y.
  apply d02_pt_impl_d01_pt.
  apply d02.
Qed.

Lemma derivable02_derive02_0 : forall (f : R -> R -> R) (x y l : R) (pr02 : derivable02_pt f x y),
  derivable02_pt_lim f x y l -> derive02_pt f x y pr02 = l.
Proof.
  intros.
  apply derivable2_derive2_0.
  apply H.
Qed.
Lemma derivable02_derive02_1 : forall (f : R -> R -> R) (x y l : R) (pr02 : derivable02_pt f x y),
  derive02_pt f x y pr02 = l -> derivable02_pt_lim f x y l.
Proof.
  intros.
  apply (derivable2_derive2_1 _ _ _ pr02).
  apply H.
Qed.
Lemma derivable02_derive02 : forall (f : R -> R -> R) (x y l : R) (pr02 : derivable02_pt f x y),
  prod (derive02_pt f x y pr02 = l -> derivable02_pt_lim f x y l)
    (derivable02_pt_lim f x y l -> derive02_pt f x y pr02 = l).
Proof.
  split.
  apply derivable02_derive02_1.
  apply derivable02_derive02_0.
Qed.

Lemma Corresp_d02 : forall f x y pr,
  derivable02_pt_lim f x y (derive02_pt f x y pr).
Proof.
  intros.
  apply (derivable02_derive02 _ _ _ _ pr).
  reflexivity.
Qed.
Lemma Corresp_d02_d01 : forall f x y pr1 pr2,
  derivable02_pt_lim f x y (derive01_pt (derive01 f pr1) x y pr2).
Proof.
  intros.
  assert (pr : derivable (fun y0 : R => f x y0)).
    intros y'.
    apply (pr1 x y').
  exists (derive _ pr) ; split.
  intros ; apply (derive_pt_eq_1 _ _ _ (pr x0)) ; reflexivity.
  apply (derivable_pt_lim_expr (fun y => derive01 f pr1 x y)).
    intros ; apply pr_nu.
  apply Corresp_d01.
Qed.
Lemma Corresp_d01_d02 : forall f x y pr1 pr2,
  derivable01_pt_lim (derive01 f pr1) x y
    (derive02_pt f x y pr2).
Proof.
  intros.
  assert (derivable01_pt (derive01 f pr1) x y).
    destruct pr2 as (l,(f',(pr,pr'))).
    exists l.
    apply (derivable_pt_lim_expr f').
      intros ; apply sym_equal, derivable01_derive01_0, pr.
    apply pr'.
  apply (derivable01_derive01 _ _ _ _ H).
  apply sym_equal, (derivable02_derive02 _ _ _ _ pr2).
  apply Corresp_d02_d01.
Qed.

Lemma derivable02_01_pt_lim :
  forall f' f x t l,
  (forall t, derivable01_pt_lim f x t (f' t)) ->
  derivable_pt_lim f' t l ->
  derivable02_pt_lim f x t l.
Proof.
  intros f' f x t l H H'.
  apply derivable2_pt_lim_derivable_pt_lim with (1 := H) (2 := H').
Qed.

(** * Continuity in R² *)

(** Definition *)

Definition continuity2_pt (f : R -> R -> R) (x y : R) :=
  forall eps : posreal, exists delta : posreal, forall (x' y' : R),
    Rabs (x'-x) < delta -> Rabs (y'-y) < delta -> Rabs (f x' y' - f x y) < eps.
Definition continuity2 (f : R -> R -> R) :=
  forall (x y : R), continuity2_pt f x y.

Lemma cont2_impl_cont_pt_0 : forall (f : R -> R -> R) x y,
  continuity2_pt f x y -> continuity_pt (fun x => f x y) x.
Proof.
  intros f x y Cf ;
  apply (equiv_cont_pt _ _).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  assert (Rabs (y-y) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  apply (Cf _ _ H H0).
Qed.
Lemma cont2_impl_cont_pt_1 : forall (f : R -> R -> R) x y,
  continuity2_pt f x y -> continuity_pt (fun y => f x y) y.
Proof.
  intros f x y Cf ;
  apply (equiv_cont_pt _ _).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  assert (Rabs (x-x) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  apply (Cf _ _ H0 H).
Qed.
Lemma cont2_impl_cont_pt : forall (f : R -> R -> R) x y,
  continuity2_pt f x y ->
    (continuity_pt (fun x => f x y) x /\
      continuity_pt (fun y => f x y) y).
Proof.
  split.
  apply cont2_impl_cont_pt_0 ; apply H.
  apply cont2_impl_cont_pt_1 ; apply H.
Qed.

Lemma cont2_impl_cont_0 : forall (f : R -> R -> R),
  continuity2 f -> forall y, continuity (fun x => f x y).
Proof.
  intros f Cf y x ; apply cont2_impl_cont_pt_0.
  apply Cf.
Qed.
Lemma cont2_impl_cont_1 : forall (f : R -> R -> R),
  continuity2 f -> forall x, continuity (fun y => f x y).
Proof.
  intros f Cf x y ;
  apply cont2_impl_cont_pt_1.
  apply Cf.
Qed.
Lemma cont2_impl_cont : forall (f : R -> R -> R),
  continuity2 f ->
    ((forall y, continuity (fun x => f x y)) /\
      (forall x, continuity (fun y => f x y))).
Proof.
  split.
  apply cont2_impl_cont_0 ; apply H.
  apply cont2_impl_cont_1 ; apply H.
Qed.

(** Uniform continuity *)

Definition unif_cont2_pave (f : R -> R -> R) (a b c d : R) :=
  forall eps : posreal, exists delta : posreal, forall (x y x' y' : R),
    a <= x <= b -> a <= x' <= b -> c <= y <= d -> c <= y' <= d ->
    Rabs (x'-x) < delta -> Rabs (y'-y) < delta -> Rabs (f x' y' - f x y) < eps.

Lemma unif_cont2_impl_cont2_pt : forall (f : R -> R -> R) (a b c d : R),
  unif_cont2_pave f a b c d ->
    (forall x y, a < x < b -> c < y < d -> continuity2_pt f x y).
Proof.
  intros.
  intros eps.
  elim (H eps) ; clear H ; intros d0 Cf.
  assert (0 < Rmin d0 (Rmin (Rmin (x-a) (b-x)) (Rmin (y-c) (d-y)))).
    apply Rmin_pos ; [apply d0 |
    apply Rmin_pos ; apply Rmin_pos ; apply Rlt_Rminus].
    apply H0. apply H0.
    apply H1. apply H1.
    set (delta := mkposreal _ H).
  exists delta ; intros.
  apply Cf.
  split ; apply Rlt_le ; apply H0.
  split.
    apply Ropp_le_cancel, (Rplus_le_reg_l x),
    (Rle_trans _ delta).
    rewrite Rplus_comm, <- (Ropp_involutive x), <- Ropp_plus_distr.
    apply (Rle_trans _ (Rabs (x'-x))) ;
    [apply Rabs_maj2 | apply Rlt_le, H2].
    apply (Rle_trans _ (Rmin (x - a) (b - x))).
    apply (Rle_trans _ (Rmin (Rmin (x - a) (b - x)) (Rmin (y - c) (d - y)))).
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_l.
    apply Rmin_l.
    apply (Rplus_le_reg_l (-x)) ; repeat rewrite (Rplus_comm (-x)) ; apply (Rle_trans _ delta).
    apply (Rle_trans _ (Rabs (x'-x))) ;
    [apply Rle_abs | apply Rlt_le, H2].
    apply (Rle_trans _ (Rmin (x - a) (b - x))).
    apply (Rle_trans _ (Rmin (Rmin (x - a) (b - x)) (Rmin (y - c) (d - y)))).
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_l.
    apply Rmin_r.
  split ; apply Rlt_le, H1.
  split.
    apply Ropp_le_cancel, (Rplus_le_reg_l y),
    (Rle_trans _ delta).
    rewrite Rplus_comm, <- (Ropp_involutive y), <- Ropp_plus_distr.
    apply (Rle_trans _ (Rabs (y'-y))) ;
    [apply Rabs_maj2 | apply Rlt_le, H3].
    apply (Rle_trans _ (Rmin (y - c) (d - y))).
    apply (Rle_trans _ (Rmin (Rmin (x - a) (b - x)) (Rmin (y - c) (d - y)))).
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_r.
    apply Rmin_l.
    apply (Rplus_le_reg_l (-y)) ; repeat rewrite (Rplus_comm (-y)) ; apply (Rle_trans _ delta).
    apply (Rle_trans _ (Rabs (y'-y))) ;
    [apply Rle_abs | apply Rlt_le, H3].
    apply (Rle_trans _ (Rmin (y - c) (d - y))).
    apply (Rle_trans _ (Rmin (Rmin (x - a) (b - x)) (Rmin (y - c) (d - y)))).
    unfold delta ; simpl ; apply Rmin_r.
    apply Rmin_r.
    apply Rmin_r.
  apply (Rlt_le_trans _ _ _ H2) ;
  unfold delta ; simpl ; apply Rmin_l.
  apply (Rlt_le_trans _ _ _ H3) ;
  unfold delta ; simpl ; apply Rmin_l.
Qed.
Lemma cont2_impl_unif_cont2 : forall (f : R -> R -> R),
  continuity2 f -> (forall a b c d, unif_cont2_pave f a b c d).
unfold continuity2, continuity2_pt, unif_cont2_pave.
intros f H a b c d eps.
specialize (H a c eps).
Admitted.

(** Basic functions and operations *)

Lemma continuity2_pt_expr_loc : forall f1 f2 x y (d : posreal)
  (Heq : forall x' y', Rabs (x'-x) < d -> Rabs (y'-y) < d -> f1 x' y' = f2 x' y'),
  continuity2_pt f1 x y -> continuity2_pt f2 x y.
Proof.
  intros.
  intro.
  elim (H eps) ; clear H ; intros d0 Cf.
  assert (0 < Rmin d d0).
    apply Rmin_pos ; [apply d | apply d0].
    set (delta := mkposreal _ H).
  exists delta ; intros.
  rewrite <- (Heq x y), <- (Heq x' y').
  apply Cf.
  apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply Rmin_r.
  apply (Rlt_le_trans _ _ _ H1) ; simpl ; apply Rmin_r.
  apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply Rmin_l.
  apply (Rlt_le_trans _ _ _ H1) ; simpl ; apply Rmin_l.
  rewrite Rminus_eq0, Rabs_R0 ; apply d.
  rewrite Rminus_eq0, Rabs_R0 ; apply d.
Qed.
Lemma continuity2_pt_expr : forall f1 f2 x y
  (Heq : forall x' y', f1 x' y' = f2 x' y'),
  continuity2_pt f1 x y -> continuity2_pt f2 x y.
Proof.
  intros f1 f2 x y Heq.
  apply (continuity2_pt_expr_loc f1 f2 _ _ (mkposreal _ Rlt_0_1)) ; simpl ; intros.
  apply Heq.
Qed.

Lemma continuity2_pt_const : forall a x y,
  continuity2_pt (Fct2_const a) x y.
Proof.
  intros a x y eps.
  exists eps ; intros.
  rewrite Rminus_eq0, Rabs_R0.
  apply eps.
Qed.
Lemma continuity2_pt_var1 : forall x y,
  continuity2_pt (Fct2_Var1) x y.
Proof.
  intros x y eps.
  exists eps ; intros.
  apply H.
Qed.
Lemma continuity2_pt_var2 : forall x y,
  continuity2_pt (Fct2_Var2) x y.
Proof.
  intros x y eps.
  exists eps ; intros.
  apply H0.
Qed.

Lemma continuity2_pt_proj1_0 : forall f x y,
  continuity_pt f x -> continuity2_pt (Fct2_proj1 f) x y.
Proof.
  intros f x y Df ; apply equiv_cont_pt in Df.
  intros eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  apply Df.
  apply H.
Qed.
Lemma continuity2_pt_proj1_1 : forall f x y,
  continuity2_pt (Fct2_proj1 f) x y -> continuity_pt f x.
Proof.
  intros f x y Cf.
  apply (equiv_cont_pt _ _).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  apply (Cf _ y).
  apply H.
  rewrite Rminus_eq0, Rabs_R0.
  apply delta.
Qed.
Lemma continuity2_pt_proj1 : forall f x y,
  continuity_pt f x <-> continuity2_pt (Fct2_proj1 f) x y.
Proof.
  split.
  apply continuity2_pt_proj1_0.
  apply continuity2_pt_proj1_1.
Qed.

Lemma continuity2_pt_proj2_0 : forall f x y,
  continuity_pt f y -> continuity2_pt (Fct2_proj2 f) x y.
Proof.
  intros f x y Df ; apply equiv_cont_pt in Df.
  intros eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  apply Df.
  apply H0.
Qed.
Lemma continuity2_pt_proj2_1 : forall f x y,
  continuity2_pt (Fct2_proj2 f) x y -> continuity_pt f y.
Proof.
  intros f x y Cf.
  apply (equiv_cont_pt _ _).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  apply (Cf x).
  rewrite Rminus_eq0, Rabs_R0.
  apply delta.
  apply H.
Qed.
Lemma continuity2_pt_proj2 : forall f x y,
  continuity_pt f y <-> continuity2_pt (Fct2_proj2 f) x y.
Proof.
  split.
  apply continuity2_pt_proj2_0.
  apply continuity2_pt_proj2_1.
Qed.

Lemma continuity2_pt_Rplus : forall x y,
  continuity2_pt Rplus x y.
Proof.
  intros x y eps.
  assert (0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (delta := mkposreal _ H).
  exists delta ; intros.
  apply (Rle_lt_trans _ (Rabs (x'-x) + Rabs (y'-y))).
    assert ((Rplus x' y' - Rplus x y) = (x' - x) + (y' - y)).
    ring.
  rewrite H2 ; clear H2 ; apply Rabs_triang.
  rewrite (double_var eps) ; apply Rplus_lt_compat ;
  [apply H0|apply H1].
Qed.
Lemma continuity2_pt_Rminus : forall x y,
  continuity2_pt Rminus x y.
Proof.
  intros x y eps.
  assert (0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (delta := mkposreal _ H).
  exists delta ; intros.
  apply (Rle_lt_trans _ (Rabs (x'-x) + Rabs (y'-y))).
    assert ((Rminus x' y' - Rminus x y) = (x' - x) + -(y' - y)).
    ring.
  rewrite H2, <- (Rabs_Ropp (y'-y)) ; clear H2 ; apply Rabs_triang.
  rewrite (double_var eps) ; apply Rplus_lt_compat ;
  [apply H0|apply H1].
Qed.
Lemma continuity2_pt_Rmult : forall x y,
  continuity2_pt Rmult x y.
Proof.
  intros x y eps.
  assert (0 < Rmin 1 (eps/(Rabs x + Rabs y + 1))).
    apply Rmin_pos ; [apply Rlt_0_1|apply Rdiv_lt_0_compat].
    apply eps.
    apply Rplus_le_lt_0_compat.
    apply Rplus_le_le_0_compat ; apply Rabs_pos.
    apply Rlt_0_1.
    set (delta := mkposreal _ H).
  exists delta ; intros.
  apply (Rle_lt_trans _ (Rabs (x'-x) * Rabs y' + Rabs x * Rabs (y'-y))).
  repeat rewrite <- Rabs_mult.
  assert ((Rmult x' y' - Rmult x y) =
    ((x' - x) * y') + (x * (y' - y))).
    ring.
  rewrite H2 ; clear H2 ; apply Rabs_triang.
  apply (Rlt_le_trans _ (delta * (Rabs y + 1) + Rabs x * delta)).
    apply Rplus_lt_le_compat.
    apply Rmult_le_0_lt_compat.
    apply Rabs_pos.
    apply Rabs_pos.
    apply H0.
    rewrite <- (Rplus_0_l (Rabs y')), <- (Rplus_opp_r (Rabs y)), Rplus_assoc.
    apply Rplus_lt_compat_l ; rewrite Rplus_comm.
    apply (Rle_lt_trans _ (Rabs (y'-y))).
    apply Rabs_triang_inv.
    apply (Rlt_le_trans _ delta _ H1).
    unfold delta ; simpl ; apply Rmin_l.
    apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Rlt_le, H1.
  unfold delta ; simpl ;
  apply (Rle_trans _ ((eps / (Rabs x + Rabs y + 1)) * (Rabs y + 1) + Rabs x * (eps / (Rabs x + Rabs y + 1)))).
  apply Rmin_case_strong ; intro H2.
  apply Rplus_le_compat.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat.
  apply Rabs_pos.
  apply Rle_0_1.
  apply H2.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply H2.
  apply Req_le ; reflexivity.
  apply Req_le ; field.
  apply sym_not_eq, Rlt_not_eq, Rplus_le_lt_0_compat.
  apply Rplus_le_le_0_compat ; apply Rabs_pos.
  apply Rlt_0_1.
Qed.

Lemma continuity2_pt_comp2 : forall f1 f2 f3 (x y : R),
  continuity2_pt f1 (f2 x y) (f3 x y) -> continuity2_pt f2 x y ->
  continuity2_pt f3 x y -> continuity2_pt (Fct2_comp2 f1 f2 f3) x y.
Proof.
  intros ; intro.
  elim (H eps) ; clear H ; intros d1 Cf1.
  elim (H0 d1) ; clear H0 ; intros d2 Cf2.
  elim (H1 d1) ; clear H1 ; intros d3 Cf3.
  assert (0 < Rmin d2 d3).
    apply Rmin_pos ; [apply d2|apply d3].
    set (delta := mkposreal _ H).
  exists delta ; intros.
  apply Cf1 ; [apply Cf2|apply Cf3].
  apply (Rlt_le_trans _ _ _ H0) ; unfold delta ; simpl ; apply Rmin_l.
  apply (Rlt_le_trans _ _ _ H1) ; unfold delta ; simpl ; apply Rmin_l.
  apply (Rlt_le_trans _ _ _ H0) ; unfold delta ; simpl ; apply Rmin_r.
  apply (Rlt_le_trans _ _ _ H1) ; unfold delta ; simpl ; apply Rmin_r.
Qed.
Lemma continuity2_pt_comp1 : forall (f1 : R -> R) (f2 : R -> R -> R) (x y : R),
  continuity_pt f1 (f2 x y) -> continuity2_pt f2 x y ->
  continuity2_pt (Fct2_comp1 f1 f2) x y.
Proof.
  intros f1 f2 x y Cf1 Cf2.
  apply (continuity2_pt_expr (Fct2_comp2 (Fct2_proj1 f1) f2 (Fct2_const 0))).
    intros ; unfold Fct2_comp2, Fct2_proj1, Fct2_const, Fct2_comp1 ;
    reflexivity.
  apply continuity2_pt_comp2.
  apply (continuity2_pt_proj1 _ _ _), Cf1.
  apply Cf2.
  apply continuity2_pt_const.
Qed.
Lemma continuity_pt_comp2 : forall f1 f2 f3 (x : R),
  continuity2_pt f1 (f2 x) (f3 x) -> continuity_pt f2 x ->
  continuity_pt f3 x -> continuity_pt (Fct_comp2 f1 f2 f3) x.
Proof.
  intros.
  apply (continuity2_pt_proj1 _ _ 0).
  apply (continuity2_pt_expr (Fct2_comp2 f1 (Fct2_proj1 f2) (Fct2_proj1 f3))) ;
    intros ;
    unfold Fct2_comp2, Fct_comp2, Fct2_proj1.
    reflexivity.
  apply continuity2_pt_comp2.
  apply H.
  apply (continuity2_pt_proj1 _ _ _), H0.
  apply (continuity2_pt_proj1 _ _ _), H1.
Qed.

Lemma continuity2_pt_opp : forall f x y,
  continuity2_pt f x y -> continuity2_pt (Fct2_opp f) x y.
Proof.
  intros.
  apply (continuity2_pt_comp1 Ropp f).
  apply continuity_pt_Ropp.
  apply H.
Qed.
Lemma continuity2_pt_plus : forall f1 f2 x y,
  continuity2_pt f1 x y -> continuity2_pt f2 x y ->
    continuity2_pt (Fct2_plus f1 f2) x y.
Proof.
  intros.
  apply (continuity2_pt_comp2 Rplus f1 f2).
  apply continuity2_pt_Rplus.
  apply H.
  apply H0.
Qed.
Lemma continuity2_pt_minus : forall f1 f2 x y,
  continuity2_pt f1 x y -> continuity2_pt f2 x y ->
    continuity2_pt (Fct2_minus f1 f2) x y.
Proof.
  intros.
  apply (continuity2_pt_comp2 Rminus f1 f2).
  apply continuity2_pt_Rminus.
  apply H.
  apply H0.
Qed.
Lemma continuity2_pt_mult : forall f1 f2 x y,
  continuity2_pt f1 x y -> continuity2_pt f2 x y ->
    continuity2_pt (Fct2_mult f1 f2) x y.
Proof.
  intros.
  apply (continuity2_pt_comp2 Rmult f1 f2).
  apply continuity2_pt_Rmult.
  apply H.
  apply H0.
Qed.

(** * Differentiability in R² *)

Definition differentiable_pt_lim (f : R -> R -> R) (x y : R) (l : R * R) :=
  forall eps : posreal, exists delta : posreal,
    forall x' y', Rabs (x'-x) < delta -> Rabs (y' - y) < delta ->
    Rabs (f x' y' - f x y - ((fst l) * (x' - x) + (snd l) * (y' - y))) <= eps * Rmax (Rabs (x'-x)) (Rabs (y'-y)).
Definition differentiable_pt (f : R -> R -> R) (x y : R) :=
  {l : R * R | differentiable_pt_lim f x y l}.
Definition differentiable (f : R -> R -> R) :=
  forall x y, differentiable_pt f x y.
Definition differentielle_pt (f : R -> R -> R) (x y : R)
  (pr : differentiable_pt f x y) := proj1_sig pr.
Definition differentielle (f : R -> R -> R) (pr : differentiable f) :=
  (fun x y => differentielle_pt f x y (pr x y)).

(** Differential and partial differential *)

Lemma differentiable_derivable10_pt_lim : forall (f : R -> R -> R) (x y : R)
  (l : R*R),
  differentiable_pt_lim f x y l -> derivable10_pt_lim f x y (fst l).
Proof.
  intros.
  apply (equiv_deriv_pt_lim _ _ _).
  intro.
  elim (H eps) ; clear H ; intros delta Df.
  exists delta ; intros.
  assert (Rabs (y-y) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  assert ((f y0 y - f x y - fst l * (y0 - x)) =
    (f y0 y - f x y - (fst l * (y0 - x) + snd l * (y - y)))).
    ring.
    rewrite H1 ; clear H1.
  assert (Rabs (y0 - x) = Rmax (Rabs (y0 - x)) (Rabs (y - y))).
    assert ((Rabs (y - y)) <= (Rabs (y0 - x))).
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos. 
    apply sym_equal ; rewrite Rmax_comm ; unfold Rmax ; case Rle_dec ; intuition.
    rewrite H1 ; clear H1.
  apply (Df _ _ H H0).
Qed.
Lemma differentiable_derivable10_pt : forall (f : R -> R -> R) (x y : R),
  differentiable_pt f x y -> derivable10_pt f x y.
Proof.
  intros f x y (l,Df).
  exists (fst l).
  apply differentiable_derivable10_pt_lim ; apply Df.
Qed.
Lemma differentielle_derive10_pt : forall (f : R -> R -> R) (x y : R) pr2 pr10,
  (fst (differentielle_pt f x y pr2)) = derive10_pt f x y pr10.
Proof.
  intros f x y (l2,Df2) (l10, Df10) ; simpl.
  apply (uniqueness_limite (fun x => f x y) x).
  apply differentiable_derivable10_pt_lim.
  apply Df2.
  apply Df10.
Qed.

Lemma differentiable_derivable01_pt_lim : forall (f : R -> R -> R) (x y : R)
  (l : R*R),
  differentiable_pt_lim f x y l -> derivable01_pt_lim f x y (snd l).
Proof.
  intros.
  apply (equiv_deriv_pt_lim _ _ _).
  intro.
  elim (H eps) ; clear H ; intros delta Df.
  exists delta ; intros.
  assert (Rabs (x-x) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  assert ((f x y0 - f x y - snd l * (y0 - y)) =
    (f x y0 - f x y - (fst l * (x - x) + snd l * (y0 - y)))).
    ring.
    rewrite H1 ; clear H1.
  assert (Rabs (y0 - y) = Rmax (Rabs (x - x)) (Rabs (y0 - y))).
    assert ((Rabs (x - x)) <= (Rabs (y0 - y))).
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.  
    apply sym_equal ; unfold Rmax ; case Rle_dec ; intuition.
    rewrite H1 ; clear H1.
  apply (Df _ _ H0 H).
Qed.
Lemma differentiable_derivable01_pt : forall (f : R -> R -> R) (x y : R),
  differentiable_pt f x y -> derivable01_pt f x y.
Proof.
  intros f x y (l,Df).
  exists (snd l).
  apply differentiable_derivable01_pt_lim ; apply Df.
Qed.
Lemma differentielle_derive01_pt : forall (f : R -> R -> R) (x y : R) pr2 pr01,
  (snd (differentielle_pt f x y pr2)) = derive01_pt f x y pr01.
Proof.
  intros f x y (l2,Df2) (l10, Df10) ; simpl.
  apply (uniqueness_limite (fun y => f x y) y).
  apply differentiable_derivable01_pt_lim.
  apply Df2.
  apply Df10.
Qed.

Lemma differentiable_derivable_pt_lim : forall (f : R -> R -> R) (x y : R)
  (l : R*R),
  differentiable_pt_lim f x y l -> (derivable10_pt_lim f x y (fst l) /\ derivable01_pt_lim f x y (snd l)).
Proof.
  split.
  apply differentiable_derivable10_pt_lim ; apply H.
  apply differentiable_derivable01_pt_lim ; apply H.
Qed.
Lemma differentiable_derivable_pt : forall (f : R -> R -> R) (x y : R),
  differentiable_pt f x y -> prod (derivable10_pt f x y) (derivable01_pt f x y).
Proof.
  split.
  apply differentiable_derivable10_pt ; apply H.
  apply differentiable_derivable01_pt ; apply H.
Qed.
Lemma differentielle_derive_pt : forall (f : R -> R -> R) (x y : R) pr2 pr10 pr01,
  differentielle_pt f x y pr2 = (derive10_pt f x y pr10, derive01_pt f x y pr01).
Proof.
  intros.
  apply injective_projections ; simpl.
  apply differentielle_derive10_pt.
  apply differentielle_derive01_pt.
Qed.

Lemma derivable_differentiable_pt_lim : forall f x y
  (pr1 : derivable10 f) (pr2 : derivable01 f),
  continuity2_pt (derive10 f pr1) x y -> continuity2_pt (derive01 f pr2) x y ->
  differentiable_pt_lim f x y (derive10 f pr1 x y,derive01 f pr2 x y).
Proof.
  intros.
  unfold continuity2_pt in H, H0 ;
  unfold derive10, derive01 in H, H0 ;
  unfold derive10, derive01 ;
  destruct (pr1 x y) as (l1,D10) ;
  destruct (pr2 x y) as (l2,D01) ;
  simpl in H, H0 ;
  simpl.
  apply equiv_deriv_pt_lim in D10.
  apply equiv_deriv_pt_lim in D01.
  intro ; simpl.
  assert (0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (eps' := mkposreal _ H1).
  elim (H eps') ; clear H ; intros d1 C10.
  elim (H0 eps') ; clear H0 ; intros d2 C01.
  assert (0 < Rmin d1 d2).
    apply Rmin_pos ; [apply d1|apply d2].
    set (delta := mkposreal _ H).
  exists delta ; intros.
  set (g1 t := f t y' - l1*t).
  set (g2 t := f x t - l2*t).
  apply (Rle_trans _ (Rabs (g1 x' - g1 x) + Rabs (g2 y' - g2 y))).
    assert ((f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y))) =
      (g1 x' - g1 x) + (g2 y' - g2 y)).
      unfold g1, g2 ; ring.
    rewrite H3 ; clear H3 ; apply Rabs_triang.
  apply (Rle_trans _ (eps' * Rabs (x'-x) + eps' * Rabs (y'-y))).
  apply Rplus_le_compat.

  assert (Dg1 : forall t, derivable_pt_lim g1 t (derive10_pt f t y' (pr1 t y') - l1)).
    intros ; unfold g1.
    apply derivable_pt_lim_minus.
    apply (derive_pt_eq_1 _ _ _ (pr1 t y')) ; reflexivity.
    rewrite <- (Rmult_1_r l1).
    apply (derivable_pt_lim_expr (fun t => l1*t)).
    intros ; ring.
    apply derivable_pt_lim_scal.
    apply derivable_pt_lim_id.
  assert (pr_g1 : derivable g1).
    intros t.
    exists (derive10_pt f t y' (pr1 t y') - l1).
    apply Dg1.
  set (MVT := Value_theorem g1 x x' pr_g1).
  destruct MVT as (c1,(Heq,Hc)).
  rewrite Heq.
  assert (derive g1 pr_g1 c1 = derive10_pt f c1 y' (pr1 c1 y') - l1).
  apply (uniqueness_limite g1 c1).
  apply (derive_pt_eq_1 _ _ _ (pr_g1 c1)) ; reflexivity.
  apply Dg1.
  rewrite H3 ; clear H3 ; rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply Rlt_le ; apply C10.
  apply (Rle_lt_trans _ (Rabs (x'-x))).
  revert Hc ; unfold Rmin, Rmax ;
  destruct (Rle_dec x x') ; intro Hc.
  repeat rewrite Rabs_right.
  unfold Rminus ; apply Rplus_le_compat_r, Hc.
  apply Rge_minus, Rle_ge, r.
  apply Rge_minus, Rle_ge, Hc.
  repeat rewrite Rabs_left1.
  unfold Rminus ;
  apply Ropp_le_contravar, Rplus_le_compat_r, Hc.
  apply Rle_minus, Rlt_le, Rnot_le_lt, n.
  apply Rle_minus, Hc.
  apply (Rlt_le_trans _ _ _ H0).
  unfold delta ; simpl ; apply Rmin_l.
  apply (Rlt_le_trans _ _ _ H2).
  unfold delta ; simpl ; apply Rmin_l.

  assert (Dg2 : forall t, derivable_pt_lim g2 t (derive01_pt f x t (pr2 x t) - l2)).
    intros ; unfold g2.
    apply derivable_pt_lim_minus.
    apply (derive_pt_eq_1 _ _ _ (pr2 x t)) ; reflexivity.
    rewrite <- (Rmult_1_r l2).
    apply (derivable_pt_lim_expr (fun t => l2*t)).
    intros ; ring.
    apply derivable_pt_lim_scal.
    apply derivable_pt_lim_id.
  assert (pr_g2 : derivable g2).
    intros t.
    exists (derive01_pt f x t (pr2 x t) - l2).
    apply Dg2.
  set (MVT := Value_theorem g2 y y' pr_g2).
  destruct MVT as (c2,(Heq,Hc)).
  rewrite Heq.
  assert (derive g2 pr_g2 c2 = derive01_pt f x c2 (pr2 x c2) - l2).
  apply (uniqueness_limite g2 c2).
  apply (derive_pt_eq_1 _ _ _ (pr_g2 c2)) ; reflexivity.
  apply Dg2.
  rewrite H3 ; clear H3 ; rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply Rlt_le ; apply C01.
  rewrite Rminus_eq0, Rabs_R0 ; apply d2.
  apply (Rle_lt_trans _ (Rabs (y'-y))).
  revert Hc ; unfold Rmin, Rmax ;
  destruct (Rle_dec y y') as [r | r] ; intro Hc.
  repeat rewrite Rabs_right.
  unfold Rminus ; apply Rplus_le_compat_r, Hc.
  apply Rge_minus, Rle_ge, r.
  apply Rge_minus, Rle_ge, Hc.
  repeat rewrite Rabs_left1.
  unfold Rminus ;
  apply Ropp_le_contravar, Rplus_le_compat_r, Hc.
  apply Rle_minus, Rlt_le, Rnot_le_lt, r.
  apply Rle_minus, Hc.
  apply (Rlt_le_trans _ _ _ H2).
  unfold delta ; simpl ; apply Rmin_r.
  rewrite <- (Rmult_plus_distr_l).
  assert (eps * Rmax (Rabs (x' - x)) (Rabs (y' - y)) =
    eps' * (2 * Rmax (Rabs (x' - x)) (Rabs (y' - y)))).
    unfold eps' ; simpl ; field.
    rewrite H3 ; clear H3 ; apply Rmult_le_compat_l.
  apply Rlt_le  ; apply eps'.
  apply Rplus_le_Rmax.
Qed.

(** Unicity *)

Lemma differentielle_unique : forall f x y l1 l2,
  differentiable_pt_lim f x y l1 -> differentiable_pt_lim f x y l2 -> l1 = l2.
Proof.
  intros.
  apply injective_projections.
  apply (uniqueness_limite (fun x => f x y) x) ;
  apply differentiable_derivable10_pt_lim.
  apply H.
  apply H0.
  apply (uniqueness_limite (fun y => f x y) y) ;
  apply differentiable_derivable01_pt_lim.
  apply H.
  apply H0.
Qed.

Lemma differentiable_differentielle_0 : forall f x y l pr,
  differentiable_pt_lim f x y l -> differentielle_pt f x y pr = l.
Proof.
  intros ;
  destruct pr as (l',Df) ;
  simpl.
  apply (differentielle_unique f x y).
  apply Df.
  apply H.
Qed.
Lemma differentiable_differentielle_1 : forall f x y l pr,
  differentielle_pt f x y pr = l -> differentiable_pt_lim f x y l.
Proof.
  intros ;
  destruct pr as (l',Df) ;
  simpl in H.
  rewrite <- H ; apply Df.
Qed.
Lemma differentiable_differentielle : forall f x y l pr,
  differentiable_pt_lim f x y l <-> differentielle_pt f x y pr = l.
Proof.
  split.
  apply differentiable_differentielle_0.
  apply differentiable_differentielle_1.
Qed.

(** Differentiability and continuity *)

Lemma differentiable_continuous_pt : forall f x y,
  differentiable_pt f x y -> continuity2_pt f x y.
Proof.
  intros f x y ((l1,l2),Df) eps ; simpl in Df.
  assert (0 < eps / 2).
    apply Rdiv_lt_0_compat ; [apply eps|apply Rlt_R0_R2].
    set (eps' := mkposreal _ H).
  elim (Df eps') ; clear Df ; intros d0 Df.
  assert (0 < Rmin (Rmin d0 1) (Rmin (eps/(4*Rmax (Rabs l1) 1)) (eps / (4* Rmax (Rabs l2) 1)))).
    apply Rmin_pos ; apply Rmin_pos.
    apply d0.
    apply Rlt_0_1.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    set (delta := mkposreal _ H0).
  exists delta ; intros.
  rewrite (double_var eps).
  apply (Rle_lt_trans _ (Rabs (f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y)))
    + Rabs (l1 * (x' - x) + l2 * (y' - y)))).
    assert (Rabs (f x' y' - f x y) =
      Rabs ((f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y))) +
      (l1 * (x' - x) + l2 * (y' - y)))).
      assert ((f x' y' - f x y) =
        (f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y)) +
        (l1 * (x' - x) + l2 * (y' - y)))).
        ring.
      rewrite <- H3 ; clear H3 ; reflexivity.
    rewrite H3 ; clear H3 ; apply Rabs_triang.
  apply Rplus_lt_le_compat.
  apply (Rle_lt_trans _ (eps' * Rmax (Rabs (x' - x)) (Rabs (y' - y)))).
  apply Df.
  apply (Rlt_le_trans _ _ _ H1) ; unfold delta ; simpl ;
  apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
  apply (Rlt_le_trans _ _ _ H2) ; unfold delta ; simpl ;
  apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
  rewrite <- (Rmult_1_r (eps/2)) ; unfold eps' ; simpl.
  apply Rmult_lt_compat_l.
  apply H.
  apply (Rlt_le_trans _ delta).
  apply (Rmax_lub_lt _ _ _ H1 H2).
  unfold delta ; simpl ;
  apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
  apply (Rle_trans _ (Rabs l1 * Rabs (x'-x) + Rabs l2 * Rabs (y'-y))).
    repeat rewrite <- Rabs_mult.
    apply Rabs_triang.
  rewrite (double_var (eps/2)).
  apply Rplus_le_compat.
  apply (Rle_trans _ (Rabs l1 * delta)).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, H1.
  apply (Rle_trans _ (Rabs l1 * (Rmin (eps / (4 * Rmax (Rabs l1) 1))
                     (eps / (4 * Rmax (Rabs l2) 1))))).
    apply Rmult_le_compat_l ; unfold delta ; simpl ; [apply Rabs_pos| apply Rmin_r].
  apply (Rle_trans _ (Rabs l1 * (eps / (4 * Rmax (Rabs l1) 1)))).
  apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rmin_l].
  unfold Rmax ; destruct (Rle_dec (Rabs l1) 1).
  rewrite <- (Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rlt_le, Rdiv_lt_0_compat ;
  [apply eps | apply Rmult_lt_0_compat ;
  [apply Rmult_lt_0_compat ; apply Rlt_R0_R2|apply Rlt_0_1]].
  apply r.
  apply Req_le ; field.
  apply Req_le ; field.
  apply Rnot_le_lt in n.
  apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 n).

  apply (Rle_trans _ (Rabs l2 * delta)).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, H2.
  apply (Rle_trans _ (Rabs l2 * (Rmin (eps / (4 * Rmax (Rabs l1) 1))
                     (eps / (4 * Rmax (Rabs l2) 1))))).
    apply Rmult_le_compat_l ; unfold delta ; simpl ; [apply Rabs_pos| apply Rmin_r].
  apply (Rle_trans _ (Rabs l2 * (eps / (4 * Rmax (Rabs l2) 1)))).
  apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rmin_r].
  unfold Rmax ; destruct (Rle_dec (Rabs l2) 1).
  rewrite <- (Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rlt_le, Rdiv_lt_0_compat ;
  [apply eps | apply Rmult_lt_0_compat ;
  [apply Rmult_lt_0_compat ; apply Rlt_R0_R2|apply Rlt_0_1]].
  apply r.
  apply Req_le ; field.
  apply Req_le ; field.
  apply Rnot_le_lt in n.
  apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 n).
Qed.

(** Basic operations and functions *)

Lemma differentiable_pt_lim_expr_loc : forall f1 f2 x y l (d : posreal)
  (Heq : forall x' y', Rabs (x'-x) < d -> Rabs (y' - y) < d -> f1 x' y' = f2 x' y'),
  differentiable_pt_lim f1 x y l -> differentiable_pt_lim f2 x y l.
Proof.
  intros ;
  intro eps.
  elim (H eps) ; clear H ; intros d0 Df.
  assert (0 < Rmin d d0).
    apply Rmin_pos ; [apply d | apply d0].
    set (delta := mkposreal _ H).
  exists delta ; intros.
  rewrite <- (Heq x' y'), <- (Heq x y).
  apply Df.
  apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply Rmin_r.
  apply (Rlt_le_trans _ _ _ H1) ; simpl ; apply Rmin_r.
  rewrite Rminus_eq0, Rabs_R0 ; apply d.
  rewrite Rminus_eq0, Rabs_R0 ; apply d.
  apply (Rlt_le_trans _ _ _ H0) ; simpl ; apply Rmin_l.
  apply (Rlt_le_trans _ _ _ H1) ; simpl ; apply Rmin_l.
Qed.
Lemma differentiable_pt_lim_expr : forall f1 f2 x y l
  (Heq : forall x' y', f1 x' y' = f2 x' y'),
  differentiable_pt_lim f1 x y l -> differentiable_pt_lim f2 x y l.
Proof.
  intros.
  apply (differentiable_pt_lim_expr_loc f1 _ _ _ _ (mkposreal _ Rlt_0_1)).
    simpl ; intros ; apply Heq.
  apply H.
Qed.
Lemma differentiable_pt_lim_const : forall a x y,
  differentiable_pt_lim (Fct2_const a) x y (0,0).
Proof.
  intros a x y eps ; simpl.
  exists eps ; intros.
  assert ((Fct2_const a x' y' - Fct2_const a x y - (0 * (x' - x) + 0 * (y' - y))) = 0).
    unfold Fct2_const ; ring.
    rewrite H1, Rabs_R0 ; clear H1.
  apply Rmult_le_pos.
  apply Rlt_le, eps.
  apply (Rle_trans _ (Rabs (x'-x))).
  apply Rabs_pos.
  apply RmaxLess1.
Qed.
Lemma differentiable_pt_lim_var1 : forall x y,
  differentiable_pt_lim Fct2_Var1 x y (1,0).
Proof.
  intros x y eps ; simpl.
  exists eps ; intros.
  assert (Fct2_Var1 x' y' - Fct2_Var1 x y - (1 * (x' - x) + 0 * (y' - y)) = 0).
    unfold Fct2_Var1 ; ring.
    rewrite H1, Rabs_R0 ; clear H1.
  apply Rmult_le_pos.
  apply Rlt_le, eps.
  apply (Rle_trans _ (Rabs (x'-x))).
  apply Rabs_pos.
  apply RmaxLess1.
Qed.
Lemma differentiable_pt_lim_var2 : forall x y,
  differentiable_pt_lim Fct2_Var2 x y (0,1).
Proof.
  intros x y eps ; simpl.
  exists eps ; intros.
  assert (Fct2_Var2 x' y' - Fct2_Var2 x y - (0 * (x' - x) + 1 * (y' - y)) = 0).
    unfold Fct2_Var2 ; ring.
    rewrite H1, Rabs_R0 ; clear H1.
  apply Rmult_le_pos.
  apply Rlt_le, eps.
  apply (Rle_trans _ (Rabs (x'-x))).
  apply Rabs_pos.
  apply RmaxLess1.
Qed.

Lemma differentiable_pt_lim_proj1_0 : forall f x y l,
  derivable_pt_lim f x l -> differentiable_pt_lim (Fct2_proj1 f) x y (l,0).
Proof.
  intros f x y l Df eps.
  apply equiv_deriv_pt_lim in Df ;
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl ; intros.
  assert (Fct2_proj1 f x' y' - Fct2_proj1 f x y - (l * (x' - x) + 0 * (y' - y))
    = f x' - f x - l * (x'-x)).
    unfold Fct2_proj1 ; ring.
  rewrite H1 ; clear H1.
  apply (Rle_trans _ (eps * Rabs (x'-x))).
  apply (Df _ H).
  apply Rmult_le_compat_l.
  apply Rlt_le, eps.
  apply RmaxLess1.
Qed.
Lemma differentiable_pt_lim_proj1_1 : forall f x y l,
  differentiable_pt_lim (Fct2_proj1 f) x y (l,0) -> derivable_pt_lim f x l.
Proof.
  intros f x y l Df.
  apply (equiv_deriv_pt_lim _ _ _) ; intro eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl in Df ; intros.
  assert (f y0 - f x - l * (y0 - x) =
    Fct2_proj1 f y0 y - Fct2_proj1 f x y - (l * (y0 - x) + 0 * (y - y))).
    unfold Fct2_proj1 ; ring.
  rewrite H0 ; clear H0.
  assert (Rabs (y0 - x) = Rmax (Rabs (y0 - x)) (Rabs (y-y))).
    assert ( (Rabs (y - y)) <= (Rabs (y0 - x)) ).
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.
    rewrite Rmax_comm ; apply sym_equal ; unfold Rmax ; case Rle_dec ; intuition.
  rewrite H0 ; clear H0.
  apply (Df _ _ H).
  rewrite Rminus_eq0, Rabs_R0 ; apply delta.
Qed.
Lemma differentiable_pt_lim_proj1 : forall f x y l,
  derivable_pt_lim f x l <-> differentiable_pt_lim (Fct2_proj1 f) x y (l,0).
Proof.
  split.
  apply differentiable_pt_lim_proj1_0.
  apply differentiable_pt_lim_proj1_1.
Qed.

Lemma differentiable_pt_lim_proj2_0 : forall f x y l,
  derivable_pt_lim f y l -> differentiable_pt_lim (Fct2_proj2 f) x y (0,l).
Proof.
  intros f x y l Df eps.
  apply equiv_deriv_pt_lim in Df ;
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl ; intros.
  assert (Fct2_proj2 f x' y' - Fct2_proj2 f x y - (0 * (x' - x) + l * (y' - y))
    = f y' - f y - l * (y'-y)).
    unfold Fct2_proj2 ; ring.
  rewrite H1 ; clear H1.
  apply (Rle_trans _ (eps * Rabs (y'-y))).
  apply (Df _ H0).
  apply Rmult_le_compat_l.
  apply Rlt_le, eps.
  apply RmaxLess2.
Qed.
Lemma differentiable_pt_lim_proj2_1 : forall f x y l,
  differentiable_pt_lim (Fct2_proj2 f) x y (0,l) -> derivable_pt_lim f y l.
Proof.
  intros f x y l Df.
  apply (equiv_deriv_pt_lim _ _ _) ; intro eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl in Df ; intros.
  assert (f y0 - f y - l * (y0 - y) =
    Fct2_proj2 f x y0 - Fct2_proj2 f x y - (0 * (x - x) + l * (y0 - y))).
    unfold Fct2_proj2 ; ring.
  rewrite H0 ; clear H0.
  assert (Rabs (y0 - y) = Rmax (Rabs (x - x)) (Rabs (y0-y))).
    assert ((Rabs (x - x)) <= (Rabs (y0 - y))).
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.
    apply sym_equal ; unfold Rmax ; case Rle_dec ; intuition.
  rewrite H0 ; clear H0.
  apply Df.
  rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  apply H.
Qed.
Lemma differentiable_pt_lim_proj2 : forall f x y l,
  derivable_pt_lim f y l <-> differentiable_pt_lim (Fct2_proj2 f) x y (0,l).
Proof.
  split.
  apply differentiable_pt_lim_proj2_0.
  apply differentiable_pt_lim_proj2_1.
Qed.

Lemma differentiable_pt_lim_Rplus : forall x y,
  differentiable_pt_lim Rplus x y (1,1).
Proof.
  intros x y eps ; simpl.
  exists eps ; intros.
  assert (Rplus x' y' - Rplus x y - (1 * (x' - x) + 1 * (y' - y)) = 0).
    ring.
    rewrite H1, Rabs_R0 ; clear H1.
  apply Rmult_le_pos.
  apply Rlt_le, eps.
  apply (Rle_trans _ (Rabs (x'-x))).
  apply Rabs_pos.
  apply RmaxLess1.
Qed.
Lemma differentiable_pt_lim_Rminus : forall x y,
  differentiable_pt_lim Rminus x y (1,-1).
Proof.
  intros x y eps ; simpl.
  exists eps ; intros.
  assert (Rminus x' y' - Rminus x y - (1 * (x' - x) + (-1) * (y' - y)) = 0).
    ring.
    rewrite H1, Rabs_R0 ; clear H1.
  apply Rmult_le_pos.
  apply Rlt_le, eps.
  apply (Rle_trans _ (Rabs (x'-x))).
  apply Rabs_pos.
  apply RmaxLess1.
Qed.
Lemma differentiable_pt_lim_Rmult : forall x y,
  differentiable_pt_lim Rmult x y (y,x).
Proof.
  intros x y eps ; simpl.
  exists eps ; intros.
  assert (Rmult x' y' - Rmult x y - (y * (x' - x) + x * (y' - y)) =
    (x'-x) * (y'-y)).
    ring.
    rewrite H1 ; clear H1.
  rewrite Rabs_mult.
  unfold Rmax ;
  destruct (Rle_dec (Rabs (x' - x)) (Rabs (y' - y))).
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply Rlt_le ; apply H.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply Rlt_le ; apply H0.
Qed.

Lemma differentiable_pt_lim_comp2 : forall f1 f2 f3 x y l1 l2 l3,
  differentiable_pt_lim f1 (f2 x y) (f3 x y) l1 ->
  differentiable_pt_lim f2 x y l2 -> differentiable_pt_lim f3 x y l3 ->
  differentiable_pt_lim (Fct2_comp2 f1 f2 f3) x y
    (fst l1 * fst l2 + snd l1 * fst l3, fst l1 * snd l2 + snd l1 * snd l3).
Proof.
  intros f1 f2 f3 x y (l1_1,l1_2) (l2_1,l2_2) (l3_1,l3_2)
    Df1 Df2 Df3 eps ; simpl.
  assert (Cf2 : continuity2_pt f2 x y).
    apply differentiable_continuous_pt.
    exists (l2_1,l2_2) ; apply Df2.
  assert (Cf3 : continuity2_pt f3 x y).
    apply differentiable_continuous_pt.
    exists (l3_1,l3_2) ; apply Df3.
  assert (He2 : 0 < eps / (4 * Rmax (Rabs l1_1) 1)).
    apply Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat].
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    set (eps2 := mkposreal _ He2).
  assert (He3 : 0 < eps / (4 * Rmax (Rabs l1_2) 1)).
    apply Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat].
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    set (eps3 := mkposreal _ He3).
  assert (He1 : 0 < eps / (2 * Rmax (eps2 + Rabs l2_1 + Rabs l2_2)
    (eps3 + Rabs l3_1 + Rabs l3_2))).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat].
    apply Rlt_R0_R2.
    apply (Rlt_le_trans _ (eps2 + Rabs l2_1 + Rabs l2_2)).
    rewrite Rplus_assoc ; apply Rplus_lt_le_0_compat.
    apply eps2.
    apply Rplus_le_le_0_compat ; apply Rabs_pos.
    apply RmaxLess1.
    set (eps1 := mkposreal _ He1).
  elim (Df1 eps1) ; clear Df1 ; intros d0 Df1.
    elim (Cf2 d0) ; clear Cf2 ; intros d1 Cf2.
    elim (Cf3 d0) ; clear Cf3 ; intros d'1 Cf3.
  elim (Df2 eps2) ; clear Df2 ; intros d2 Df2.
  elim (Df3 eps3) ; clear Df3 ; intros d3 Df3.
  assert (Hd : 0 < Rmin (Rmin d1 d'1) (Rmin d2 d3)).
    apply Rmin_pos ; apply Rmin_pos ;
    [apply d1 | apply d'1 | apply d2 | apply d3].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  apply (Rle_trans _ (Rabs (f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
    (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y)))
    + Rabs (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
    ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))))).
    assert ((Fct2_comp2 f1 f2 f3 x' y' - Fct2_comp2 f1 f2 f3 x y -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))) =
      (f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
      (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y))) +
      (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))).
      unfold Fct2_comp2 ; ring.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
  rewrite (double_var eps), (Rmult_plus_distr_r (eps/2)).
  apply Rplus_le_compat.
  apply (Rle_trans _ (eps1 * Rmax (Rabs (f2 x' y' - f2 x y)) (Rabs (f3 x' y' - f3 x y)))).
    apply Df1.
    apply Cf2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
    apply Cf3.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
  apply (Rle_trans _ (eps1 * (Rmax (eps2 + Rabs l2_1 + Rabs l2_2)
    (eps3 + Rabs l3_1 + Rabs l3_2) * Rmax (Rabs (x'-x)) (Rabs (y'-y))))).
    apply Rmult_le_compat_l.
    apply Rlt_le, eps1.
    rewrite Rmax_mult.
    apply Rmax_case_strong ; intros _ ; 
    [ apply Rle_trans with (2 := RmaxLess1 _ _) 
    | apply Rle_trans with (2 := RmaxLess2 _ _)].
    rewrite Rplus_assoc, Rmult_plus_distr_r.
    apply (Rle_trans _ (Rabs (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))
      + Rabs (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      assert (Rabs (f2 x' y' - f2 x y) =
      Rabs ((f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) +
      (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      assert ((f2 x' y' - f2 x y) =
      ((f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) +
      (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      ring.
      rewrite <- H1 ; clear H1 ; reflexivity.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
    apply Rplus_le_compat.
    apply Df2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    apply (Rle_trans _ (Rabs l2_1 * Rabs (x'-x) + Rabs l2_2 * Rabs (y'-y))).
      repeat rewrite <- Rabs_mult ; apply Rabs_triang.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat ; apply Rmult_le_compat_l.
      apply Rabs_pos.
      apply RmaxLess1.
      apply Rabs_pos.
      apply RmaxLess2.
  rewrite Rplus_assoc, Rmult_plus_distr_r.
  apply (Rle_trans _ (Rabs (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y)))
      + Rabs (l3_1 * (x' - x) + l3_2 * (y' - y)))).
      assert (Rabs (f3 x' y' - f3 x y) =
      Rabs ((f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) +
      (l3_1 * (x' - x) + l3_2 * (y' - y)))).
      assert ((f3 x' y' - f3 x y) =
      ((f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) +
      (l3_1 * (x' - x) + l3_2 * (y' - y)))).
      ring.
      rewrite <- H1 ; clear H1 ; reflexivity.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
    apply Rplus_le_compat.
    apply Df3.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    apply (Rle_trans _ (Rabs l3_1 * Rabs (x'-x) + Rabs l3_2 * Rabs (y'-y))).
      repeat rewrite <- Rabs_mult ; apply Rabs_triang.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat ; apply Rmult_le_compat_l.
      apply Rabs_pos.
      apply RmaxLess1.
      apply Rabs_pos.
      apply RmaxLess2.
  apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
  simpl ; apply Req_le ; field.
  apply sym_not_eq, Rlt_not_eq, (Rlt_le_trans _ (eps2 + Rabs l2_1 + Rabs l2_2)).
  rewrite Rplus_assoc ; apply Rplus_lt_le_0_compat.
  apply eps2.
  apply Rplus_le_le_0_compat ; apply Rabs_pos.
  apply RmaxLess1.
  rewrite (double_var (eps/2)), (Rmult_plus_distr_r (eps/2/2)).
  apply (Rle_trans _ (Rabs l1_1 * Rabs (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))
    + Rabs l1_2 * Rabs (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
    repeat rewrite <- Rabs_mult.
    assert ((l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))) =
      (l1_1 * (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))) +
      (l1_2 * (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
      ring.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
  apply Rplus_le_compat.
  apply (Rle_trans _ (Rabs l1_1 * (eps2 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
    apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Df2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
    apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
    unfold eps2, Rmax ; simpl ; destruct (Rle_dec (Rabs l1_1) 1).
    rewrite <- (Rmult_1_l (eps/2/2)) ; apply Rmult_le_compat.
    apply Rabs_pos.
    rewrite Rmult_1_r ; apply Rlt_le, Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat ; apply Rlt_R0_R2].
    apply r.
    apply Req_le ; field.
    apply Req_le ; field.
    apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 (Rnot_le_lt _ _ n)).
  apply (Rle_trans _ (Rabs l1_2 * (eps3 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
    apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Df3.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
    apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
    unfold eps3, Rmax ; simpl ; destruct (Rle_dec (Rabs l1_2) 1).
    rewrite <- (Rmult_1_l (eps/2/2)) ; apply Rmult_le_compat.
    apply Rabs_pos.
    rewrite Rmult_1_r ; apply Rlt_le, Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat ; apply Rlt_R0_R2].
    apply r.
    apply Req_le ; field.
    apply Req_le ; field.
    apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 (Rnot_le_lt _ _ n)).
Qed.
Lemma differentiable_pt_lim_comp1 : forall f1 f2 x y l1 l2,
  derivable_pt_lim f1 (f2 x y) l1 -> differentiable_pt_lim f2 x y l2
  -> differentiable_pt_lim (Fct2_comp1 f1 f2) x y (l1 * fst l2, l1 * snd l2).
Proof.
  intros.
  apply (differentiable_pt_lim_expr (Fct2_comp2 (Fct2_proj1 f1) f2 (Fct2_const 0))).
    intros ; unfold Fct2_comp2, Fct2_comp1, Fct2_proj1, Fct2_const ;
    reflexivity.
  assert ((l1 * fst l2, l1 * snd l2) = (fst (l1,0) * fst l2 + snd (l1,0) * fst (0,0),
    fst (l1,0) * snd l2 + snd (l1,0) * snd (0,0))).
    apply injective_projections ; simpl ; ring.
  rewrite H1 ; clear H1.
  apply differentiable_pt_lim_comp2.
  apply (differentiable_pt_lim_proj1 _ _ _ _), H.
  apply H0.
  apply differentiable_pt_lim_const.
Qed.
Lemma derivable_pt_lim_comp2 : forall f1 f2 f3 x l1 l2 l3,
  differentiable_pt_lim f1 (f2 x) (f3 x) l1 ->
  derivable_pt_lim f2 x l2 -> derivable_pt_lim f3 x l3 ->
  derivable_pt_lim (Fct_comp2 f1 f2 f3) x (fst l1 * l2 + snd l1 * l3).
Proof.
  intros.
  apply (differentiable_pt_lim_proj1 (Fct_comp2 f1 f2 f3) x 0 (fst l1 * l2 + snd l1 * l3)).
  apply (differentiable_pt_lim_expr (Fct2_comp2 f1 (Fct2_proj1 f2) (Fct2_proj1 f3))).
    intros ; unfold Fct2_comp2, Fct_comp2, Fct2_proj1 ; reflexivity.
  assert ((fst l1 * l2 + snd l1 * l3, 0) =
    (fst l1 * fst (l2,0) + snd l1 * fst (l3,0),
    fst l1 * snd (l2,0) + snd l1 * snd (l3,0))).
    apply injective_projections ; simpl ; ring.
  rewrite H2 ; clear H2.
  apply differentiable_pt_lim_comp2.
  apply H.
  apply (differentiable_pt_lim_proj1 _ _ _ _), H0.
  apply (differentiable_pt_lim_proj1 _ _ _ _), H1.
Qed.

Lemma differentiable_pt_lim_opp : forall f x y l,
  differentiable_pt_lim f x y l 
    -> differentiable_pt_lim (Fct2_opp f) x y (- fst l, - snd l).
Proof.
  intros f x y l Df.
  assert ((- fst l, - snd l) = (-1 * fst l, -1 * snd l)).
    apply injective_projections ; simpl ; ring.
  rewrite H ; clear H.
  apply (differentiable_pt_lim_comp1 Ropp).
  apply derivable_pt_lim_Ropp.
  apply Df.
Qed.
Lemma differentiable_pt_lim_plus : forall f1 f2 x y l1 l2,
  differentiable_pt_lim f1 x y l1 -> differentiable_pt_lim f2 x y l2
    -> differentiable_pt_lim (Fct2_plus f1 f2) x y (fst l1 + fst l2, snd l1 + snd l2).
Proof.
  intros f1 f2 x y l1 l2 Df1 Df2.
  assert ((fst l1 + fst l2, snd l1 + snd l2) =
    (fst (1, 1) * fst l1 + snd (1, 1) * fst l2,
    fst (1, 1) * snd l1 + snd (1, 1) * snd l2)).
    apply injective_projections ; simpl ; ring.
  rewrite H ; clear H.
  apply (differentiable_pt_lim_comp2 Rplus).
  apply differentiable_pt_lim_Rplus.
  apply Df1.
  apply Df2.
Qed.
Lemma differentiable_pt_lim_minus : forall f1 f2 x y l1 l2,
  differentiable_pt_lim f1 x y l1 -> differentiable_pt_lim f2 x y l2
    -> differentiable_pt_lim (Fct2_minus f1 f2) x y (fst l1 - fst l2, snd l1 - snd l2).
Proof.
  intros f1 f2 x y l1 l2 Df1 Df2.
  assert ((fst l1 - fst l2, snd l1 - snd l2) =
    (fst (1, -1) * fst l1 + snd (1, -1) * fst l2,
    fst (1, -1) * snd l1 + snd (1, -1) * snd l2)).
    apply injective_projections ; simpl ; ring.
  rewrite H ; clear H.
  apply (differentiable_pt_lim_comp2 Rminus).
  apply differentiable_pt_lim_Rminus.
  apply Df1.
  apply Df2.
Qed.
Lemma differentiable_pt_lim_mult : forall f1 f2 x y l1 l2,
  differentiable_pt_lim f1 x y l1 -> differentiable_pt_lim f2 x y l2
    -> differentiable_pt_lim (Fct2_mult f1 f2) x y 
    (f2 x y * fst l1 + f1 x y * fst l2, f2 x y * snd l1 + f1 x y * snd l2).
Proof.
  intros f1 f2 x y l1 l2 Df1 Df2.
  assert ((f2 x y * fst l1 + f1 x y * fst l2, f2 x y * snd l1 + f1 x y * snd l2) =
    (fst (f2 x y, f1 x y) * fst l1 + snd (f2 x y, f1 x y) * fst l2,
    fst (f2 x y, f1 x y) * snd l1 + snd (f2 x y, f1 x y) * snd l2)).
    apply injective_projections ; simpl ; ring.
  rewrite H ; clear H.
  apply (differentiable_pt_lim_comp2 Rmult).
  apply differentiable_pt_lim_Rmult.
  apply Df1.
  apply Df2.
Qed.

(** * Riemann integral *)

Definition Rint (f : R -> R) (pr : forall a b, Riemann_integrable f a b) (a b : R) : R :=
  RiemannInt (pr a b).

Lemma differentiable_pt_lim_Rint : forall (f : R -> R) (a b : R) pr,
  forall (Cf : continuity f), differentiable_pt_lim (Rint f pr) a b
    (- f a , f b).
Proof.
  intros.
  apply (differentiable_pt_lim_expr (Rint f (cont_impl_Rint f Cf))).
    intros ; unfold Rint ; apply RiemannInt_P5.
  assert ( forall a b, derivable10_pt_lim (Rint f (cont_impl_Rint f Cf)) a b (- f a)).
    intros ;
    apply (derivable_pt_lim_expr (fun x : R => - Rint f (cont_impl_Rint f Cf) b0 x)).
    intros ; apply sym_equal, RiemannInt_P8.
    apply derivable_pt_lim_opp.
    apply derivable_pt_lim_prim.
  assert (pr10 : derivable10 (Rint f (cont_impl_Rint f Cf))).
    intros a0 b0 ; exists (-f a0) ; apply H.
  assert (H10 : forall a b, - f a = derive10 _ pr10 a b).
    intros ; apply sym_equal, (derivable10_derive10 _ _ _ _ _), H.
  rewrite (H10 a b) ; clear H.
  assert ( forall a b, derivable01_pt_lim (Rint f (cont_impl_Rint f Cf)) a b (f b)).
    intros ;
    apply derivable_pt_lim_prim.
  assert (pr01 : derivable01 (Rint f (cont_impl_Rint f Cf))).
    intros a0 b0 ; exists (f b0) ; apply H.
  assert (H01 : forall a b, f b = derive01 _ pr01 a b).
    intros ; apply sym_equal, (derivable01_derive01 _ _ _ _ _), H.
  rewrite (H01 a b) ; clear H.

  apply derivable_differentiable_pt_lim.

  apply (continuity2_pt_expr (fun x y => - f x)).
  apply H10.
  apply (continuity2_pt_proj1 (fun x => - f x) _ _).
  apply continuity_pt_opp.
  apply Cf.

  apply (continuity2_pt_expr (fun x y => f y)).
  apply H01.
  apply (continuity2_pt_proj2 (fun y => f y) a b).
  apply Cf.
Qed.
Lemma differentiable_pt_Rint : forall (f : R -> R) (a b : R) pr,
  forall (Cf : continuity f), differentiable_pt (Rint f pr) a b.
Proof.
  intros ;
  exists (- f a, f b) ;
  apply differentiable_pt_lim_Rint ;
  apply Cf.
Qed.
Lemma differentielle_pt_Rint : forall (f : R -> R) (a b : R) pr pr',
  forall (Cf : continuity f), differentielle_pt (Rint f pr) a b pr'
    = (- f a , f b).
Proof.
  intros.
  apply (differentiable_differentielle (Rint f pr) a b (- f a,f b) pr').
  apply differentiable_pt_lim_Rint.
  apply Cf.
Qed.

(** * Parametric integral *)
Definition Param (f : R -> R -> R) (a b : R)
  (RIf : forall x, Riemann_integrable (fun t => f t x) a b) (x : R) :=
  RiemannInt (RIf x).

Lemma cont2_impl_Rint01 : forall (f : R -> R -> R),
  continuity2 f -> forall a b x, Riemann_integrable (fun t => f t x) a b.
Proof.
  intros.
  apply cont_impl_Rint.
  intros t.
  apply (cont2_impl_cont_pt f t x).
  apply H.
Qed.

Lemma derivable_pt_lim_param : forall f a b RIf x D01
  (Cdf : continuity2 (derive01 f D01)),
  derivable_pt_lim (Param f a b RIf) x
  (Param (derive01 f D01) a b (cont2_impl_Rint01 _ Cdf a b) x).
Proof.
  intros.
  apply (equiv_deriv_pt_lim _ _ _) ; intro.
  assert (UCf : unif_cont2_pave (derive01 f D01) (Rmin a b) (Rmax a b) (x-1) (x+1)).
    apply cont2_impl_unif_cont2.
    apply Cdf.
  assert (He : 0 < eps / Rmax (Rabs (b-a)) 1).
    apply Rdiv_lt_0_compat ;
    [apply eps | apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _))].
    set (eps' := mkposreal _ He).
  elim (UCf eps') ; clear UCf ; intros d0 UCf.
  assert (Hd : 0 < Rmin d0 1).
    apply Rmin_pos ; [apply d0 | apply Rlt_0_1].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  unfold Param.
  assert (Riemann_integrable (fun t => f t y - f t x - (derive01 f D01) t x * (y-x)) a b).
    apply Riemann_integrable_minus.
    apply Riemann_integrable_minus.
    apply RIf.
    apply RIf.
    apply (Riemann_integrable_expr (fun t => (y-x) * derive01 f D01 t x)).
    intros ; ring.
    apply Riemann_integrable_scal.
    apply (cont2_impl_Rint01 (derive01 f D01) Cdf a b x).
  assert (RiemannInt (RIf y) - RiemannInt (RIf x) -
    RiemannInt (cont2_impl_Rint01 (derive01 f D01) Cdf a b x) * (y - x)
    = RiemannInt X).
    rewrite Rmult_comm.
    rewrite <- (RiemannInt_scal _ _ _ _ _
      (Riemann_integrable_scal _ _ _ _ (cont2_impl_Rint01 (derive01 f D01) Cdf a b x))).
    rewrite <- (RiemannInt_minus _ _ _ _ (RIf y) (RIf x)
      (Riemann_integrable_minus _ _ _ _ (RIf y) (RIf x))).
    rewrite <- (RiemannInt_minus _ _ _ _ _ _
      (Riemann_integrable_minus _ _ _ _ (Riemann_integrable_minus (fun t : R => f t y) (fun t : R => f t x) a b
     (RIf y) (RIf x)) (Riemann_integrable_scal (fun t : R => derive01 f D01 t x) a b (y - x)
     (cont2_impl_Rint01 (derive01 f D01) Cdf a b x)))).
   apply RiemannInt_expr.
   intros ; ring.
   rewrite H0 ; clear H0.
  apply (Rle_trans _ ((eps' * Rabs (y-x)) * Rabs (b-a))).
  apply RiemannInt_Rabs_le_const.
  intros.
  set (g t := f x0 t - derive01 f D01 x0 x * t).
  assert (forall t, derivable_pt_lim g t (derive01 f D01 x0 t - derive01 f D01 x0 x)).
    unfold g ; intros.
    apply derivable_pt_lim_minus.
    apply (Corresp_d01 f x0 t).
    rewrite <- (Rmult_1_r (derive01 f D01 x0 x)).
    apply (derivable_pt_lim_expr (fun t => derive01 f D01 x0 x * t)).
      intros ; ring.
    apply (derivable_pt_lim_scal id (derive01 f D01 x0 x)).
    apply derivable_pt_lim_id.
  assert (derivable g).
    intros t.
    exists (derive01 f D01 x0 t - derive01 f D01 x0 x) ; apply H1.
  assert ((f x0 y - f x0 x - derive01 f D01 x0 x * (y - x)) = g y - g x).
    unfold g ; ring.
    rewrite H3 ; clear H3.
  set (MVT := Value_theorem g x y H2).
  destruct MVT as (c,(Heq,Hc)).
  rewrite Heq, Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  assert (derive g H2 c = derive01 f D01 x0 c - derive01 f D01 x0 x).
    apply (uniqueness_limite g c).
    apply (derive_pt_eq _ _ _ (H2 c)) ; reflexivity.
    apply H1.
  rewrite H3 ; clear H3.
  apply Rlt_le, UCf.
  apply H0.
  apply H0.
  split ; [apply (Rle_minus2 x x 1)|] ; apply Rlt_le, Rlt_plus_1.
  apply (Rabs_le_between' _ _ _).
  apply (Rle_trans _ (Rabs (y-x))).
  revert Hc ; unfold Rmin, Rmax ; destruct (Rle_dec x y) ; intros.
  repeat rewrite Rabs_right.
  unfold Rminus ; apply Rplus_le_compat_r, Hc.
  apply Rge_minus, Rle_ge, r.
  apply Rge_minus, Rle_ge, Hc.
  repeat rewrite Rabs_left1.
  unfold Rminus ; apply Ropp_le_contravar, Rplus_le_compat_r, Hc.
  apply Rle_minus, Rlt_le, Rnot_le_lt, n.
  apply Rle_minus, Hc.
  apply (Rle_trans _ _ _ (Rlt_le _ _ H)).
  simpl ; apply Rmin_r.
  rewrite Rminus_eq0, Rabs_R0 ; apply d0.
  apply (Rle_lt_trans _ (Rabs (y-x))).
  revert Hc ; unfold Rmin, Rmax ; destruct (Rle_dec x y) ; intros.
  repeat rewrite Rabs_right.
  unfold Rminus ; apply Rplus_le_compat_r, Hc.
  apply Rge_minus, Rle_ge, r.
  apply Rge_minus, Rle_ge, Hc.
  repeat rewrite Rabs_left1.
  unfold Rminus ; apply Ropp_le_contravar, Rplus_le_compat_r, Hc.
  apply Rle_minus, Rlt_le, Rnot_le_lt, n.
  apply Rle_minus, Hc.
  apply (Rlt_le_trans _ _ _ H).
  simpl ; apply Rmin_l.
  simpl ; unfold Rmax ; destruct (Rle_dec (Rabs (b-a)) 1).
  rewrite Rmult_assoc, (Rmult_comm (Rabs (y-x))), <- Rmult_assoc, <- Rdiv_1 ;
  apply Rmult_le_compat_r ; [apply Rabs_pos|].
  rewrite <- (Rmult_1_r eps) ; apply Rmult_le_compat.
  rewrite Rmult_1_r ; apply Rlt_le, eps.
  apply Rabs_pos.
  apply Req_le ; field.
  apply r.
  apply Req_le ; field.
  apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1), Rnot_le_lt, n.
Qed.