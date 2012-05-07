Require Import Reals.
Require Import Arithmetique.
Require Import Function1 Function2.
Require Import Partial_function.

Open Scope R_scope.

(** Partials functions with two variables have type : R -> R -> partial_val *)

(** * Extension and equality *)

Definition Pfun2_extension (f1 f2 : R -> R -> partial_val) :=
  forall x y, Pval_extension (f1 x y) (f2 x y).

Definition Pfun2_equal (f1 f2 : R -> R -> partial_val) :=
  forall x y, Pval_equal (f1 x y) (f2 x y).

(** Pfun2_extention is an order relation *)

Lemma Pfun2_equal_extension : forall f1 f2,
  Pfun2_equal f1 f2 -> Pfun2_extension f1 f2.
Proof.
  intros f1 f2 Heq x y.
  split ; intros.
  apply (Heq x y), X.
  apply (Heq x y).
Qed.

Lemma Pfun2_extension_reflexive : forall f, Pfun2_extension f f.
Proof.
  split.
  intros ;
  apply X.
  intros ;
  apply (pHeq (f x y)).
Qed.

Lemma Pfun2_extension_anti_symetrique : forall f1 f2,
  Pfun2_extension f1 f2 -> Pfun2_extension f2 f1 -> Pfun2_equal f1 f2.
Proof.
  intros.
  split ; [split|] ; intros.
  apply (X x y), X1.
  apply (X0 x y), X1.
  apply (X x y).
Qed.

Lemma Pfun2_extension_transitive : forall f1 f2 f3,
  Pfun2_extension f1 f2 -> Pfun2_extension f2 f3 -> Pfun2_extension f1 f3.
Proof.
  split ; intros.
  apply (X x y), (X0 x y), X1.
  rewrite <- ((snd (X0 x y)) (fst (X0 x y) d2)) ;
  apply (X x y).
Qed.

(** Pfun2_equal is an equivalence relation *)

Lemma Pfun2_equal_reflexive : forall f, Pfun2_equal f f.
Proof.
  split ; intros.
  split ; intros ; apply X.
  apply (pHeq (f x y)).
Qed.

Lemma Pfun2_equal_symetrique : forall f1 f2,
  Pfun2_equal f1 f2 -> Pfun2_equal f2 f1.
Proof.
  intros.
  split ; [split |] ; intros.
  apply (X x y), X0.
  apply (X x y), X0.
  apply sym_equal, (X x y).
Qed.

Lemma Pfun2_equal_transitive : forall f1 f2 f3,
  Pfun2_equal f1 f2 -> Pfun2_equal f2 f3 -> Pfun2_equal f1 f3.
Proof.
  intros.
  split ; [split|] ; intros.
  apply (X x y), (X0 x y), X1.
  apply (X0 x y), (X x y), X1.
  rewrite <- ((snd (X0 x y)) (fst (fst (X0 x y)) d2)) ;
  apply (X x y).
Qed.

(** * Basics functions *)

Definition Pfun2_fun (f : R -> R -> R) x y :=
  Pval_val (f x y).

Definition Pfun2_Pfun_v1 (f : R -> partial_val) (x y : R) :=
  Pval (pdom (f x)) (fun d => pval (f x) d) (fun d1 d2 => pHeq _ d1 d2).

Definition Pfun2_Pfun_v2 (f : R -> partial_val) (x y : R) :=
  Pval (pdom (f y)) (fun d => pval (f y) d) (fun d1 d2 => pHeq _ d1 d2).

Lemma Pfun2_app_Heq : forall (f : R -> R -> partial_val) (x y : partial_val),
  forall (d1 d2 : {dx : pdom x & {dy : pdom y & pdom (f (pval x dx) (pval y dy))}}),
    pval (f (pval x (projT1 d1)) (pval y (projT1 (projT2 d1)))) (projT2 (projT2 d1)) =
    pval (f (pval x (projT1 d2)) (pval y (projT1 (projT2 d2)))) (projT2 (projT2 d2)).
Proof.
  intros f x y (d1x,(d1y,d1)) (d2x,(d2y,d2)) ; simpl.
  revert d1.
  rewrite (pHeq x d1x d2x).
  rewrite (pHeq y d1y d2y).
  intros ; apply pHeq.
Qed.
Definition Pfun2_app (f : R -> R -> partial_val) (x y : partial_val) : partial_val :=
  Pval {dx : pdom x & {dy : pdom y & pdom (f (pval x dx) (pval y dy))}} 
    (fun d => pval (f (pval x (projT1 d)) (pval y (projT1 (projT2 d)))) (projT2 (projT2 d)))
    (Pfun2_app_Heq f x y).

(** * Continuity *)

Definition Pfun2_continuity_pt (f : R -> R -> partial_val) x y :=
  { pr_x : pdom (f x y) |
    forall eps : posreal, exists delta : posreal,
    forall (x' y' : R), (Rabs (x'-x)) < delta -> (Rabs (y'-y)) < delta ->
    exists pr_y : pdom (f x' y'),
    Rabs (pval _ pr_y - pval _ pr_x) < eps }.

Definition Pfun2_continuity (f : R -> R -> partial_val) :=
  forall x y, Pfun2_continuity_pt f x y.

(** Prolongement and equality *)

Lemma Pfun2_continuity_pt_extension : forall (f1 f2 : R -> R -> partial_val) x y,
  Pfun2_extension f1 f2 -> Pfun2_continuity_pt f2 x y -> Pfun2_continuity_pt f1 x y.
Proof.
  intros f1 f2 x y Hext (pr_x,Cf2).
  destruct (Hext x y) as (dom12,Heq12).
  exists (dom12 pr_x) ; intros.
  elim (Cf2 eps) ; clear Cf2 ; intros delta Cf2.
  exists delta ; intros.
  elim (Cf2 x' y' H H0) ; clear Cf2 ; intros pr_y Cf2.
  destruct (Hext x' y') as (dom'12,Heq'12).
  exists (dom'12 pr_y) ; intros.
  rewrite (Heq12 _ pr_x) ;
  rewrite (Heq'12 _ pr_y).
  apply Cf2.
Qed.

Lemma Pfun2_continuity_pt_eq : forall (f1 f2 : R -> R -> partial_val) x y,
  Pfun2_equal f1 f2 -> Pfun2_continuity_pt f2 x y -> Pfun2_continuity_pt f1 x y.
Proof.
  intros.
  apply (Pfun2_continuity_pt_extension f1 f2).
  apply Pfun2_equal_extension.
  apply X.
  apply X0.
Qed.

(** Basic functions *)

Lemma Pfun2_continuity_pt_fun_0 : forall (f : R -> R -> R) x y,
  continuity2_pt f x y -> Pfun2_continuity_pt (Pfun2_fun f) x y.
Proof.
  intros.
  exists I ; intros.
  elim (H eps) ; clear H ; intros delta Cf.
  exists delta ; intros.
  exists I.
  apply (Cf _ _ H H0).
Qed.
Lemma Pfun2_continuity_pt_fun_1 : forall (f : R -> R -> R) x y,
  Pfun2_continuity_pt (Pfun2_fun f) x y -> continuity2_pt f x y.
Proof.
  intros f x y (pr_x,Cf) eps.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  elim (Cf _ _ H H0) ; clear Cf ; intros pr_y Cf.
  apply Cf.
Qed.
Lemma Pfun2_continuity_pt_fun : forall (f : R -> R -> R) x y,
  prod (continuity2_pt f x y -> Pfun2_continuity_pt (Pfun2_fun f) x y)
    (Pfun2_continuity_pt (Pfun2_fun f) x y -> continuity2_pt f x y).
Proof.
  split.
  apply Pfun2_continuity_pt_fun_0.
  apply Pfun2_continuity_pt_fun_1.
Qed.

Lemma Pfun2_continuity_pt_Pfun_v1_0 : forall (f : R -> partial_val) x y,
  Pfun_continuity_pt f x -> Pfun2_continuity_pt (Pfun2_Pfun_v1 f) x y.
Proof.
  intros f x y (pr_x,Cf).
  exists pr_x ; intros.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  elim (Cf _ H) ; clear Cf ; intros pr_y Cf.
  exists pr_y.
  apply Cf.
Qed.
Lemma Pfun2_continuity_pt_Pfun_v1_1 : forall (f : R -> partial_val) x y,
  Pfun2_continuity_pt (Pfun2_Pfun_v1 f) x y -> Pfun_continuity_pt f x.
Proof.
  intros f x y (pr_x,Cf).
  exists pr_x ; intros.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  assert (Rabs (y-y) < delta).
    rewrite Rminus_eq0, Rabs_R0.
    apply delta.
  elim (Cf _ _ H H0) ; clear Cf ; intros pr_y Cf.
  exists pr_y.
  apply Cf.
Qed.
Lemma Pfun2_continuity_pt_Pfun_v1 : forall (f : R -> partial_val) x y,
  prod (Pfun_continuity_pt f x -> Pfun2_continuity_pt (Pfun2_Pfun_v1 f) x y)
  (Pfun2_continuity_pt (Pfun2_Pfun_v1 f) x y -> Pfun_continuity_pt f x).
Proof.
  split.
  apply Pfun2_continuity_pt_Pfun_v1_0.
  apply Pfun2_continuity_pt_Pfun_v1_1.
Qed.

Lemma Pfun2_continuity_pt_Pfun_v2_0 : forall (f : R -> partial_val) x y,
  Pfun_continuity_pt f y -> Pfun2_continuity_pt (Pfun2_Pfun_v2 f) x y.
Proof.
  intros f x y (pr_x,Cf).
  exists pr_x ; intros.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  elim (Cf _ H0) ; clear Cf ; intros pr_y Cf.
  exists pr_y.
  apply Cf.
Qed.
Lemma Pfun2_continuity_pt_Pfun_v2_1 : forall (f : R -> partial_val) x y,
  Pfun2_continuity_pt (Pfun2_Pfun_v2 f) x y -> Pfun_continuity_pt f y.
Proof.
  intros f x y (pr_x,Cf).
  exists pr_x ; intros.
  elim (Cf eps) ; clear Cf ; intros delta Cf.
  exists delta ; intros.
  assert (Rabs (x-x) < delta).
    rewrite Rminus_eq0, Rabs_R0.
    apply delta.
  elim (Cf _ _ H0 H) ; clear Cf ; intros pr_y Cf.
  exists pr_y.
  apply Cf.
Qed.
Lemma Pfun2_continuity_pt_Pfun_v2 : forall (f : R -> partial_val) x y,
  prod (Pfun_continuity_pt f y -> Pfun2_continuity_pt (Pfun2_Pfun_v2 f) x y)
  (Pfun2_continuity_pt (Pfun2_Pfun_v2 f) x y -> Pfun_continuity_pt f y).
Proof.
  split.
  apply Pfun2_continuity_pt_Pfun_v2_0.
  apply Pfun2_continuity_pt_Pfun_v2_1.
Qed.

(** Compositions *)

Lemma Pfun2_continuity_pt_comp2 : forall (f1 f2 f3 : R -> R -> partial_val) x y,
  Pfun2_continuity_pt f2 x y -> Pfun2_continuity_pt f3 x y ->
  (forall d2 d3, Pfun2_continuity_pt f1 (pval (f2 x y) d2) (pval (f3 x y) d3)) ->
    Pfun2_continuity_pt (fun x y => Pfun2_app f1 (f2 x y) (f3 x y)) x y.
Proof.
  intros f1 f2 f3 x y (pr2_x,Cf2) (pr3_x,Cf3) Cf1.
  elim (Cf1 pr2_x pr3_x) ; clear Cf1 ; intros pr1_x Cf1.
  assert (pr_x : {dx : pdom (f2 x y) & 
  {dy : pdom (f3 x y) &  pdom (f1 (pval (f2 x y) dx) (pval (f3 x y) dy))}}).
    exists pr2_x ; exists pr3_x ; apply pr1_x.
  exists pr_x ; intros.
  elim (Cf1 eps) ; clear Cf1 ; intros d1 Cf1.
  elim (Cf2 d1) ; clear Cf2 ; intros d2 Cf2.
  elim (Cf3 d1) ; clear Cf3 ; intros d3 Cf3.
  assert (Hd : 0 < Rmin d2 d3).
    apply Rmin_pos ; [apply d2 | apply d3].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (x'-x) < d2).
    apply (Rlt_le_trans _ _ _ H) ; unfold delta ; simpl ; apply Rmin_l.
  assert (Rabs (y'-y) < d2).
    apply (Rlt_le_trans _ _ _ H0) ; unfold delta ; simpl ; apply Rmin_l.
  elim (Cf2 _ _ H1 H2) ; clear H1 H2 Cf2 ; intros pr2_y Cf2.
  assert (Rabs (x'-x) < d3).
    apply (Rlt_le_trans _ _ _ H) ; unfold delta ; simpl ; apply Rmin_r.
  assert (Rabs (y'-y) < d3).
    apply (Rlt_le_trans _ _ _ H0) ; unfold delta ; simpl ; apply Rmin_r.
  elim (Cf3 _ _ H1 H2) ; clear H1 H2 Cf3 ; intros pr3_y Cf3.
  elim (Cf1 _ _ Cf2 Cf3) ; clear Cf1 ; intros pr1_y Cf1.
  assert (pr_y : {dx : pdom (f2 x' y') & 
         {dy : pdom (f3 x' y') & 
         pdom (f1 (pval (f2 x' y') dx) (pval (f3 x' y') dy))}}).
    exists pr2_y ; exists pr3_y ; apply pr1_y.
  exists pr_y.
  assert (pval (Pfun2_app f1 (f2 x y) (f3 x y)) pr_x = 
    pval (f1 (pval (f2 x y) pr2_x) (pval (f3 x y) pr3_x)) pr1_x).
    destruct pr_x as (pr2,(pr3,pr1)) ; simpl.
    revert pr1 ; rewrite (pHeq _ pr2 pr2_x), (pHeq _ pr3 pr3_x) ; intros ; apply pHeq.
    rewrite H1 ; clear H1.
  assert (pval (Pfun2_app f1 (f2 x' y') (f3 x' y')) pr_y = 
    pval (f1 (pval (f2 x' y') pr2_y) (pval (f3 x' y') pr3_y)) pr1_y).
    destruct pr_y as (pr2,(pr3,pr1)) ; simpl.
    revert pr1 ; rewrite (pHeq _ pr2 pr2_y), (pHeq _ pr3 pr3_y) ; intros ; apply pHeq.
    rewrite H1 ; clear H1.
  apply Cf1.
Qed.

Lemma Pfun2_continuity_pt_comp1 : forall (f1 : R -> partial_val) (f2 : R -> R -> partial_val) x y,
  Pfun2_continuity_pt f2 x y ->
    (forall d, Pfun_continuity_pt f1 (pval (f2 x y) d)) ->
      Pfun2_continuity_pt (fun x y => Pfun_app f1 (f2 x y)) x y.
Proof.
  intros f1 f2 x y Cf2 Cf1.
  apply (Pfun2_continuity_pt_extension _ (fun x y => Pfun2_app (Pfun2_Pfun_v1 f1) (f2 x y) (Pval_val 0))).
  split ; simpl.
  intros (d2,(_,d1)) ;
  exists d2 ; apply d1.
  intros (d2,d1) (d'2,(t,d'1)) ; simpl.
  revert d1 ; rewrite (pHeq _ d2 d'2) ; intros ; apply pHeq.
  apply Pfun2_continuity_pt_comp2.
  apply Cf2.
  apply (Pfun2_continuity_pt_Pfun_v1 (fun _ => Pval_val 0) x y), Pfun_continuity_pt_const.
  intros ; apply (Pfun2_continuity_pt_Pfun_v1 f1 _ _), Cf1.
Qed.

Lemma Pfun_continuity_pt_comp2 : forall (f1 : R -> R -> partial_val) (f2 f3 : R -> partial_val) x,
  Pfun_continuity_pt f2 x -> Pfun_continuity_pt f3 x ->
  (forall d2 d3, Pfun2_continuity_pt f1 (pval (f2 x) d2) (pval (f3 x) d3)) ->
    Pfun_continuity_pt (fun x => Pfun2_app f1 (f2 x) (f3 x)) x.
Proof.
  intros f1 f2 f3 x Cf2 Cf3 Cf1.
  apply (Pfun2_continuity_pt_Pfun_v1 _ x 0).
  apply (Pfun2_continuity_pt_extension _ (fun x y => Pfun2_app f1 (Pfun2_Pfun_v1 f2 x 0) (Pfun2_Pfun_v1 f3 x 0))).
  split ; simpl ; auto.
  intros (d1x,(d1y,d1)) (d2x,(d2y,d2)) ; simpl.
  revert d1 ; rewrite (pHeq _ d1x d2x), (pHeq _ d1y d2y) ; intros ; apply pHeq.
  apply Pfun2_continuity_pt_comp2.
  apply Pfun2_continuity_pt_Pfun_v1_0, Cf2.
  apply Pfun2_continuity_pt_Pfun_v1_0, Cf3.
  simpl ; apply Cf1.
Qed.

(** * Partial derivative *)

Definition Pfun2_derivable10_pt_lim (f : R -> R -> partial_val) (x y l : R) :=
  Pfun_derivable_pt_lim (fun x => f x y) x l.
Definition Pfun2_derivable01_pt_lim (f : R -> R -> partial_val) (x y l : R) :=
  Pfun_derivable_pt_lim (fun y => f x y) y l.

Definition Pfun2_derivable10_pt (f : R -> R -> partial_val) (x y : R) :=
  Pfun_derivable_pt (fun x => f x y) x.
Definition Pfun2_derivable01_pt (f : R -> R -> partial_val) (x y : R) :=
  Pfun_derivable_pt (fun y => f x y) y.

Definition Pfun2_derive10_pt (f : R -> R -> partial_val) (x y : R) (pr : Pfun2_derivable10_pt f x y) :=
  Pfun_derive_pt (fun x => f x y) x pr.
Definition Pfun2_derive01_pt (f : R -> R -> partial_val) (x y : R) (pr : Pfun2_derivable01_pt f x y) :=
  Pfun_derive_pt (fun y => f x y) y pr.

Definition Pfun2_derivable10 (f : R -> R -> partial_val) :=
  forall x y, pdom (f x y) -> Pfun2_derivable10_pt f x y.
Definition Pfun2_derivable01 (f : R -> R -> partial_val) :=
  forall x y, pdom (f x y) -> Pfun2_derivable10_pt f x y.

Lemma Pfun2_derive10_Heq : forall f x y (d1 d2 : Pfun2_derivable10_pt f x y),
  Pfun2_derive10_pt f x y d1 = Pfun2_derive10_pt f x y d2.
Proof.
  intros.
  apply Pfun_derive_Heq.
Qed.
Definition Pfun2_derive10 (f : R -> R -> partial_val) (x y : R) : partial_val :=
  Pval (Pfun2_derivable10_pt f x y) (fun d => Pfun2_derive10_pt f x y d) (Pfun2_derive10_Heq f x y).

Lemma Pfun2_derive01_Heq : forall f x y (d1 d2 : Pfun2_derivable01_pt f x y),
  Pfun2_derive01_pt f x y d1 = Pfun2_derive01_pt f x y d2.
Proof.
  intros.
  apply Pfun_derive_Heq.
Qed.
Definition Pfun2_derive01 (f : R -> R -> partial_val) (x y : R) : partial_val :=
  Pval (Pfun2_derivable01_pt f x y) (fun d => Pfun2_derive01_pt f x y d) (Pfun2_derive01_Heq f x y).

(** * Differentiability *)

Definition Pfun2_differentiable_pt_lim f x y l :=
  { pr_x : pdom (f x y) |
    forall eps : posreal, exists delta : posreal,
    forall (x' y' : R), (Rabs (x'-x)) < delta -> (Rabs (y'-y)) < delta ->
    exists pr_y : pdom (f x' y'),
    Rabs (pval _ pr_y - pval _ pr_x - (fst l * (x' - x) + snd l * (y' - y))) <= eps * Rmax (Rabs (x' - x)) (Rabs (y' - y)) }.

Lemma Pfun2_differentiable_derivable10_pt_lim : forall f x y l,
  Pfun2_differentiable_pt_lim f x y l -> Pfun2_derivable10_pt_lim f x y (fst l).
Proof.
  intros f x y (l1,l2) (pr_x,Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros x' H.
  assert (Rabs (y-y) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  elim (Df _ _ H H0) ; clear Df ; intros pr_y Df.
  exists pr_y.
  replace (pval _ pr_y - pval _ pr_x - fst (l1, l2) * (x' - x))
    with (pval _ pr_y - pval _ pr_x - (fst (l1, l2) * (x' - x) + snd (l1, l2) * (y - y))) by ring.
  assert (Rabs (x' - x) = Rmax (Rabs (x' - x)) (Rabs (y - y))).
    apply sym_equal ; rewrite Rmax_comm ; apply Rmax_eq_l.
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.
    rewrite H1 ; clear H1.
  apply Df.
Qed.

Lemma Pfun2_differentiable_derivable01_pt_lim : forall f x y l,
  Pfun2_differentiable_pt_lim f x y l -> Pfun2_derivable01_pt_lim f x y (snd l).
Proof.
  intros f x y (l1,l2) (pr_x,Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros y' H0.
  assert (Rabs (x-x) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  elim (Df _ _ H H0) ; clear Df ; intros pr_y Df.
  exists pr_y.
  replace (pval _ pr_y - pval _ pr_x - snd (l1, l2) * (y' - y))
    with (pval _ pr_y - pval _ pr_x - (fst (l1, l2) * (x - x) + snd (l1, l2) * (y' - y))) by ring.
  assert (Rabs (y' - y) = Rmax (Rabs (x - x)) (Rabs (y' - y))).
    apply sym_equal, Rmax_eq_l.
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.
    rewrite H1 ; clear H1.
  apply Df.
Qed.

Lemma Pfun2_differentiable_derivable_pt_lim : forall f x y l,
  Pfun2_differentiable_pt_lim f x y l ->
  prod (Pfun_derivable_pt_lim (fun x => f x y) x (fst l)) (Pfun_derivable_pt_lim (f x) y (snd l)).
Proof.
  split.
  apply Pfun2_differentiable_derivable10_pt_lim ; apply X.
  apply Pfun2_differentiable_derivable01_pt_lim ; apply X.
Qed.

Lemma Pfun2_differential_unique :
  forall f x y l1 l2,
    Pfun2_differentiable_pt_lim f x y l1 -> Pfun2_differentiable_pt_lim f x y l2 -> l1 = l2.
Proof.
  intros.
  apply injective_projections.
  apply Pfun_derive_unique with (fun x => f x y) x ;
  apply (Pfun2_differentiable_derivable_pt_lim _ _ _ _) ; [apply X | apply X0].
  apply Pfun_derive_unique with (f x) y ;
  apply (Pfun2_differentiable_derivable_pt_lim _ _ _ _) ; [apply X | apply X0].
Qed.

Definition Pfun2_differentiable_pt f x y :=
  {l : R*R & Pfun2_differentiable_pt_lim f x y l}.

Definition Pfun2_differential_pt (f : R -> R -> partial_val) (x y : R) (pr : Pfun2_differentiable_pt f x y) :=
  projT1 pr.

Definition Pfun2_differentiable (f : R -> R -> partial_val) :=
  forall x y, Pfun2_differentiable_pt f x y.

Lemma Pfun2_differential1_Heq :
  forall f x y d1 d2,
  fst (Pfun2_differential_pt f x y d1) = fst (Pfun2_differential_pt f x y d2).
Proof.
  destruct d1 as (l1,d1).
  destruct d2 as (l2,d2).
  simpl.
  apply f_equal.
  apply (Pfun2_differential_unique f x y).
  apply d1.
  apply d2.
Qed.

Lemma Pfun2_differential2_Heq :
  forall f x y d1 d2,
  snd (Pfun2_differential_pt f x y d1) = snd (Pfun2_differential_pt f x y d2).
Proof.
  destruct d1 as (l1,d1).
  destruct d2 as (l2,d2).
  simpl.
  apply f_equal.
  apply (Pfun2_differential_unique f x y).
  apply d1.
  apply d2.
Qed.

Definition Pfun2_differential f x y :=
  (Pval (Pfun2_differentiable_pt f x y) (fun pr => fst (Pfun2_differential_pt f x y pr))
    (Pfun2_differential1_Heq f x y),
   Pval (Pfun2_differentiable_pt f x y) (fun pr => snd (Pfun2_differential_pt f x y pr))
    (Pfun2_differential2_Heq f x y)).

Lemma Pfun2_differentiable_differential_0 : forall f x y l pr,
  Pfun2_differentiable_pt_lim f x y l -> Pfun2_differential_pt f x y pr = l.
Proof.
  intros f x y l (l',H1) H2.
  now apply (Pfun2_differential_unique f x y).
Qed.

Lemma Pfun2_differentiable_differential_1 : forall f x y l pr,
  Pfun2_differential_pt f x y pr = l -> Pfun2_differentiable_pt_lim f x y l.
Proof.
  intros f x y l (l',H1) H2.
  now rewrite <- H2.
Qed.

Lemma Pfun2_differentiable_differential : forall f x y l pr,
  prod (Pfun2_differentiable_pt_lim f x y l -> Pfun2_differential_pt f x y pr = l)
    (Pfun2_differential_pt f x y pr = l -> Pfun2_differentiable_pt_lim f x y l).
Proof.
  split ; intros.
  apply Pfun2_differentiable_differential_0, X.
  apply (Pfun2_differentiable_differential_1 _ _ _ _ pr), H.
Qed.

Lemma Pfun2_differentiable_continuous_pt : forall f x y,
  Pfun2_differentiable_pt f x y -> Pfun2_continuity_pt f x y.
Proof.
  intros f x y Df.
  cut ({pr_x : pdom (f x y) |
    forall eps : posreal,
    exists delta : posreal,
      forall x' y' : R,
      Rabs (x' - x) < delta ->
      Rabs (y' - y) < delta ->
      exists pr_y : pdom (f x' y'), Rabs (pval _ pr_y - pval _ pr_x) <= eps}).
    intros (pr_x,Cf).
    exists pr_x ; intros.
    assert (0 < eps/2).
      apply Rdiv_lt_0_compat.
      apply eps.
      apply Rlt_R0_R2.
    elim (Cf (mkposreal _ H)) ; clear Cf ; intros delta Cf.
    exists delta ; intros.
    elim (Cf _ _ H0 H1) ; clear Cf ; intros pr_y Cf.
    exists pr_y.
    apply (Rle_lt_trans _ (eps/2)).
    apply Cf.
    rewrite <- (Rplus_0_r (eps/2)), (double_var eps).
    apply Rplus_le_lt_compat.
    apply Req_le ; field.
    apply H.
  destruct Df as ((l1,l2),(pr_x,Df)).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros d0 Df.
  assert (Hd : 0 < Rmin d0 (eps/((Rabs l1) + (Rabs l2) + eps))).
    apply Rmin_pos.
    apply d0.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rplus_le_lt_0_compat.
    apply Rplus_le_le_0_compat.
    apply Rabs_pos.
    apply Rabs_pos.
    apply eps.
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (x' - x) < d0).
    apply (Rlt_le_trans _ _ _ H) ; unfold delta ; simpl ; apply Rmin_l.
  assert (Rabs (y' - y) < d0).
    apply (Rlt_le_trans _ _ _ H0) ; unfold delta ; simpl ; apply Rmin_l.
  elim (Df _ _ H1 H2) ; clear Df ; simpl ; intros pr_y Df.
  exists pr_y.
  apply (Rle_trans _ ((eps + (Rabs l1 + Rabs l2)) * delta)).
  apply (Rle_trans _ (Rabs (pval _ pr_y - pval _ pr_x - (l1 * (x' - x) + l2 * (y' - y)))
    + Rabs (l1 * (x' - x) + l2 * (y' - y)))).
    assert (Rabs (pval _ pr_y - pval _ pr_x) =
      Rabs ((pval _ pr_y - pval _ pr_x - (l1 * (x' - x) + l2 * (y' - y))) +
      (l1 * (x' - x) + l2 * (y' - y)))).
    assert ((pval _ pr_y - pval _ pr_x) =
      (pval _ pr_y - pval _ pr_x - (l1 * (x' - x) + l2 * (y' - y))) +
      (l1 * (x' - x) + l2 * (y' - y))).
      ring.
      rewrite <- H3 ; clear H3 ; ring.
    rewrite H3 ; clear H3 ; apply Rabs_triang.
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  apply (Rle_trans _ (eps * Rmax (Rabs (x' - x)) (Rabs (y' - y)))).
  apply Df.
  apply Rmult_le_compat_l.
  apply Rlt_le ; apply eps.
  apply Rmax_lub ; apply Rlt_le.
  apply H.
  apply H0.
  apply (Rle_trans _ (Rabs l1 * Rabs (x'-x) + Rabs l2 * Rabs (y'-y))).
  repeat rewrite <- Rabs_mult.
  apply Rabs_triang.
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat ;
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le ; apply H.
  apply Rabs_pos.
  apply Rlt_le ; apply H0.
  apply (Rle_trans _ ((eps + (Rabs l1 + Rabs l2)) * (eps / ((Rabs l1) + (Rabs l2) + eps)))).
  apply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat.
  apply Rlt_le ; apply eps.
  apply Rplus_le_le_0_compat ; apply Rabs_pos.
  unfold delta ; simpl ; apply Rmin_r.
  apply Req_le ; field.
  apply sym_not_eq, Rlt_not_eq.
  apply Rplus_le_lt_0_compat.
  apply Rplus_le_le_0_compat ; apply Rabs_pos.
  apply eps.
Qed.

(** Extention and equality *)

Lemma Pfun2_differentiable_pt_lim_extension : forall f1 f2 x y l,
  (forall x y, Pval_extension (f1 x y) (f2 x y)) ->
  Pfun2_differentiable_pt_lim f2 x y l -> Pfun2_differentiable_pt_lim f1 x y l.
Proof.
  intros f1 f2 x y l E (pr_x,Df2).
  exists (fst (E x y) pr_x) ; intros.
  elim (Df2 eps) ; clear Df2 ; intros delta Df2.
  exists delta ; intros.
  elim (Df2 _ _ H H0) ; clear Df2 ; intros pr_y Df2.
  exists (fst (E x' y') pr_y).
  rewrite (snd (E x y) _ pr_x), (snd (E x' y') _ pr_y).
  apply Df2.
Qed.

Lemma Pfun2_differentiable_pt_lim_equal : forall f1 f2 x y l,
  Pfun2_equal f1 f2 -> Pfun2_differentiable_pt_lim f2 x y l -> Pfun2_differentiable_pt_lim f1 x y l.
Proof.
  intros f1 f2 x y l Heq.
  apply Pfun2_differentiable_pt_lim_extension.
  apply Pfun2_equal_extension.
  apply Heq.
Qed.

(** Basic functions *)

Lemma Pfun2_differentiable_pt_lim_fun_0 : forall (f : R -> R -> R) x y l,
  differentiable_pt_lim f x y l -> Pfun2_differentiable_pt_lim (Pfun2_fun f) x y l.
Proof.
  intros f x y l Df.
  exists I ; intros.
  unfold differentiable_pt_lim in Df.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  exists I.
  apply (Df _ _ H H0).
Qed.
Lemma Pfun2_differentiable_pt_lim_fun_1 : forall (f : R -> R -> R) x y l,
  Pfun2_differentiable_pt_lim (Pfun2_fun f) x y l -> differentiable_pt_lim f x y l.
Proof.
  intros f x y l (pr_x,Df) eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  elim (Df _ _ H H0) ; clear Df ; intros pr_y Df.
  apply Df.
Qed.
Lemma Pfun2_differentiable_pt_lim_fun : forall (f : R -> R -> R) x y l,
  prod (differentiable_pt_lim f x y l -> Pfun2_differentiable_pt_lim (Pfun2_fun f) x y l)
    (Pfun2_differentiable_pt_lim (Pfun2_fun f) x y l -> differentiable_pt_lim f x y l).
Proof.
  split.
  apply Pfun2_differentiable_pt_lim_fun_0.
  apply Pfun2_differentiable_pt_lim_fun_1.
Qed.

Lemma Pfun2_differentiable_pt_lim_Pfun_v1_0 : forall f x y l,
  Pfun_derivable_pt_lim f x l -> Pfun2_differentiable_pt_lim (Pfun2_Pfun_v1 f) x y (l,0).
Proof.
  intros f x y l (pr_x,Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  elim (Df _ H) ; clear Df ; intros pr_y Df.
  exists pr_y.
  replace (pval (Pfun2_Pfun_v1 f x' y') pr_y - pval (Pfun2_Pfun_v1 f x y) pr_x -
    (fst (l, 0) * (x' - x) + snd (l, 0) * (y' - y)))
    with (pval _ pr_y - pval _ pr_x - l * (x' - x)) by (simpl; ring).
  apply (Rle_trans _ (eps*Rabs (x'-x))).
  apply Df.
  apply Rmult_le_compat_l, RmaxLess1.
  apply Rlt_le, eps.
Qed.
Lemma Pfun2_differentiable_pt_lim_Pfun_v1_1 : forall f x y l,
  Pfun2_differentiable_pt_lim (Pfun2_Pfun_v1 f) x y (l,0) -> Pfun_derivable_pt_lim f x l.
Proof.
  intros f x y l (pr_x,Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  assert (Rabs (y-y) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  elim (Df _ _ H H0) ; clear Df ; intros pr_y Df.
  exists pr_y.
  replace (pval (f y0) pr_y - pval (f x) pr_x - l * (y0 - x))
    with (pval _ pr_y - pval _ pr_x - (fst (l, 0) * (y0 - x) + snd (l, 0) * (y - y)))
    by (simpl ; ring).
  assert (Rabs (y0 - x) = Rmax (Rabs (y0 - x)) (Rabs (y - y))).
    rewrite Rmax_comm ; apply sym_equal, Rmax_eq_l.
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.
    rewrite H1 ; clear H1.
    apply Df.
Qed.
Lemma Pfun2_differentiable_pt_lim_Pfun_v1 : forall f x y l,
  prod (Pfun_derivable_pt_lim f x l -> Pfun2_differentiable_pt_lim (Pfun2_Pfun_v1 f) x y (l,0))
    (Pfun2_differentiable_pt_lim (Pfun2_Pfun_v1 f) x y (l,0) -> Pfun_derivable_pt_lim f x l).
Proof.
  split.
  apply Pfun2_differentiable_pt_lim_Pfun_v1_0.
  apply Pfun2_differentiable_pt_lim_Pfun_v1_1.
Qed.

Lemma Pfun2_differentiable_pt_lim_Pfun_v2_0 : forall (f : R -> partial_val) x y l,
  Pfun_derivable_pt_lim f y l -> Pfun2_differentiable_pt_lim (Pfun2_Pfun_v2 f) x y (0,l).
Proof.
  intros f x y l (pr_x,Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  elim (Df _ H0) ; clear Df ; intros pr_y Df.
  exists pr_y.
  assert (pval (Pfun2_Pfun_v2 f x' y') pr_y - pval (Pfun2_Pfun_v2 f x y) pr_x -
   (fst (0, l) * (x' - x) + snd (0, l) * (y' - y)) =
    pval _ pr_y - pval _ pr_x - l * (y' - y)).
    simpl ; ring.
    rewrite H1 ; clear H1.
  apply (Rle_trans _ (eps*Rabs (y'-y))).
  apply Df.
  apply Rmult_le_compat_l, RmaxLess2.
  apply Rlt_le, eps.
Qed.
Lemma Pfun2_differentiable_pt_lim_Pfun_v2_1 : forall (f : R -> partial_val) x y l,
  Pfun2_differentiable_pt_lim (Pfun2_Pfun_v2 f) x y (0,l) -> Pfun_derivable_pt_lim f y l.
Proof.
  intros f x y l (pr_x,Df).
  exists pr_x ; intros.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; intros.
  assert (Rabs (x-x) < delta).
    rewrite Rminus_eq0, Rabs_R0 ; apply delta.
  elim (Df _ _ H0 H) ; clear Df ; intros pr_y Df.
  exists pr_y.
  assert (pval (f y0) pr_y - pval (f y) pr_x - l * (y0 - y) =
    pval (Pfun2_Pfun_v2 f x y0) pr_y - pval (Pfun2_Pfun_v2 f x y) pr_x -
        (fst (0, l) * (x - x) + snd (0, l) * (y0 - y))).
    simpl ; ring.
    rewrite H1 ; clear H1.
  assert (Rabs (y0 - y) = Rmax (Rabs (x - x)) (Rabs (y0 - y))).
    apply sym_equal, Rmax_eq_l.
    rewrite Rminus_eq0, Rabs_R0 ; apply Rabs_pos.
    rewrite H1 ; clear H1.
    apply Df.
Qed.
Lemma Pfun2_differentiable_pt_lim_Pfun_v2 : forall (f : R -> partial_val) x y l,
  prod (Pfun_derivable_pt_lim f y l -> Pfun2_differentiable_pt_lim (Pfun2_Pfun_v2 f) x y (0,l))
    (Pfun2_differentiable_pt_lim (Pfun2_Pfun_v2 f) x y (0,l) -> Pfun_derivable_pt_lim f y l).
Proof.
  split.
  apply Pfun2_differentiable_pt_lim_Pfun_v2_0.
  apply Pfun2_differentiable_pt_lim_Pfun_v2_1.
Qed.

Lemma Pfun2_differentiable_pt_lim_comp2 : forall f1 f2 f3 x y l1 l2 l3,
  Pfun2_differentiable_pt_lim f2 x y l2 -> Pfun2_differentiable_pt_lim f3 x y l3 ->
  (forall d2 d3, Pfun2_differentiable_pt_lim f1 (pval (f2 x y) d2) (pval (f3 x y) d3) l1) ->
  Pfun2_differentiable_pt_lim (fun x y => Pfun2_app f1 (f2 x y) (f3 x y)) x y
    (fst l1 * fst l2 + snd l1 * fst l3,fst l1 * snd l2 + snd l1 * snd l3 ).
Proof.
  intros f1 f2 f3 x y (l1_1,l1_2) (l2_1,l2_2) (l3_1,l3_2) Df2 Df3 Df1 ; simpl.
  assert (Cf2 : Pfun2_continuity_pt f2 x y).
    apply Pfun2_differentiable_continuous_pt.
    exists (l2_1,l2_2) ; apply Df2.
  assert (Cf3 : Pfun2_continuity_pt f3 x y).
    apply Pfun2_differentiable_continuous_pt.
    exists (l3_1,l3_2) ; apply Df3.

  elim Df2 ; clear Df2 ; intros pr2_x Df2.
  elim Cf2 ; clear Cf2 ; intros pr2'_x Cf2.
  elim Df3 ; clear Df3 ; intros pr3_x Df3.
  elim Cf3 ; clear Cf3 ; intros pr3'_x Cf3.
  elim (Df1 pr2_x pr3_x) ; clear Df1 ; intros pr1_x Df1.
  unfold Pfun2_differentiable_pt_lim ; simpl.
  assert (pr_x : {dx : pdom (f2 x y) & 
  {dy : pdom (f3 x y) &  pdom (f1 (pval (f2 x y) dx) (pval (f3 x y) dy))}}).
  exists pr2_x ; exists pr3_x ; apply pr1_x.
  exists (pr_x).
  intros eps.
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
  elim (Df2 eps2) ; clear Df2 ; intros d'2 Df2.
  elim (Df3 eps3) ; clear Df3 ; intros d'3 Df3.
  assert (Hd : 0 < Rmin (Rmin d1 d'1) (Rmin d'2 d'3)).
    apply Rmin_pos ; apply Rmin_pos ;
    [apply d1 | apply d'1 | apply d'2 | apply d'3].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  assert (Rabs (x' - x) < d'2 /\ Rabs (y' - y) < d'2).
    split ;
    [apply (Rlt_le_trans _ delta _ H)|apply (Rlt_le_trans _ _ _ H0)] ;
    simpl ;
    apply (Rle_trans _ (Rmin d'2 d'3) _ (Rmin_r _ _) (Rmin_l _ _)).
  elim (Df2 _ _ (proj1 H1) (proj2 H1)) ; clear H1 Df2 ; intros pr2_y Df2.
  assert (Rabs (x' - x) < d1 /\ Rabs (y' - y) < d1).
    split ;
    [apply (Rlt_le_trans _ delta _ H)|apply (Rlt_le_trans _ _ _ H0)] ;
    simpl ;
    apply (Rle_trans _ (Rmin d1 d'1) _ (Rmin_l _ _) (Rmin_l _ _)).
  elim (Cf2 x' y' (proj1 H1) (proj2 H1)) ; clear H1 Cf2 ; intros pr2'_y Cf2.
  assert (Rabs (x' - x) < d'3 /\ Rabs (y' - y) < d'3).
    split ;
    [apply (Rlt_le_trans _ delta _ H)|apply (Rlt_le_trans _ _ _ H0)] ;
    simpl ;
    apply (Rle_trans _ (Rmin d'2 d'3) _ (Rmin_r _ _) (Rmin_r _ _)).
  elim (Df3 _ _ (proj1 H1) (proj2 H1)) ; clear H1 Df3 ; intros pr3_y Df3.
  assert (Rabs (x' - x) < d'1 /\ Rabs (y' - y) < d'1).
    split ;
    [apply (Rlt_le_trans _ delta _ H)|apply (Rlt_le_trans _ _ _ H0)] ;
    simpl ;
    apply (Rle_trans _ (Rmin d1 d'1) _ (Rmin_l _ _) (Rmin_r _ _)).
  elim (Cf3 x' y' (proj1 H1) (proj2 H1)) ; clear H1 Cf3 ; intros pr3'_y Cf3.
  rewrite (pHeq _ _ pr2_x), (pHeq _ _ pr2_y) in Cf2.
  rewrite (pHeq _ _ pr3_x), (pHeq _ _ pr3_y) in Cf3.
  elim (Df1 _ _ Cf2 Cf3) ; clear Df1 ; intros pr1_y Df1.
  assert (pr_y : {dx : pdom (f2 x' y') & 
         {dy : pdom (f3 x' y') & 
         pdom (f1 (pval (f2 x' y') dx) (pval (f3 x' y') dy))}}).
    exists pr2_y ; exists pr3_y ; apply pr1_y.
  exists pr_y.
  simpl.
  apply (Rle_trans _ (Rabs (pval _ pr1_y - pval _ pr1_x -
    (l1_1 * (pval _ pr2_y - pval _ pr2_x) + l1_2 * (pval _ pr3_y - pval _ pr3_x)))
    + Rabs (l1_1 * (pval _ pr2_y - pval _ pr2_x) + l1_2 * (pval _ pr3_y - pval _ pr3_x) -
    ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))))).
    assert ((pval (f1 (pval (f2 x' y') (projT1 pr_y))
      (pval (f3 x' y') (projT1 (projT2 pr_y)))) (projT2 (projT2 pr_y)) -
      pval (f1 (pval (f2 x y) (projT1 pr_x)) (pval (f3 x y) (projT1 (projT2 pr_x))))
      (projT2 (projT2 pr_x)) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))) =
      (pval (f1 (pval (f2 x' y') pr2_y) (pval (f3 x' y') pr3_y)) pr1_y -
      pval (f1 (pval (f2 x y) pr2_x) (pval (f3 x y) pr3_x)) pr1_x -
      (l1_1 * (pval (f2 x' y') pr2_y - pval (f2 x y) pr2_x) +
      l1_2 * (pval (f3 x' y') pr3_y - pval (f3 x y) pr3_x))) +
      (l1_1 * (pval (f2 x' y') pr2_y - pval (f2 x y) pr2_x) +
      l1_2 * (pval (f3 x' y') pr3_y - pval (f3 x y) pr3_x) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))).
      destruct pr_x as (pr2_x',(pr3_x',pr1_x')) ; simpl.
      revert pr1_x' ; rewrite (pHeq _ pr2_x' pr2_x), (pHeq _ pr3_x' pr3_x) ; intros ;
      rewrite (pHeq _ pr1_x' pr1_x).
      destruct pr_y as (pr2_y',(pr3_y',pr1_y')) ; simpl.
      revert pr1_y' ; rewrite (pHeq _ pr2_y' pr2_y), (pHeq _ pr3_y' pr3_y) ; intros ;
      rewrite (pHeq _ pr1_y' pr1_y).
      ring.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
  rewrite (double_var eps), (Rmult_plus_distr_r (eps/2)).
  apply Rplus_le_compat.
    apply (Rle_trans _ (eps1 *
      Rmax (Rabs (pval _ pr2_y - pval _ pr2_x))
        (Rabs (pval _ pr3_y - pval _ pr3_x)))).
    apply Df1.
  apply (Rle_trans _ (eps1 * (Rmax (eps2 + Rabs l2_1 + Rabs l2_2)
    (eps3 + Rabs l3_1 + Rabs l3_2) * Rmax (Rabs (x'-x)) (Rabs (y'-y))))).
    apply Rmult_le_compat_l.
    apply Rlt_le, eps1.
    rewrite Rmax_mult.
    apply Rmax_le.
    rewrite Rplus_assoc, Rmult_plus_distr_r.
    apply (Rle_trans _ (Rabs (pval _ pr2_y - pval _ pr2_x - (l2_1 * (x' - x) + l2_2 * (y' - y)))
      + Rabs (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      refine (Rle_trans _ _ _ _ (Rabs_triang _ _)).
      right. apply f_equal. ring.
    apply Rplus_le_compat.
    apply Df2.
    apply (Rle_trans _ (Rabs l2_1 * Rabs (x'-x) + Rabs l2_2 * Rabs (y'-y))).
      repeat rewrite <- Rabs_mult ; apply Rabs_triang.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat ; apply Rmult_le_compat_l.
      apply Rabs_pos.
      apply RmaxLess1.
      apply Rabs_pos.
      apply RmaxLess2.
  rewrite Rplus_assoc, Rmult_plus_distr_r.
  apply (Rle_trans _ (Rabs (pval _ pr3_y - pval _ pr3_x - (l3_1 * (x' - x) + l3_2 * (y' - y)))
      + Rabs (l3_1 * (x' - x) + l3_2 * (y' - y)))).
    refine (Rle_trans _ _ _ _ (Rabs_triang _ _)).
    right. apply f_equal. ring.
    apply Rplus_le_compat.
    apply Df3.
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
  apply (Rle_trans _ (Rabs l1_1 * Rabs (pval _ pr2_y - pval _ pr2_x - (l2_1 * (x' - x) + l2_2 * (y' - y)))
    + Rabs l1_2 * Rabs (pval _ pr3_y - pval _ pr3_x - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
    repeat rewrite <- Rabs_mult.
    refine (Rle_trans _ _ _ _ (Rabs_triang _ _)).
    right. apply f_equal. ring.
  apply Rplus_le_compat.
  apply (Rle_trans _ (Rabs l1_1 * (eps2 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
    apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Df2.
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

Lemma Pfun2_differentiable_pt_lim_comp1 : forall (f1 : R -> partial_val) (f2 : R -> R -> partial_val) x y l1 l2,
  Pfun2_differentiable_pt_lim f2 x y l2 -> (forall d, Pfun_derivable_pt_lim f1 (pval (f2 x y) d) l1) ->
    Pfun2_differentiable_pt_lim (fun x y => Pfun_app f1 (f2 x y)) x y (l1 * fst l2, l1 * snd l2).
Proof.
  intros f1 f2 x y l1 l2 Df2 Df1.
  assert ((l1 * fst l2, l1 * snd l2) =
    (fst (l1,0) * fst l2 + snd (l1,0) * fst (0,0),
    fst (l1,0) * snd l2 + snd (l1,0) * snd (0,0) )).
    apply injective_projections ; simpl ; ring.
    rewrite H ; clear H.
  apply (Pfun2_differentiable_pt_lim_extension _ (fun x y => Pfun2_app (Pfun2_Pfun_v1 f1) (f2 x y) (Pval_val 0))).
  split ; simpl.
  intros (dx,(_,d)).
  exists dx ; apply d.
  intros (d,d1) (dx,(t,dx1)) ; simpl.
  revert d1 ; rewrite (pHeq _ d dx) ; intros ; apply pHeq.
  apply Pfun2_differentiable_pt_lim_comp2.
  apply Df2.
  apply (Pfun2_differentiable_pt_lim_Pfun_v1 (fun x => Pval_val 0) x y 0),
  Pfun_derivable_pt_lim_const.
  intros ; apply (Pfun2_differentiable_pt_lim_Pfun_v1 f1 (pval (f2 x y) d2)
  (pval (Pval_val 0) d3) l1), Df1.
Qed.

Lemma Pfun_derivable_pt_lim_comp2 : forall f1 f2 f3 x l1 l2 l3,
  Pfun_derivable_pt_lim f2 x l2 -> Pfun_derivable_pt_lim f3 x l3 ->
  (forall d2 d3, Pfun2_differentiable_pt_lim f1 (pval (f2 x) d2) (pval (f3 x) d3) l1) ->
  Pfun_derivable_pt_lim (fun x => Pfun2_app f1 (f2 x) (f3 x)) x (fst l1 * l2 + snd l1 * l3).
Proof.
  intros f1 f2 f3 x l1 l2 l3 Df2 Df3 Df1.
  apply Pfun2_differentiable_pt_lim_Pfun_v1_1 with 0.
  apply (Pfun2_differentiable_pt_lim_extension _ (fun x y => Pfun2_app f1 (Pfun2_Pfun_v1 f2 x y) (Pfun2_Pfun_v1 f3 x y))).
    split ; intros.
    apply X.
    simpl in d1, d2.
    destruct d1 as (d1x,(d1y,d1)).
    destruct d2 as (d2x,(d2y,d2)).
    simpl.
    revert d1.
    rewrite (pHeq _ d1x d2x), (pHeq _ d1y d2y).
    intros.
    apply pHeq.
  assert ((fst l1 * l2 + snd l1 * l3,0) =
    (fst l1 * fst (l2,0) + snd l1 * fst (l3,0),
    fst l1 * snd (l2,0) + snd l1 * snd (l3,0) )).
    apply injective_projections ; simpl ; ring.
    rewrite H ; clear H.
  apply Pfun2_differentiable_pt_lim_comp2.
  apply (Pfun2_differentiable_pt_lim_Pfun_v1 _ _ _ _), Df2.
  apply (Pfun2_differentiable_pt_lim_Pfun_v1 _ _ _ _), Df3.
  apply Df1.
Qed.

(** Riemann integrale *)

Lemma Pfun2_Rint_Heq :
  forall (f : R -> partial_val) a b d1 d2,
  Pval_RiemannInt f a b d1 = Pval_RiemannInt f a b d2.
Proof.
  intros f a b (def1,Rint1) (def2,Rint2).
  unfold Pval_RiemannInt ; simpl.
  apply RiemannInt_expr.
  intros ; unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin a b) x) ; [| elim n ; apply H].
  destruct (Rle_dec x (Rmax a b)) ; [| elim n ; apply H].
  apply (pHeq (f x)).
Qed.
Definition Pfun2_Rint f a b :=
  Pval (Pval_Riemann_integrable f a b)
    (Pval_RiemannInt f a b) (Pfun2_Rint_Heq f a b).

Lemma Pfun2_differentiable_pt_lim_Rint : forall f,
  forall a b (d : posreal) pr_a pr_b, Pfun_continuity_pt f a ->
  Pfun_continuity_pt f b ->
  Pval_Riemann_integrable f a b ->
  Pval_Riemann_integrable f (a-d) (a+d) ->
  Pval_Riemann_integrable f (b-d) (b+d) ->
  Pfun2_differentiable_pt_lim (Pfun2_Rint f) a b (-pval (f a) pr_a, pval (f b) pr_b).
Proof.
  intros f a b d pr_a pr_b (pr'_a,Cf_a) (pr'_b,Cf_b) Rint_ab Rint_a_d Rint_b_d.
  exists Rint_ab ; intros.
  assert (He' : 0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (eps' := mkposreal _ He').
  elim (Cf_a eps') ; clear Cf_a ; intros da Cf_a.
  elim (Cf_b eps') ; clear Cf_b ; intros db Cf_b.
  assert (Hd : 0 < Rmin d (Rmin da db)).
    apply Rmin_pos ; [apply d | apply Rmin_pos ; [apply da|apply db]].
    set (delta := mkposreal _ Hd) ;
  exists delta ; intros.
  assert (pr_x'a : Pval_Riemann_integrable f x' a).
    apply (Pval_Riemann_integrable_Chasles f x' (a-d)).
    apply (Pval_Riemann_integrable_bounds f).
    apply (Pval_Riemann_integrable_Chasles_1 f (a-d) (a+d) x').
    apply Rint_a_d.
    apply (Rabs_le_encadre_cor x' a d).
    apply (Rle_trans _ _ _ (Rlt_le _ _ H)).
    simpl ; apply Rmin_l.
    apply (Pval_Riemann_integrable_Chasles_1 f (a-d) (a+d) a).
    apply Rint_a_d.
    apply (Rabs_le_encadre_cor _ _ _).
    rewrite Rminus_eq0, Rabs_R0 ; apply Rlt_le, d.
  assert (pr_by' : Pval_Riemann_integrable f b y').
    apply (Pval_Riemann_integrable_Chasles f b (b-d)).
    apply (Pval_Riemann_integrable_bounds f).
    apply (Pval_Riemann_integrable_Chasles_1 f (b-d) (b+d) b).
    apply Rint_b_d.
    apply (Rabs_le_encadre_cor _ _ _).
    rewrite Rminus_eq0, Rabs_R0 ; apply Rlt_le, d.
    apply (Pval_Riemann_integrable_Chasles_1 f (b-d) (b+d) y').
    apply Rint_b_d.
    apply (Rabs_le_encadre_cor _ _ _).
    apply (Rle_trans _ _ _ (Rlt_le _ _ H0)).
    simpl ; apply Rmin_l.
  assert (pr_y : Pval_Riemann_integrable f x' y').
    apply (Pval_Riemann_integrable_Chasles f x' a y').
    apply pr_x'a.
    apply (Pval_Riemann_integrable_Chasles f a b y').
    apply Rint_ab.
    apply pr_by'.

  exists pr_y.
  simpl ;
  rewrite <- (RiemannInt_const (pval _ pr_b) b y' (Riemann_integrable_const _ _ _)) ;
  rewrite Ropp_mult_distr_l_reverse ;
  rewrite <- (RiemannInt_const (pval _ pr_a) a x' (Riemann_integrable_const _ _ _)) ;
  rewrite <- (RiemannInt_P8 (RiemannInt_P1 (Riemann_integrable_const (pval _ pr_a) a x'))).
  assert (Pval_RiemannInt f x' y' pr_y =
    Pval_RiemannInt f x' a pr_x'a +
    Pval_RiemannInt f a b Rint_ab +
    Pval_RiemannInt f b y' pr_by').
    rewrite (Pval_RiemannInt_Chasles f x' a b _ _
      (Pval_Riemann_integrable_Chasles f x' a b pr_x'a Rint_ab)).
    apply sym_equal, (Pval_RiemannInt_Chasles f).
  rewrite H1 ; clear H1.
  unfold Pval_RiemannInt.
  set (pr''_a := (RiemannInt_P1 (Riemann_integrable_const (pval _ pr_a) a x'))).
  set (pr''_b := (Riemann_integrable_const (pval _ pr_b) b y')).
  apply (Rle_trans _ (Rabs (RiemannInt (projT2 pr_x'a) - RiemannInt pr''_a)
    + Rabs (RiemannInt (projT2 pr_by')-RiemannInt pr''_b))).
  assert ((RiemannInt (projT2 pr_x'a) + RiemannInt (projT2 Rint_ab) +
    RiemannInt (projT2 pr_by') - RiemannInt (projT2 Rint_ab) -
    (RiemannInt pr''_a + RiemannInt pr''_b)) =
    (RiemannInt (projT2 pr_x'a) - RiemannInt pr''_a) +
    (RiemannInt (projT2 pr_by') - RiemannInt pr''_b)).
    ring.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
  rewrite (double_var eps), Rmult_plus_distr_r.
  apply Rplus_le_compat.
  rewrite <- (RiemannInt_minus _ _ x' a _ _
    (Riemann_integrable_minus _ _ x' a (projT2 pr_x'a) pr''_a)).
  apply (Rle_trans _ (eps' * Rabs (x' - a))).
  rewrite <- (Rabs_Ropp (x'-a)), Ropp_minus_distr'.
  apply RiemannInt_Rabs_le_const.
  intros ; unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin x' a) x) ; [| elim n ; apply H1].
  destruct (Rle_dec x (Rmax x' a)) ; [|elim n ; apply H1].
  assert (Rabs (x-a) < da).
    apply (Rle_lt_trans _ (Rabs (x'-a))).
    unfold Rmin, Rmax in H1.
    destruct (Rle_dec x' a).
    repeat rewrite Rabs_left1.
    unfold Rminus ; apply Ropp_le_contravar, Rplus_le_compat_r, H1.
    apply Rle_minus, r1.
    apply Rle_minus, H1.
    repeat rewrite Rabs_right.
    unfold Rminus ; apply Rplus_le_compat_r, H1.
    apply Rge_minus, Rle_ge, Rlt_le, Rnot_le_lt, n.
    apply Rge_minus, Rle_ge, H1.
    apply (Rlt_le_trans _ _ _ H).
    simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
  elim (Cf_a _ H2) ; clear H2 Cf_a ; intros pr_x' Cf_a.
  rewrite (pHeq _ _ pr_x'), (pHeq _ _ pr'_a).
  apply Rlt_le, Cf_a.
  apply Rmult_le_compat_l.
  apply Rlt_le, He'.
  apply RmaxLess1.
  rewrite <- (RiemannInt_minus _ _ b y' _ _
    (Riemann_integrable_minus _ _ b y' (projT2 pr_by') pr''_b)).
  apply (Rle_trans _ (eps' * Rabs (y' - b))).
  apply RiemannInt_Rabs_le_const.
  intros ; unfold Pfun_eval_a_b.
  destruct (Rle_dec (Rmin b y') x) ; [| elim n ; apply H1].
  destruct (Rle_dec x (Rmax b y')) ; [|elim n ; apply H1].
  assert (Rabs (x-b) < db).
    apply (Rle_lt_trans _ (Rabs (y'-b))).
    unfold Rmin, Rmax in H1.
    destruct (Rle_dec b y').
    repeat rewrite Rabs_right.
    unfold Rminus ; apply Rplus_le_compat_r, H1.
    apply Rge_minus, Rle_ge, r1.
    apply Rge_minus, Rle_ge, H1.
    repeat rewrite Rabs_left1.
    unfold Rminus ; apply Ropp_le_contravar, Rplus_le_compat_r, H1.
    apply Rle_minus, Rlt_le, Rnot_le_lt, n.
    apply Rle_minus, H1.
    apply (Rlt_le_trans _ _ _ H0).
    simpl ; apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
  elim (Cf_b _ H2) ; clear H2 Cf_b ; intros pr_y' Cf_b.
  rewrite (pHeq _ _ pr_y'), (pHeq _ _ pr'_b).
  apply Rlt_le, Cf_b.
  apply Rmult_le_compat_l.
  apply Rlt_le, He'.
  apply RmaxLess2.
Qed.
