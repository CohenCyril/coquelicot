Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Locally Deriv_fct.

Lemma MVT_cor4:
  forall (f : R -> R) a eps,
  (forall c, Rabs (c - a) <= eps -> ex_derive f c) ->
  forall b, (Rabs (b - a) <= eps) ->
  exists c, f b - f a = Derive f c * (b - a) /\ (Rabs (c - a) <= Rabs (b - a)).
Proof.
intros f a eps Hf' b.
unfold Rabs at 1 3.
case Rcase_abs; intros H1 H2.
destruct (MVT_cor2 f (Derive f) b a).
apply Rplus_lt_reg_r with (-a).
ring_simplify.
now rewrite Rplus_comm.
intros c Hc.
apply Derive_correct.
apply Hf'.
rewrite Rabs_left1.
apply Rle_trans with (2:=H2).
apply Ropp_le_contravar.
now apply Rplus_le_compat_r.
apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
rewrite -RIneq.Ropp_minus_distr (proj1 H).
ring.
rewrite Rabs_left.
apply Ropp_le_contravar.
left; now apply Rplus_lt_compat_r.
apply Rplus_lt_reg_r with a.
now ring_simplify.
destruct H1.
destruct (MVT_cor2 f (Derive f) a b).
apply Rplus_lt_reg_r with (-a).
ring_simplify.
now rewrite Rplus_comm.
intros c Hc.
apply Derive_correct.
apply Hf'.
rewrite Rabs_right.
apply Rle_trans with (2:=H2).
now apply Rplus_le_compat_r.
apply Rle_ge; apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
exact (proj1 H0).
rewrite Rabs_right.
left; now apply Rplus_lt_compat_r.
apply Rle_ge; apply Rplus_le_reg_r with a.
left; now ring_simplify.
exists a.
replace b with a.
split;[ring|idtac].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rle_refl.
apply Rplus_eq_reg_l with (-a).
ring_simplify.
rewrite - H; ring.
Qed.

Lemma bounded_variation :
  forall h D x y,
  (forall t, Rabs (t - x) <= Rabs (y - x) -> ex_derive h t /\ (Rabs (Derive h t) <= D)) ->
  Rabs (h y - h x) <= D * Rabs (y - x).
Proof.
intros h D x y H.
destruct (MVT_cor4 h x (Rabs (y - x))) with (b := y) as [t Ht].
intros c Hc.
specialize (H c Hc).
apply H.
apply Rle_refl.
rewrite (proj1 Ht).
rewrite Rabs_mult.
apply Rmult_le_compat_r.
apply Rabs_pos.
now apply H.
Qed.

Definition continuity2_pt (f : R -> R -> R) (x y : R) :=
  forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.

Definition derivable_pt_lim_aux (f : R -> R) (x l : R) :=
  forall eps : posreal, locally (fun y => Rabs (f y - f x - l * (y-x)) <= eps * Rabs (y-x)) x.

Lemma equiv_deriv_pt_lim_0 : forall f x l,
  derivable_pt_lim f x l -> derivable_pt_lim_aux f x l.
Proof.
  intros f x l.
  move /derivable_pt_lim_locally => H eps.
  specialize (H eps).
  apply: locally_impl H.
  apply locally_forall => y H.
  destruct (Req_dec y x) as [H'|H'].
  rewrite H'.
  ring_simplify (f x - f x - l * (x - x)).
  rewrite /Rminus Rplus_opp_r Rabs_R0 Rmult_0_r.
  apply Rle_refl.
  move: (H H') => {H} H.
  replace (f y - f x - l * (y - x)) with (((f y - f x) / (y - x) - l) * (y - x)).
  rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  now apply Rlt_le.
  field.
  contradict H'.
  now apply Rminus_diag_uniq.
Qed.

Lemma equiv_deriv_pt_lim_1 : forall f x l,
  derivable_pt_lim_aux f x l -> derivable_pt_lim f x l.
Proof.
  intros f x l Df.
  intros eps Heps.
  assert (He : 0 < eps/2).
    apply Rdiv_lt_0_compat.
    apply Heps.
    apply Rlt_R0_R2.
    set (eps2 := mkposreal _ He).
  elim (Df eps2) ; clear Df ; intros delta Df.
  exists delta ; intros.
  assert (x+h-x = h).
    ring.
  assert (((f (x + h) - f x) / h - l) = (f(x+h) - f x - l * ((x+h)-x))/((x+h)-x)).
    field.
    rewrite H1 ;
    apply H.
    rewrite H2 ; clear H2.
  apply (Rle_lt_trans _ eps2).
  rewrite Rabs_div.
  apply (Rle_div _ _ (Rabs (x + h - x))).
  apply Rabs_pos_lt.
  rewrite H1 ;
    apply H.
  apply (Df (x+h)).
  rewrite H1 ;
    apply H0.
    rewrite H1 ; apply H.
  rewrite (double_var eps).
  rewrite <- (Rplus_0_r eps2).
  unfold eps2 ; simpl.
  apply Rplus_lt_compat_l.
  apply He.
Qed.

Definition differentiable_pt_lim (f : R -> R -> R) (x y : R) (lx ly : R) :=
  forall eps : posreal, locally_2d (fun u v =>
    Rabs (f u v - f x y - (lx * (u - x) + ly * (v - y))) <= eps * Rmax (Rabs (u - x)) (Rabs (v - y))) x y.

Lemma differentiable_pt_lim_eta : forall f1 f2 x y lx ly,
  locally_2d (fun u v => f1 u v = f2 u v) x y ->
  differentiable_pt_lim f1 x y lx ly -> differentiable_pt_lim f2 x y lx ly.
Proof.
  intros f1 f2 x y lx ly H H1 eps.
  apply: locally_2d_impl (H1 eps) => {H1}.
  apply: locally_2d_align (H).
  intros e Heq u v  Hu Hv H0.
  apply locally_2d_singleton in H.
  now rewrite -H -Heq.
Qed.

Definition differentiable_pt (f : R -> R -> R) (x y : R) :=
  exists lx, exists ly, differentiable_pt_lim f x y lx ly.

Lemma differentiable_continuity_pt : forall f x y,
  differentiable_pt f x y -> continuity2_pt f x y.
Proof.
  intros f x y (l1&l2&Df) eps ; simpl in Df.
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
  exists delta ; intros x' y' H1 H2.
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


(*
Lemma toto3: forall f eps x y, 
  locally_2d (fun u v => continuity_pt (fun t => f t v) u) x y -> 
  exists delta:posreal,
    forall u v t : R,
     Rabs (u - x) < delta ->
     Rabs (v - y) < delta ->
     Rabs (v - t) < delta ->
     Rabs (f u t - f x t) <= eps ->
     Rabs (f u v - f x v) <= eps.
intros f eps x y (d,H).
exists d.
intros u v t Hu Hv Ht H1.

assert (locally
         (fun u : R =>
          forall eps : posreal, locally (fun t : R => Rabs (f u t - f x t) <= eps ) x) y).
apply (locally_impl (fun v : R => continuity_pt (fun u : R => f u v) x) 
  (fun u : R => forall eps0 : posreal, locally (fun t : R => Rabs (f u t - f x t) <= eps0) x) y).
2: apply H.
apply locally_forall.
intros z Hz.
specialize (proj1 (continuity_pt_locally _ _) Hz).

apply continuity_pt_locally in Hz.
.

continuity_pt_locally

unfold continuity_pt, continue_in in H1.
*)


Lemma derivable_differentiable_pt_lim : forall f x y l2,
    locally_2d (fun u v => ex_derive (fun z => f z v) u) x y ->
    (*locally (fun u => ex_derive (fun z => f z u) x) y ->*)
    is_derive (fun z => f x z) y l2 -> 
    continuity_pt (fun u => Derive (fun z => f z u) x) y ->
    (* continuity2_pt (fun u v => Derive (fun z => f z v) u) x y ->*)
    differentiable_pt_lim f x y (Derive (fun u => f u y) x) l2. 
Proof.
  intros f x y l2 Dx Dy CC.
  (* . *)
  assert (Dx2:(locally (fun u => derivable_pt_lim_aux (fun t => f t u) x (Derive (fun t => f t u) x)) y)).
  apply locally_2d_1d_const_x in Dx.
  apply locally_impl with (2:=Dx).
  apply locally_forall.
  intros z Hz.
  apply equiv_deriv_pt_lim_0.
  apply Derive_correct.
  exact Hz.
  assert (Dx3: forall eps:posreal, locally_2d (fun u v : R =>
            Rabs (f u v - f x v - Derive (fun t : R => f t v) x * (u - x)) <=
            eps * Rabs (u - x)) x y).
  intros eps.
  unfold ex_derive, derivable_pt_lim in Dx. 

  destruct Dx as (d,Hd).


  apply locally_locally_2D with 
    (P:=fun eps u v =>  Rabs (f u v - f x v - Derive (fun t : R => f t v) x * (u - x)) <= eps * Rabs (u - x)).
  intros eps0 u v. 
  case (Rle_or_lt (Rabs (f u v - f x v - Derive (fun t : R => f t v) x * (u - x)))
              (eps0 * Rabs (u - x))).
  intros; now left.
  intros; right; now apply Rlt_not_le.
  exact Dx2.
  clear eps.
  destruct Dx as (d,H1).
  unfold ex_derive in H1.


  exists (mkposreal _ Rlt_0_1).
  simpl; intros u v t Hu Hv Ht H2.



 
  admit.

  clear Dx Dx2.
  (* . *)
  assert (Dy2:derivable_pt_lim_aux (fun t => f x t) y l2).
  now apply equiv_deriv_pt_lim_0.
  clear Dy.
  (* . *)
(*  assert (continuity_pt (fun u => Derive (fun z => f z u) x) y).
  intros eps Heps. 
  destruct (CC (mkposreal eps Heps))  as (d,Hd).
  exists d; split.
  apply cond_pos.
  simpl; unfold dist, R_dist; intros z (_,Hz2).
  apply Hd.
  rewrite /Rminus Rplus_opp_r Rabs_R0.
  apply cond_pos.
  exact Hz2.
  clear CC; revert H; move /continuity_pt_locally => Cx eps.*)
  revert CC; move /continuity_pt_locally => Cx eps.
  set (eps' := pos_div_2 (pos_div_2 eps)).
  move: (Dy2 eps') => {Dy2} [dy Hy].
  move: (Dx3 eps') => {Dx3} [dx Hx].
  move: (Cx eps') => {Cx} [dx2 Cx].
  (* *)
  pose (d1:=(mkposreal _ (Rmin_stable_in_posreal dx dy))).
  exists (mkposreal _ (Rmin_stable_in_posreal d1 dx2)) => /= u v Hu Hv.
  set (l1 := Derive (fun u : R => f u y) x).
  replace (f u v - f x y - (l1 * (u - x) + l2 * (v - y))) with
    ((f u v - f x v - l1 * (u - x)) + (f x v - f x y - l2 * (v - y))) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (apply sym_eq ; apply double_var).
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  (* *)
  apply Rle_trans with (pos_div_2 eps * Rabs (u - x)).
  replace  (f u v - f x v - l1 * (u - x)) with
    ((f u v - f x v - Derive (fun u : R => f u v) x *(u-x))+ (u-x)*(Derive (fun u : R => f u v) x-l1)) by ring.
  apply Rle_trans with (1:=Rabs_triang _ _).
  replace (pos (pos_div_2 eps)) with (eps' + eps') by (apply sym_eq ; apply double_var).
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  apply Hx.
  apply Rlt_le_trans with (1:=Hu).
  apply Rle_trans with (1:=Rmin_l _ _).
  apply Rmin_l.
  apply Rlt_le_trans with (1:=Hv).
  apply Rle_trans with (1:=Rmin_l _ _).
  apply Rmin_l.
  rewrite (Rmult_comm eps' _) Rabs_mult.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  unfold l1; left.
  apply Cx.
  apply Rlt_le_trans with (1:=Hv).
  apply Rmin_r.
  apply Rmult_le_compat_l.
  left; apply cond_pos.
  apply Rmax_l.
  (* *)
  apply Rle_trans with (eps' * Rabs (v - y)).
  apply Hy.
  apply Rlt_le_trans with (1:=Hv).
  apply Rle_trans with (1:=Rmin_l _ _).
  apply Rmin_r.
  apply Rmult_le_compat.
  left; apply cond_pos.
  apply Rabs_pos.
  rewrite <- (Rplus_0_r eps').
  rewrite (double_var (pos_div_2 eps)); unfold eps'.
  apply Rplus_le_compat_l.
  replace (pos_div_2 eps / 2) with (pos eps') by reflexivity.
  left; apply cond_pos.
  apply Rmax_r.
  Qed.



Lemma derivable_differentiable_pt_lim2 : forall f x y,
  locally_2d (fun u v => ex_derive (fun z => f z v) u) x y ->
  is_derive (fun z => f x z) y l2 -> 
  continuity2_pt (fun u v => Derive (fun z => f z v) u) x y ->
  differentiable_pt_lim f x y (Derive (fun u => f u y) x) l2.


Lemma derivable_differentiable_pt_lim : forall f x y,
  locally_2d (fun u v => ex_derive (fun z => f z v) u) x y ->
  locally_2d (fun u v => ex_derive (fun z => f u z) v) x y ->
  continuity2_pt (fun u v => Derive (fun z => f z v) u) x y ->
  continuity2_pt (fun u v => Derive (fun z => f u z) v) x y ->
  differentiable_pt_lim f x y (Derive (fun u => f u y) x) (Derive (fun v => f x v) y).
Proof.
  intros f x y Dx Dy Cx Cy eps.
  set (eps' := pos_div_2 eps).
  specialize (Cx eps').
  specialize (Cy eps').
  move: (locally_2d_and _ _ _ _ Dx Dy) => {Dx Dy} H.
  move: (locally_2d_and _ _ _ _ H Cx) => {H Cx} H.
  move: (locally_2d_and _ _ _ _ H Cy) => {H Cy}.
  set (l1 := Derive (fun u : R => f u y) x).
  set (l2 := Derive (fun v : R => f x v) y).
  apply: locally_2d_align => delta H u v Hu Hv.
  set (g1 t := f t v - l1*t).
  set (g2 t := f x t - l2*t).
  apply Rle_trans with (Rabs (g1 u - g1 x) + Rabs (g2 v - g2 y)).
    replace (f u v - f x y - (l1 * (u - x) + l2 * (v - y))) with
      ((g1 u - g1 x) + (g2 v - g2 y)) by (unfold g1, g2 ; ring).
    apply Rabs_triang.
  replace (pos eps) with (eps' + eps') by (apply sym_eq ; apply double_var).
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  (* *)
  apply Rle_trans with (eps' * Rabs (u - x)).
  apply bounded_variation => t Ht.
  assert (is_derive g1 t (Derive (fun z : R => f z v) t - l1)).
    apply derivable_pt_lim_minus with (f2 := fun t => l1 * t).
    apply Derive_correct.
    apply H with (2 := Hv).
    now apply Rle_lt_trans with (1 := Ht).
    rewrite -{2}(Rmult_1_r l1).
    apply derivable_pt_lim_scal.
    apply derivable_pt_lim_id.
  split.
  eexists. apply H0.
  apply Rlt_le.
  rewrite (is_derive_unique _ _ _ H0).
  apply H with (2 := Hv).
  now apply Rle_lt_trans with (1 := Ht).
  apply Rmult_le_compat_l.
  apply Rlt_le.
  apply cond_pos.
  apply Rmax_l.
  (* *)
  apply Rle_trans with (eps' * Rabs (v - y)).
  apply bounded_variation => t Ht.
  assert (is_derive g2 t (Derive (fun z : R => f x z) t - l2)).
    apply derivable_pt_lim_minus with (f1 := fun v => f x v) (f2 := fun t => l2 * t).
    apply Derive_correct.
    apply H.
    rewrite /Rminus Rplus_opp_r Rabs_R0.
    apply cond_pos.
    now apply Rle_lt_trans with (1 := Ht).
    rewrite -{2}(Rmult_1_r l2).
    apply derivable_pt_lim_scal.
    apply derivable_pt_lim_id.
  split.
  eexists. apply H0.
  apply Rlt_le.
  rewrite (is_derive_unique _ _ _ H0).
  apply H.
  rewrite /Rminus Rplus_opp_r Rabs_R0.
  apply cond_pos.
  now apply Rle_lt_trans with (1 := Ht).
  apply Rmult_le_compat_l.
  apply Rlt_le.
  apply cond_pos.
  apply Rmax_r.
Qed.

Lemma differentiable_pt_lim_proj1_0 : forall f x y l,
  derivable_pt_lim f x l -> differentiable_pt_lim (fun u v => f u) x y l 0.
Proof.
  intros f x y l Df eps.
  apply equiv_deriv_pt_lim_0 in Df ;
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl ; intros.
  rewrite Rmult_0_l Rplus_0_r.
  apply (Rle_trans _ (eps * Rabs (u - x))).
  apply (Df _ H).
  apply Rmult_le_compat_l.
  apply Rlt_le, eps.
  apply RmaxLess1.
Qed.

Lemma differentiable_pt_lim_proj1_1 : forall f x y l,
  differentiable_pt_lim (fun u v => f u) x y l 0 -> derivable_pt_lim f x l.
Proof.
  intros f x y l Df.
  apply (equiv_deriv_pt_lim_1 _ _ _) ; intro eps.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl in Df ; intros.
  replace (f y0 - f x - l * (y0 - x)) with (f y0 - f x - (l * (y0 - x) + 0 * (y - y))) by ring.
  assert (Rabs (y0 - x) = Rmax (Rabs (y0 - x)) (Rabs (y-y))).
    rewrite Rmax_comm ; apply sym_equal, Rmax_right.
    rewrite Rminus_eq0 Rabs_R0 ; apply Rabs_pos.
  rewrite H0 ; clear H0.
  apply (Df _ _ H).
  rewrite Rminus_eq0 Rabs_R0 ; apply delta.
Qed.

Lemma differentiable_pt_lim_comp : forall f1 f2 f3 x y l1x l1y l2x l2y l3x l3y,
  differentiable_pt_lim f1 (f2 x y) (f3 x y) l1x l1y ->
  differentiable_pt_lim f2 x y l2x l2y -> differentiable_pt_lim f3 x y l3x l3y ->
  differentiable_pt_lim (fun u v => f1 (f2 u v) (f3 u v)) x y
    (l1x * l2x + l1y * l3x) (l1x * l2y + l1y * l3y).
Proof.
  intros f1 f2 f3 x y l1_1 l1_2 l2_1 l2_2 l3_1 l3_2
    Df1 Df2 Df3 eps ; simpl.
  assert (Cf2 : continuity2_pt f2 x y).
    apply differentiable_continuity_pt.
    exists l2_1 ; exists l2_2 ; apply Df2.
  assert (Cf3 : continuity2_pt f3 x y).
    apply differentiable_continuity_pt.
    exists l3_1 ; exists l3_2 ; apply Df3.
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
  exists delta ; intros x' y' ; intros.
  apply (Rle_trans _ (Rabs (f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
    (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y)))
    + Rabs (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
    ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))))).
    replace ((f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))) with
      ((f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
      (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y))) +
      (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))) by ring.
    apply Rabs_triang.
  rewrite (double_var eps) (Rmult_plus_distr_r (eps/2)).
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
    apply Rmax_le_compat.
    rewrite Rplus_assoc Rmult_plus_distr_r.
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
  rewrite Rplus_assoc Rmult_plus_distr_r.
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
  rewrite (double_var (eps/2)) (Rmult_plus_distr_r (eps/2/2)).
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

Lemma derivable_pt_lim_comp_2d : forall f1 f2 f3 x l1x l1y l2 l3,
  differentiable_pt_lim f1 (f2 x) (f3 x) l1x l1y ->
  derivable_pt_lim f2 x l2 -> derivable_pt_lim f3 x l3 ->
  derivable_pt_lim (fun t => f1 (f2 t) (f3 t)) x (l1x * l2 + l1y * l3).
Proof.
  intros.
  apply (differentiable_pt_lim_proj1_1 _ x 0 (l1x * l2 + l1y * l3)).
  pattern 0 at 2 ; replace 0 with (l1x * 0 + l1y * 0) by ring.
  apply differentiable_pt_lim_comp.
  apply H.
  apply: differentiable_pt_lim_proj1_0 H0.
  apply: differentiable_pt_lim_proj1_0 H1.
Qed.
