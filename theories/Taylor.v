Require Import Deriv_fct.




Definition partial_derive (m k : nat) (f : R -> R -> R) : R -> R -> R :=
  fun x y => Deriv_n (fun t => Deriv_n (fun z => f t z) k y) m x.

Definition differential (p : nat) (f : R -> R -> R) (x y dx dy : R) : R :=
  sum_f_R0 
    (fun m =>
      C p m *
      partial_derive m (p - m)%nat f x y *
      dx ^ m * dy ^ (p - m)%nat)
    p.

Definition DL_pol (n : nat) (f : R -> R -> R) (x y dx dy : R) : R :=
  sum_f_R0
    (fun p =>
      differential p f x y dx dy / INR (fact p))
    n.


Definition continuity2_pt (f : R -> R -> R) (x y : R) :=
  forall eps : posreal, exists delta : posreal, forall (x' y' : R),
    Rabs (x'-x) < delta -> Rabs (y'-y) < delta -> Rabs (f x' y' - f x y) < eps.
Definition continuity2 (f : R -> R -> R) :=
  forall (x y : R), continuity2_pt f x y.

Definition ex_diff_n f n x y :=
    (exists eps : posreal, forall m k, (m+k < n)%nat 
          -> forall u v, Rabs (u-x) < eps -> Rabs (v-y) < eps 
             ->  ex_deriv (fun z => partial_derive m k f z v) u /\
                 ex_deriv (fun z => partial_derive m k f u z) v )
    /\
    (forall m k, (m+k <= n)%nat 
          ->  continuity2_pt (fun u v => partial_derive m k f u v) x y).


Definition DL_regular_n f m x y :=
    exists D, exists delta: posreal, forall u v,
    Rabs (u-x) < delta -> Rabs (v-y) < delta ->
       Rabs (f u v - DL_pol m f x y (u-x) (v-y)) <= D * (Rmax (Rabs (u-x)) (Rabs (v-y))) ^ (S m).

Lemma MVT_cor4:
   forall (f f' : R -> R) (a eps : R),
   (forall c : R, Rabs (c-a) <= eps -> derivable_pt_lim f c (f' c)) ->
   forall b, (Rabs (b-a) <= eps) -> 
      exists c : R, f b - f a = f' c * (b - a) /\ (Rabs (c-a) <= Rabs (b-a)).
intros f f' a eps Hf' b.
unfold Rabs at 1 3.
case Rcase_abs; intros H1 H2.
destruct (MVT_cor2 f f' b a).
apply Rplus_lt_reg_r with (-a).
ring_simplify.
now rewrite Rplus_comm.
intros; apply Hf'.
rewrite Rabs_left1.
apply Rle_trans with (2:=H2).
apply Ropp_le_contravar.
now apply Rplus_le_compat_r.
apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
rewrite - Ropp_minus_distr (proj1 H).
ring.
rewrite Rabs_left.
apply Ropp_le_contravar.
left; now apply Rplus_lt_compat_r.
apply Rplus_lt_reg_r with a.
now ring_simplify.
destruct H1.
destruct (MVT_cor2 f f' a b).
apply Rplus_lt_reg_r with (-a).
ring_simplify.
now rewrite Rplus_comm.
intros; apply Hf'.
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


Lemma bounded_variation_aux:
  forall h x y D, x < y -> (forall t, x <= t <= y -> ex_deriv h t /\ (Rabs (Deriv h t) <= D)) -> 
     Rabs (h y - h x) <= D * Rabs (y-x).
intros h x y D H Ht.
assert (H2:= MVT_cor2 h (Deriv h) x y H).
destruct H2.
intros c Hc.
apply Deriv_prop.
now apply Ht.
rewrite (proj1 H0).
rewrite Rabs_mult.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Ht.
split; left; apply H0.
Qed.

Lemma bounded_variation: 
  forall h x y D, (forall t, Rmin x y <= t <= Rmax x y -> ex_deriv h t /\ (Rabs (Deriv h t) <= D)) -> 
     Rabs (h x - h y) <= D * Rabs (x-y).
intros h x y D; unfold Rmin, Rmax.
destruct (Rle_dec x y) as [[H|H]|H].
rewrite Rabs_minus_sym (Rabs_minus_sym x _).
now apply bounded_variation_aux.
intros _.
rewrite H /Rminus 2!Rplus_opp_r Rabs_R0 Rmult_0_r; apply Rle_refl.
apply bounded_variation_aux.
now apply Rnot_le_lt.
Qed.

Lemma ex_deriv_eta: forall f g,
   (forall y, f y = g y) -> forall x, ex_deriv f x -> ex_deriv g x.
intros f g Hfg x (l,Hf).
exists l.
intros t Ht.
destruct (Hf t Ht).
exists x0; intros h Hh1 Hh2.
rewrite <- 2!Hfg.
now apply H.
Qed.

Lemma Deriv_eta: forall f g, 
   (forall y, f y = g y) -> forall x, Deriv f x = Deriv g x.
Proof.
intros f g Hfg x.
unfold Deriv, Lim, Lim_seq.
apply f_equal.
rewrite 2!LimSup_seq_correct.
apply Rbar_limsup_eq.
intros n; now rewrite 2!Hfg.
Qed.

Lemma Deriv_n_eta: forall f g, 
   (forall y, f y = g y) -> forall n x, Deriv_n f n x = Deriv_n g n x.
Proof.
intros f g Hfg.
induction n.
now simpl.
simpl.
now apply Deriv_eta.
Qed.

Lemma Deriv_n_comp: forall f n m x,
  Deriv_n (Deriv_n f m) n x = Deriv_n f (n+m) x.
intros f n m.
induction n.
now simpl.
simpl.
now apply Deriv_eta.
Qed.






Lemma Schwartz: forall f x y (eps : posreal), 
   (forall u v, Rabs (u-x) < eps -> Rabs (v-y) < eps 
          ->  ex_deriv (fun z => f z v) u /\
              ex_deriv (fun z => f u z) v /\
              ex_deriv (fun z => Deriv (fun t => f z t) v) u /\
              ex_deriv (fun z => Deriv (fun t => f t z) u) v)
    -> continuity2_pt (fun u v => Deriv (fun z => Deriv (fun t => f z t) v) u) x y
    -> continuity2_pt (fun u v => Deriv (fun z => Deriv (fun t => f t z) u) v) x y
    -> Deriv (fun z => Deriv (fun t => f z t) y) x = Deriv (fun z => Deriv (fun t => f t z) x) y.
Proof.
intros f x y eps H H1 H2.
set (phi k x := f x (y+k) - f x y).
set (delta h k := phi k (x+h) - phi k x).
assert (ex_deriv 





Theorem Taylor_Lagrange : forall f n x y,
   ex_diff_n f (S n) x y -> DL_regular_n f n x y.
Proof.
intros f n; revert f.
induction n.
(* *)
intros f x y ((eps,H1),H).
specialize (H1 0%nat 0%nat (lt_0_Sn _)).
assert (H2 := (H 0%nat 1%nat (le_refl 1))).
assert (H3 := (H 1%nat 0%nat (le_refl 1))).
specialize (H2 (mkposreal 1 Rlt_0_1)); simpl in H2.
specialize (H3 (mkposreal 1 Rlt_0_1)); simpl in H3.
destruct H2 as (d2, Hd2).
destruct H3 as (d3, Hd3).
exists ((Rabs (partial_derive 0 1 f x y)+1) + (Rabs (partial_derive 1 0 f x y) + 1));
   exists (mkposreal _ (Rmin_stable_in_posreal eps (mkposreal _ (Rmin_stable_in_posreal d2 d3)))); simpl.
intros u v Hu Hv.
unfold DL_pol, differential, partial_derive, C; simpl.
field_simplify (f u v - 1 / (1 * 1) * f x y * 1 * 1 / 1).
unfold Rdiv; rewrite Rinv_1 (* Rmult_1_l *) 2!Rmult_1_r.
replace (f u v - f x y) with ((f u v - f u y) + (f u y - f x y)) by ring.
apply Rle_trans with (1:= Rabs_triang _ _ ).
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
(* . *)
apply Rle_trans with ((Rabs (Deriv (fun x0 : R => f x x0) y) + 1) * (Rabs (v - y))).
apply bounded_variation with (h:= fun y => f u y).
intros t Ht.
split.
apply H1.
admit.
admit.
unfold partial_derive in Hd2; simpl in Hd2.
apply Rplus_le_reg_r with (-Rabs (Deriv (fun x0 : R => f x x0) y)).
ring_simplify.
apply Rle_trans with (1:=Rabs_triang_inv _ _).
left; apply Hd2.
admit.
admit.
apply Rmult_le_compat_l.
admit.
apply Rmax_r.
(* . *)
apply Rle_trans with ((Rabs (Deriv (fun x0 : R => f x0 y) x) + 1) * (Rabs (u - x))).
apply bounded_variation with (h:= fun x => f x y).
intros t Ht.
split.
apply H1.
admit.
admit.
unfold partial_derive in Hd3; simpl in Hd3.
apply Rplus_le_reg_r with (-Rabs (Deriv (fun x0 : R => f x0 y) x)).
ring_simplify.
apply Rle_trans with (1:=Rabs_triang_inv _ _).
left; apply Hd3.
admit.
admit.
apply Rmult_le_compat_l.
admit.
apply Rmax_l.
(* *)
intros f x y H; simpl in H.
(* . *)
assert (Hx := IHn (fun x y => Deriv (fun z => f z y) x) x y).
destruct Hx as (Dx,(deltax,Hx)).
(* .. *)
destruct H as ((eps,H1),H2).
split.
exists eps.
intros m k Hmk u v Hu Hv; split.
(* ... *)
assert (S m + k < S (S n))%nat.
omega.
specialize (H1 _ _ H u v Hu Hv).
apply ex_deriv_eta with (2:=proj1 H1).
intros; unfold partial_derive.
replace (S m) with (m + 1)%nat by apply (plus_comm m 1).
rewrite -(Deriv_n_comp _ m 1).
apply Deriv_n_eta.
intros y1.
admit. (* compliqué *)
(* ... *)
assert (S m + k < S (S n))%nat.
omega.
specialize (H1 _ _ H u v Hu Hv).
apply ex_deriv_eta with (2:=proj2 H1).
intros; unfold partial_derive.
replace (S m) with (m + 1)%nat by apply (plus_comm m 1).
rewrite -(Deriv_n_comp _ m 1).
apply Deriv_n_eta.
intros y1.
admit. (* compliqué *)



rewrite -Deriv_n_comp.
apply trans_eq with ((Deriv_n (Deriv_n (fun z : R => f y1 z) k) 1) v).
reflexivity.
rewrite Deriv_n_comp plus_comm - Deriv_n_comp.
apply Deriv_n_eta.
simpl.



now idtac.

rewrite

rewrite (Deriv_n_comp _ 1 n).


apply f_equal. (* argh, mauvais sens du Deriv_n *)






unfold ex_diff_n in *.


; exists (mkposreal 1 Rlt_0_1).



specialize (H3 (mkposreal 1 Rlt_0_1)).





















