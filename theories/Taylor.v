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

Lemma ex_deriv_eta: forall f g x,
  ex_deriv f x -> (forall y, f y = g y) -> ex_deriv g x.
intros f g x (l,Hf) Hfg.
exists l.
intros t Ht.
destruct (Hf t Ht).
exists x0; intros h Hh1 Hh2.
rewrite <- 2!Hfg.
now apply H.
Qed.






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


admit. (* compliqué *)


assert (m + S k < S (S n))%nat.
omega.
specialize (H1 m (S k) H u v Hu Hv).
apply ex_deriv_eta with (1:=proj2 H1).
intros; unfold partial_derive.
simpl.
apply f_equal. (* argh, mauvais sens du Deriv_n *)



unfold ex_diff_n in *.


; exists (mkposreal 1 Rlt_0_1).



specialize (H3 (mkposreal 1 Rlt_0_1)).





















