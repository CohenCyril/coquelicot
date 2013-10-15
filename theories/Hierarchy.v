(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2013 Sylvie Boldo
#<br />#
Copyright (C) 2011-2013 Catherine Lelay
#<br />#
Copyright (C) 2011-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals Locally Limit Rbar.
Require Import Rcomplements.

(** * Vector space *)

Class AbelianGroup G := {
  plus : G -> G -> G ;
  opp : G -> G ;
  minus x y := plus x (opp y) ;
  zero : G ;
  plus_comm : forall x y, plus x y = plus y x ;
  plus_assoc : forall x y z, plus x (plus y z) = plus (plus x y) z ;
  plus_zero_r : forall x, plus x zero = x ;
  plus_opp_r : forall x, plus x (opp x) = zero
}.

Lemma plus_zero_l :
  forall G (GG : AbelianGroup G) (x : G),
  plus zero x = x.
Proof.
intros G GG x.
now rewrite plus_comm, plus_zero_r.
Qed.

Lemma plus_opp_l :
  forall G (GG : AbelianGroup G) (x : G),
  plus (opp x) x = zero.
Proof.
intros G GG x.
rewrite plus_comm.
apply plus_opp_r.
Qed.

Lemma opp_zero :
  forall G (GG : AbelianGroup G),
  opp zero = zero.
Proof.
intros G GG.
rewrite <- (plus_zero_r (opp zero)).
apply plus_opp_l.
Qed.

Lemma minus_zero_r :
  forall G (GG : AbelianGroup G) (x : G),
  minus x zero = x.
Proof.
intros G GG x.
unfold minus.
rewrite opp_zero.
apply plus_zero_r.
Qed.

Lemma plus_reg_r :
  forall G (GG : AbelianGroup G) (x y z : G),
  plus x z = plus y z -> x = y.
Proof.
intros G GG x y z H.
rewrite <- (plus_zero_r x), <- (plus_zero_r y).
rewrite <- (plus_opp_r z).
rewrite 2!plus_assoc.
now rewrite H.
Qed.

Lemma opp_plus :
  forall G (GG : AbelianGroup G) (x y : G),
  opp (plus x y) = plus (opp x) (opp y).
Proof.
intros G GG x y.
apply plus_reg_r with (GG := GG) (z := plus x y).
rewrite plus_opp_l.
rewrite plus_assoc.
rewrite (plus_comm (opp x)).
rewrite <- (plus_assoc (opp y)).
rewrite plus_opp_l.
rewrite plus_zero_r.
apply sym_eq, plus_opp_l.
Qed.

Lemma opp_opp :
  forall {G} {GG : AbelianGroup G} (x : G),
  opp (opp x) = x.
Proof.
intros G GG x.
apply plus_reg_r with (GG := GG) (z := opp x).
rewrite plus_opp_r.
apply plus_opp_l.
Qed.

Class Field K := {
  field_group :> AbelianGroup K ;
  mult : K -> K -> K ;
  inv : K -> K ;
  one : K ;
  mult_comm : forall x y, mult x y = mult y x ;
  mult_assoc : forall x y z, mult x (mult y z) = mult (mult x y) z ;
  mult_one_r : forall x, mult x one = x ;
  mult_inv_r : forall x, x <> zero -> mult x (inv x) = one ;
  mult_distr_r : forall x y z, mult (plus x y) z = plus (mult x z) (mult y z)
}.

Lemma mult_one_l :
  forall K (FK : Field K) (x : K),
  mult one x = x.
Proof.
intros K FK x.
rewrite mult_comm.
apply mult_one_r.
Qed.

Lemma mult_distr_l :
  forall K (FK : Field K) (x y z : K),
  mult x (plus y z) = plus (mult x y) (mult x z).
Proof.
intros K FK x y z.
rewrite mult_comm.
rewrite mult_distr_r.
apply f_equal2 ; apply mult_comm.
Qed.

Lemma mult_zero_r :
  forall K (FK : Field K) (x : K),
  mult x zero = zero.
Proof.
intros K FK x.
apply plus_reg_r with (GG := field_group) (z := mult x zero).
rewrite <- mult_distr_l.
rewrite plus_zero_r.
now rewrite plus_zero_l.
Qed.

Lemma mult_zero_l :
  forall K (FK : Field K) (x : K),
  mult zero x = zero.
Proof.
intros K FK x.
rewrite mult_comm; apply mult_zero_r.
Qed.

Lemma mult_eq_compat_l: forall K (FK : Field K) 
  (r x y: K), r <> zero -> mult r x = mult r y -> x = y.
Proof.
intros K FK r x y Hr H.
rewrite <- (mult_one_l _ _ x).
rewrite <- (mult_inv_r r); try assumption.
rewrite mult_comm, mult_assoc, (mult_comm x _).
rewrite H.
rewrite mult_comm, mult_assoc, (mult_comm _ r).
rewrite mult_inv_r; try assumption.
apply mult_one_l.
Qed.


Lemma inv_eq: forall K (FK : Field K) 
  (x y : K), x <> zero -> mult x y = one -> y = inv x.
Proof.
intros K FK x y Hx H.
apply mult_eq_compat_l with (FK:=FK) (r:=x).
assumption.
now rewrite H, mult_inv_r.
Qed.

Lemma inv_mult :
  forall K (FK : Field K) (x y : K), mult x y <> zero ->
  inv (mult x y) = mult (inv x) (inv y).
Proof.
intros K FK x y Hxy.
apply sym_eq, inv_eq; try assumption.
rewrite (mult_comm x), mult_assoc.
rewrite <- (mult_assoc _ _ (inv x)).
rewrite mult_inv_r.
rewrite mult_one_r.
rewrite mult_inv_r.
reflexivity.
intros L; apply Hxy.
rewrite L; apply mult_zero_r.
intros L; apply Hxy.
rewrite L; apply mult_zero_l.
Qed.

Global Instance R_abelian_group : AbelianGroup R.
Proof.
apply (@Build_AbelianGroup R Rplus Ropp R0).
apply Rplus_comm.
intros x y z.
apply sym_eq, Rplus_assoc.
apply Rplus_0_r.
apply Rplus_opp_r.
Defined.

Global Instance R_field : Field R.
Proof.
apply (@Build_Field R _ Rmult Rinv R1).
apply Rmult_comm.
intros x y z.
apply sym_eq, Rmult_assoc.
apply Rmult_1_r.
apply Rinv_r.
apply Rmult_plus_distr_r.
Defined.

Class VectorSpace V K {FK : Field K} := {
  vspace_group :> AbelianGroup V ;
  scal : K -> V -> V ;
  scal_assoc : forall x y u, scal x (scal y u) = scal (mult x y) u ;
  scal_one : forall u, scal one u = u ;
  scal_distr_l : forall x u v, scal x (plus u v) = plus (scal x u) (scal x v) ;
  scal_distr_r : forall x y u, scal (plus x y) u = plus (scal x u) (scal y u)
}.

Global Instance vspace_of_field :
  forall K (FK : Field K), VectorSpace K K.
Proof.
intros K FK.
apply (@Build_VectorSpace K K FK field_group mult).
apply mult_assoc.
apply mult_one_l.
apply mult_distr_l.
apply mult_distr_r.
Defined.

Lemma scal_zero_r :
  forall V K (FK : Field K) (VV : VectorSpace V K) (x : K),
  scal x zero = zero.
Proof.
intros V K FK VV x.
apply plus_reg_r with (GG := vspace_group) (z := scal x zero).
rewrite <- scal_distr_l.
rewrite plus_zero_r.
now rewrite plus_zero_l.
Qed.

Lemma scal_zero_l :
  forall V K (FK : Field K) (VV : VectorSpace V K) (u : V),
  scal zero u = zero.
Proof.
intros V K FK VV u.
apply plus_reg_r with (GG := vspace_group) (z := scal zero u).
rewrite plus_zero_l.
rewrite <- scal_distr_r.
now rewrite plus_zero_r.
Qed.

Lemma scal_opp_l :
  forall V K (FK : Field K) (VV : VectorSpace V K) (x : K) (u : V),
  scal (opp x) u = opp (scal x u).
Proof.
intros V K FK VV x u.
apply plus_reg_r with (GG := vspace_group) (z := (scal x u)).
rewrite plus_opp_l.
rewrite <- scal_distr_r.
rewrite plus_opp_l.
apply scal_zero_l.
Qed.

Lemma scal_opp_r :
  forall V K (FK : Field K) (VV : VectorSpace V K) (x : K) (u : V),
  scal x (opp u) = opp (scal x u).
Proof.
intros V K FK VV x u.
apply plus_reg_r with (GG := vspace_group) (z := (scal x u)).
rewrite plus_opp_l.
rewrite <- scal_distr_l.
rewrite plus_opp_l.
apply scal_zero_r.
Qed.

Lemma scal_opp_one :
  forall V K (FK : Field K) (VV : VectorSpace V K) (u : V),
  scal (opp one) u = opp u.
Proof.
intros V K FK VV u.
rewrite scal_opp_l.
now rewrite scal_one.
Qed.

(** Product of vector spaces *)

Global Instance prod_abelian_group :
  forall U V (GU : AbelianGroup U) (GV : AbelianGroup V),
  AbelianGroup (U * V).
Proof.
intros U V GU GV.
apply (@Build_AbelianGroup _
  (fun x y : U * V => (plus (fst x) (fst y), plus (snd x) (snd y)))
  (fun x : U * V => (opp (fst x), opp (snd x)))
  (zero, zero)).
intros x y.
apply f_equal2 ; apply plus_comm.
intros x y z.
apply f_equal2 ; apply plus_assoc.
intros (x1,x2).
apply f_equal2 ; apply plus_zero_r.
intros x.
apply f_equal2 ; apply plus_opp_r.
Defined.

Global Instance prod_vector_space :
  forall U V K (FK : Field K) (VU : VectorSpace U K) (VV : VectorSpace V K),
  VectorSpace (U * V) K.
Proof.
intros U V K FK VU VV.
apply (@Build_VectorSpace _ K FK (prod_abelian_group _ _ _ _)
  (fun (x : K) (uv : U * V) => (scal x (fst uv), scal x (snd uv)))).
intros x y u.
apply f_equal2 ; apply scal_assoc.
intros (u,v).
apply f_equal2 ; apply scal_one.
intros x u v.
simpl.
apply f_equal2 ; apply scal_distr_l.
intros x y u.
simpl.
apply f_equal2 ; apply scal_distr_r.
Defined.


(** * Topological vector spaces *)

Class MetricVectorSpace V K {FK : Field K} := {
  mvspace_vector :> VectorSpace V K ;
  mvspace_metric :> MetricSpace V ;
  mvspace_plus : forall x y, filterlim (fun z : V * V => plus (fst z) (snd z)) (filter_prod (locally x) (locally y)) (locally (plus x y)) ;
  mvspace_scal : forall x y, filterlim (fun z : V => scal x z) (locally y) (locally (scal x y))
}.

Global Instance R_metric_vector : MetricVectorSpace R R.
Proof.
econstructor.
intros x y.
now apply filterlim_plus with (x := Finite x) (y := Finite y).
intros x y.
apply filterlim_scal_l with (l := Finite y).
Defined.

(** * Normed spaces *)

Class NormedAbelianGroup G := {
  nagroup_abelian :> AbelianGroup G ;
  norm : G -> R ;
  norm_zero : norm zero = 0 ;
  norm_opp : forall x, norm (opp x) = norm x ;
  norm_triangle : forall x y, norm (plus x y) <= norm x + norm y
}.

Lemma NAG_dist_refl {G} {NAG : NormedAbelianGroup G} :
  forall a : G, norm (minus a a) = 0.
Proof.
  move => a.
  by rewrite /minus plus_opp_r norm_zero.
Qed.
Lemma NAG_dist_comm {G} {NAG : NormedAbelianGroup G} :
  forall a b : G, norm (minus b a) = norm (minus a b).
Proof.
  move => a b.
  by rewrite /minus -norm_opp opp_plus opp_opp plus_comm.
Qed.
Lemma NAG_dist_triangle {G} {NAG : NormedAbelianGroup G} :
  forall a b c : G, norm (minus c a) <= norm (minus b a) + norm (minus c b).
Proof.
  move => a b c.
  apply Rle_trans with (2 := norm_triangle _ _).
  apply Req_le.
  rewrite plus_comm.
  unfold minus.
  rewrite plus_assoc, <- (plus_assoc c), plus_opp_l, plus_zero_r.
  reflexivity.
Qed.

Global Instance NormedAbelianGroup_MetricSpace {G : Type} :
  NormedAbelianGroup G -> MetricSpace G.
Proof.
  intro NAG.
  apply Build_MetricSpace with (fun x y => norm (minus y x)).
  - by apply NAG_dist_refl.
  - by apply NAG_dist_comm.
  - by apply NAG_dist_triangle.
Defined.

Lemma norm_ge_0 :
  forall {G} {NG : NormedAbelianGroup G} (x : G),
  0 <= norm x.
Proof.
intros G NG x.
apply Rmult_le_reg_r with (1 := Rlt_R0_R2).
rewrite Rmult_0_l, <- norm_zero, <- (plus_opp_r x).
apply Rle_trans with (1 := norm_triangle _ _).
rewrite norm_opp.
apply Req_le.
ring.
Qed.

Global Instance R_NormedAbelianGroup : NormedAbelianGroup R.
Proof.
  apply (Build_NormedAbelianGroup _ _ (fun x => Rabs x)).
  by apply Rabs_R0.
  move => x ; by apply Rabs_Ropp.
  move => x y ; by apply Rabs_triang.
Defined.

(** * Functional Structures *)

Require Import FunctionalExtensionality Lub.

(** Abelian Group *)

Global Instance AbelianGroup_Fct {T G} :
  AbelianGroup G -> AbelianGroup (T -> G).
Proof.
  intro AG.
  apply (Build_AbelianGroup _ (fun f g => (fun x => plus (f x) (g x)))
         (fun f => (fun x => opp (f x)))
         (fun _ => zero)).
  - move => f g.
    apply functional_extensionality => x.
    by apply plus_comm.
  - move => f g h.
    apply functional_extensionality => x.
    by apply plus_assoc.
  - move => f.
    apply functional_extensionality => x.
    by apply plus_zero_r.
  - move => f.
    apply functional_extensionality => x.
    by apply plus_opp_r.
Defined.

(** Metric Space *)

Lemma UnifFct_dist_ne {T M} {MS : MetricSpace M}
  (f g : T -> M) : exists s : R, s = 0 \/ exists x : T, s = distance (f x) (g x).
Proof.
  exists 0 ; by left.
Qed.

Definition UnifFct_dist {T M} {MS : MetricSpace M}
  (f g : T -> M) : R :=
    Rbar_min 1 (Lub_Rbar_ne _ (UnifFct_dist_ne f g)).

Lemma UnifFct_dist_le_lub {T M} {MS : MetricSpace M} (f g : T -> M) :
  Rbar_le (UnifFct_dist f g) (Lub_Rbar_ne _ (UnifFct_dist_ne f g)).
Proof.
  rewrite /UnifFct_dist /Rbar_min ; case: Rbar_le_dec ; simpl => H.
  by [].
  apply Rbar_not_le_lt in H.
  move: H ; rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ;
  case => [l | | ] ; simpl ; case => ub lub H.
  by right.
  by [].
  apply ub ; by left.
Qed.

Lemma UnifFct_dist_lub_lt_1  {T M} {MS : MetricSpace M}
  (f g : T -> M) (x : R) : x <= 1
    -> ((UnifFct_dist f g) < x <-> Rbar_lt (Lub_Rbar_ne _ (UnifFct_dist_ne f g)) x).
Proof.
  move => Hx.
  rewrite /UnifFct_dist /Rbar_min ; case: Rbar_le_dec ; simpl => H.
  split => H0.
  by apply Rlt_not_le in H0.
  by apply (Rbar_le_lt_trans _ _ _ H H0).
  apply Rbar_not_le_lt in H.
  move: H ; rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ;
  case => [l | | ] ; simpl ; case => ub lub H.
  by split.
  by [].
  case: (ub 0).
  by left.
  by [].
  by [].
Qed.

Lemma UnifFct_dist_ge_fct {T G} {MS : MetricSpace G} :
  forall (f g : T -> G) (x : T), (UnifFct_dist f g) < 1 
    -> distance (f x) (g x) <= UnifFct_dist f g.
Proof.
  move => f g x.
  unfold UnifFct_dist, Rbar_min ; case: Rbar_le_dec ; simpl => H Hfg.
  by apply Rlt_irrefl in Hfg.
  apply Rbar_finite_le.
  apply Rbar_not_le_lt in H.
  case: (Lub_Rbar_ne_correct _ (UnifFct_dist_ne f g)) => ub _.
  case: Lub_Rbar_ne ub H => [l | | ] ; simpl => ub H.
  apply ub.
  right ; by exists x.
  by [].
  case: (ub 0) ; by auto.
Qed.

Lemma UnifFct_dist_maj {T G} {MS : MetricSpace G} :
  forall (f g : T -> G) (M : R), 0 <= M ->
    (forall x, distance (f x) (g x) <= M) -> UnifFct_dist f g <= M.
Proof.
  move => f g M Hm Hfg.
  apply Rbar_finite_le.
  apply Rbar_le_trans with (1 := UnifFct_dist_le_lub f g).
  apply Lub_Rbar_ne_correct.
  move => s ; case => [-> | [x ->]] {s}.
  by apply Rbar_finite_le.
  by apply Rbar_finite_le.
Qed.

Lemma UnifFct_dist_bw_0_1 {T M} {MS : MetricSpace M} (f g : T -> M) :
  0 <= UnifFct_dist f g <= 1.
Proof.
  rewrite /UnifFct_dist /Rbar_min ; case: Rbar_le_dec ; simpl => H.
  split ; [by apply Rle_0_1 | by apply Rle_refl].
  apply Rbar_not_le_lt in H.
  move: H ; rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ;
  case => [l | | ] ; simpl ; case => ub lub H.
  split.
  apply Rbar_finite_le, ub ; by left.
  by apply Rlt_le.
  by [].
  split ; [by apply Rle_refl | by apply Rle_0_1].
Qed.

Lemma UnifFct_dist_refl {T M} {MS : MetricSpace M} (f : T -> M) :
  UnifFct_dist f f = 0.
Proof.
  apply Rle_antisym.
  apply Rbar_finite_le, Rbar_le_trans with (1 := UnifFct_dist_le_lub _ _).
  rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l ; simpl ; case => ub lub.
  apply lub => s ; case => [ -> | [ x -> ]] {s}.
  by right.
  rewrite distance_refl ; by right.
  by apply UnifFct_dist_bw_0_1.
Qed.

Lemma UnifFct_dist_comm {T M} {MS : MetricSpace M} (f g : T -> M) :
  UnifFct_dist f g = UnifFct_dist g f.
Proof.
  rewrite /UnifFct_dist.
  apply f_equal, f_equal.
  apply Lub_Rbar_ne_eqset => s ;
  split ; case => [-> | [x ->]].
  by left.
  right ; exists x ; by apply distance_comm.
  by left.
  right ; exists x ; by apply distance_comm.
Qed.

Lemma UnifFct_dist_triangle {T M} {MS : MetricSpace M} (f g h : T -> M) :
  UnifFct_dist f h <= UnifFct_dist f g + UnifFct_dist g h.
Proof.
  - case: (Rle_lt_dec 1 (UnifFct_dist f g)) => Hfg.
    apply Rle_trans with (2 := Rplus_le_compat_r _ _ _ Hfg).
    apply Rle_trans with 1.
    by apply UnifFct_dist_bw_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by apply UnifFct_dist_bw_0_1.
    move: (fun x => UnifFct_dist_ge_fct f g x Hfg) => {Hfg} Hfg.
  - case: (Rle_lt_dec 1 (UnifFct_dist g h)) => Hgh.
    apply Rle_trans with (2 := Rplus_le_compat_l _ _ _ Hgh).
    apply Rle_trans with 1.
    by apply UnifFct_dist_bw_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by apply UnifFct_dist_bw_0_1.
    move: (fun x => UnifFct_dist_ge_fct g h x Hgh) => {Hgh} Hgh.
    apply UnifFct_dist_maj.
    apply Rplus_le_le_0_compat ;
    by apply UnifFct_dist_bw_0_1.
    move => x.
    apply Rle_trans with (1 := distance_triangle _ (g x) _).
    by apply Rplus_le_compat.
Qed.

Lemma MetricSpace_UnifFct {T M} :
  MetricSpace M -> MetricSpace (T -> M).
Proof.
  intros.
  apply (Build_MetricSpace _ UnifFct_dist).
  + by apply UnifFct_dist_refl.
  + by apply UnifFct_dist_comm.
  + by apply UnifFct_dist_triangle.
Defined.

(** Normed Abelian Group *)

Lemma UnifFct_norm_ne {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G), exists s : R, s = 0 \/ exists x : T, s = norm (f x).
Proof.
  intro f.
  exists 0.
  by left.
Qed.
Definition UnifFct_norm {T G} {NAG : NormedAbelianGroup G} (f : T -> G) : R :=
    Rbar_min 1 (Lub_Rbar_ne _ (UnifFct_norm_ne f)).

Lemma UnifFct_norm_le_lub  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G), Rbar_le (UnifFct_norm f) (Lub_Rbar_ne _ (UnifFct_norm_ne f)).
Proof.
  intro f.
  unfold UnifFct_norm, Rbar_min ;
  case: Rbar_le_dec => H.
  exact H.
  apply Rbar_not_le_lt in H ; revert H.
  unfold Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] ;
  simpl ; intros [ub lub] H.
  by right.
  apply ub ; by left.
  apply ub ; by left.
Qed.

Lemma UnifFct_dist_norm {T G} {NAG : NormedAbelianGroup G} (f g : T -> G) :
  UnifFct_dist f g = UnifFct_norm (minus g f).
Proof.
  apply (f_equal real), f_equal.
  apply Lub_Rbar_ne_eqset.
  by unfold distance.
Qed.

Lemma UnifFct_norm_lub_lt_1  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G) (x : R), x <= 1
    -> ((UnifFct_norm f) < x <-> Rbar_lt (Lub_Rbar_ne _ (UnifFct_norm_ne f)) x).
Proof.
  intros f x.
  unfold UnifFct_norm, Rbar_min ; case Rbar_le_dec ; simpl ; try by auto.
  intros H Hx ; split ; intro H0.
  by apply Rlt_not_le in H0.
  contradict H.
  apply Rbar_lt_not_le, Rbar_lt_le_trans with x.
  by [].
  by apply Rbar_finite_le.

  move/Rbar_not_le_lt.
  rewrite /Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] ;
  simpl ; intros [ub lub] H.
  by split.
  by auto.
  case: (ub 0) ; by auto.
Qed.

Lemma UnifFct_norm_ge_fct  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G) (x : T), (UnifFct_norm f) < 1 -> norm (f x) <= UnifFct_norm f.
Proof.
  intros f x.
  rewrite /UnifFct_norm /Rbar_min ; case: Rbar_le_dec ; simpl ; try by auto.
  move => H H0.
  by apply Rlt_irrefl in H0.

  move/Rbar_not_le_lt.
  rewrite /Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] ; simpl ; intros [ub lub] H H0.
  apply Rbar_finite_le, ub.
  right ; by exists x.
  by auto.
  case: (ub 0) ; by auto.
Qed.

Lemma UnifFct_norm_maj  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G) (M : R), 0 <= M ->
    (forall x, norm (f x) <= M) -> UnifFct_norm f <= M.
Proof.
  intros f M Hm Hf.
  apply Rbar_finite_le.
  apply Rbar_le_trans with (1 := UnifFct_norm_le_lub f).
  apply Lub_Rbar_ne_correct.
  move => s ; case => [-> | [x ->]] {s}.
  by apply Rbar_finite_le.
  by apply Rbar_finite_le.
Qed.

Lemma UnifFct_norm_bw_0_1 {T M} {MNAG : NormedAbelianGroup M} : 
  forall (f : T -> M), 0 <= UnifFct_norm f <= 1.
Proof.
  intro f.
  rewrite /UnifFct_norm /Rbar_min ; case: Rbar_le_dec => H.
  split ; [by apply Rle_0_1 | by right].
  apply Rbar_not_le_lt in H.
  move: H ; rewrite /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ; case => [l | | ] ; simpl ; intros Hlub H.
  split.
  apply Rbar_finite_le, Hlub ; by left.
  by apply Rlt_le.
  by auto.
  split ; [ by right | by apply Rle_0_1 ].
Qed.

Lemma UnifFct_norm_zero {T G} {NAG : NormedAbelianGroup G} :
  @UnifFct_norm T G NAG zero = 0.
Proof.
  replace 0 with (real (Finite 0)) by auto.
  apply (f_equal real).
  replace (Lub_Rbar_ne _ _) with (Finite 0).
  rewrite /Rbar_min ; case: Rbar_le_dec ; simpl ; intros H.
  contradict H ; apply Rbar_lt_not_le.
  by apply Rlt_0_1.
  auto.
  apply sym_eq, is_lub_Rbar_ne_unique ; split.
  - move => s ; simpl => Hs.
    case: Hs => Hs.
    rewrite <- Hs ; by right.
    case: Hs => x -> {s}.
    rewrite norm_zero ; by right.
  - move => b Hb.
    apply Hb.
    by left.
Qed.

Lemma UnifFct_norm_opp  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G), UnifFct_norm (opp f) = UnifFct_norm f.
Proof.
  intro f.
  apply (f_equal (fun x => real (Rbar_min 1 x))).
  apply Lub_Rbar_ne_eqset => s ; split ; simpl ; case => Hs ; try by left.
  case: Hs => x -> {s} ; right ; exists x.
  by apply norm_opp.
  case: Hs => x -> {s} ; right ; exists x.
  by apply sym_equal, norm_opp.
Qed.

Lemma UnifFct_norm_triangle  {T G} {NAG : NormedAbelianGroup G} :
  forall f g : T -> G,
  UnifFct_norm (plus f g) <= UnifFct_norm f + UnifFct_norm g.
Proof.
  move => f g ; simpl.
  - case: (Rle_lt_dec 1 (UnifFct_norm f)) => Hf.
    apply Rle_trans with (2 := Rplus_le_compat_r _ _ _ Hf).
    apply Rle_trans with 1.
    by apply UnifFct_norm_bw_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by apply UnifFct_norm_bw_0_1.
    move: (fun x => UnifFct_norm_ge_fct f x Hf) => {Hf} Hf.
  - case: (Rle_lt_dec 1 (UnifFct_norm g)) => Hg.
    apply Rle_trans with (2 := Rplus_le_compat_l _ _ _ Hg).
    apply Rle_trans with 1.
    by apply UnifFct_norm_bw_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by apply UnifFct_norm_bw_0_1.
    move: (fun x => UnifFct_norm_ge_fct g x Hg) => {Hg} Hg.
    apply UnifFct_norm_maj.
    apply Rplus_le_le_0_compat ;
    by apply UnifFct_norm_bw_0_1.
    move => x.
    apply Rle_trans with (1 := norm_triangle _ _).
    by apply Rplus_le_compat.
Qed.

Lemma NAG_UnifFct {T} {G} :
  NormedAbelianGroup G -> NormedAbelianGroup (T -> G).
Proof.
  move => NAG.
  exists (@AbelianGroup_Fct T G (@nagroup_abelian G NAG)) UnifFct_norm.
  - by apply UnifFct_norm_zero.
  - move => f.
    by apply UnifFct_norm_opp.
  - move => f g.
    by apply UnifFct_norm_triangle.
Defined.

Lemma complete_cauchy_UnifFct {T} : 
  let MS := MetricSpace_UnifFct R_metric in
  forall F : ((T -> R) -> Prop) -> Prop,
  ProperFilter F ->
    (forall eps : posreal, exists x : T -> R, F (ball x eps)) ->
    exists x : T -> R, is_filter_lim F x.
Proof.
  move => MS F FF HFc.
  
  cut (exists f, forall eps : posreal, F (fun g => distance f g < eps)).
    case => f Hf.
    exists f.
    apply is_filter_lim_filterlim.
    by apply FF.
    by apply filterlim_locally.

  set Fr := fun (t : T) (P : R -> Prop) => F (fun g => P (g t)).
  have FFr : forall t, ProperFilter (Fr t).
    case: FF => HF FF t.
    split.
    - move => P Hp.
      case: (HF _ Hp) => f Hf.
      by exists (f t).
    - split.
      + by apply FF.
      + move => P P' Hp Hp'.
      by apply FF.
      + move => P P' Hpp'.
      apply FF.
      move => f ; by apply Hpp'.
  assert (HFrc : forall t, forall eps : posreal, exists x : R, Fr t (ball x eps)).
    move => t eps.
    wlog: eps / (eps < 1) => [Hw | Heps].
      case: (Rlt_le_dec eps 1) => Heps.
      by apply Hw.
      case: (Hw (pos_div_2 (mkposreal _ Rlt_0_1))).
      apply Rlt_div_l.
      by apply Rlt_0_2.
      apply Rminus_lt_0 ; simpl ; ring_simplify ; by apply Rlt_0_1.
      move => x Hx ; exists x ; move: Hx.
      apply FFr => y.
      rewrite /ball ; simpl => H.
      apply Rlt_trans with (1 := H).
      apply Rlt_div_l.
      by apply Rlt_0_2.
      apply Rle_lt_trans with (1 := Heps).
      apply Rminus_lt_0 ; simpl ; ring_simplify ; by apply eps.
    case: (HFc eps) => f Hf.
    exists (f t).
    move: Hf ; apply FF => g.
    rewrite /ball ; simpl => H.
    apply UnifFct_dist_lub_lt_1 in H.
    apply (Rbar_le_lt_trans (distR (f t) (g t)) (Lub_Rbar_ne _ (UnifFct_dist_ne f g)) eps).
      rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l ; simpl => Hl.
      apply Hl.
      right ; by exists t.
      by apply H.
      by apply Rlt_le.
  assert (Hex : forall t, exists x, is_filter_lim (Fr t) x).
    move => t.
    apply: complete_cauchy. apply: (HFrc t).
  assert (forall t, exists! x, is_filter_lim (Fr t) x).
    move => t.
    case: (Hex t) => x Hx.
    exists x.
    split.
    by apply Hx.
    move => x' Hx'.
    suff : ~ x <> x'.
      case: (Req_dec x x') ; by auto.
    move: Hx Hx'.
    apply: is_filter_lim_unique.
    move: H => {Hex} Hex.
  move: (fun t => uniqueness_dec _ (Hex t)) => Hf.
  set f := fun t => projT1 (Hf t) ; exists f.

  move => eps.
  case: (Rlt_le_dec 1 eps) => Heps.
  apply filter_imp with (fun _ => True).
  move => x _.
  apply Rle_lt_trans with (2 := Heps).
  rewrite /distance ; simpl.
  by apply UnifFct_dist_bw_0_1.
  by apply filter_true.

  apply filter_imp with (fun g => forall t, distance (f t) (g t) < pos_div_2 eps).
  move => g Hg.
  unfold distance ; simpl.
  rewrite UnifFct_dist_lub_lt_1.
  apply Rbar_le_lt_trans with (pos_div_2 eps).
  apply Lub_Rbar_ne_correct => s Hs.
  case: Hs => [-> | [t ->]].
  apply Rbar_lt_le, is_pos_div_2.
  apply Rbar_finite_le, Rlt_le, (Hg t).
  apply Rminus_lt_0 ; simpl ; field_simplify ;
  rewrite Rdiv_1 ; by apply is_pos_div_2.
  by [].
  
  have : (pos_div_2 eps <= 1).
    apply Rle_trans with (2 := Heps).
    simpl ; apply Rminus_le_0 ; field_simplify ; rewrite Rdiv_1.
    apply Rlt_le, is_pos_div_2.
  
  move: (pos_div_2 eps) => {eps Heps} eps Heps.
  assert (forall t (eps : posreal), (Fr t) (fun x => distance (f t) x < eps)).
    move =>  t.
    apply filterlim_locally.
    apply is_filter_lim_filterlim.
    by apply FFr.
    apply (projT2 (Hf t)).

  generalize (proj1 cauchy_distance HFc) => {HFc} HFc.

  case: (HFc (pos_div_2 eps)) => {HFc} P ; simpl ; case => HP H0.
  apply filter_imp with (2 := HP).
  move => g Hg t.
  move: (fun h => H0 g h Hg) => {H0} H0.
  move: (H t (pos_div_2 eps)) ; simpl => {H} H.
  unfold Fr in H ; generalize (filter_and _ _ H HP) => {H} H.
  apply filter_ex in H ; case: H => h H.
  apply Rle_lt_trans with (1 := distR_triangle (f t) (h t) (g t)).
  rewrite (double_var eps).
  apply Rplus_lt_compat.
  by apply H.
  move: (H0 _ (proj2 H)) => {H0} H0.
  apply Rle_lt_trans with (2 := H0).
  rewrite distR_comm.
  apply: (UnifFct_dist_ge_fct g h t).
  apply Rlt_le_trans with (1 := H0).
  apply Rle_div_l.
  by apply Rlt_0_2.
  apply Rle_trans with (1 := Heps), Rminus_le_0 ; ring_simplify ; by apply Rle_0_1.
Qed.

Lemma R_CMS_UnifFct {T} : CompleteMetricSpace (T -> R).
Proof.
  intros.
  apply Build_CompleteMetricSpace with (MetricSpace_UnifFct R_metric).
  by apply complete_cauchy_UnifFct.
Defined.

