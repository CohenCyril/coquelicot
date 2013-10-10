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
