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

Require Import Reals List Morphisms ssreflect.
Require Import Rcomplements Rbar Lub.
Require Import FunctionalExtensionality.
Open Scope R_scope.

(** * Algebraic spaces *)
(** ** Abelian Groups *)

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

Global Instance AbelianGroup_prod :
  forall U V,
  AbelianGroup U -> AbelianGroup V
    -> AbelianGroup (U * V).
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

Global Instance AbelianGroup_fct :
  forall T G,
    AbelianGroup G -> AbelianGroup (T -> G).
Proof.
  intros T G AG.
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

(** Arithmetic operations *)

Lemma plus_zero_l :
  forall G (GG : AbelianGroup G) (x : G),
  plus zero x = x.
Proof.
intros G GG x.
now rewrite plus_comm plus_zero_r.
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

(** ** Fields *)

Class Field_mixin (K : Type) (KA : AbelianGroup K) := {
  mult : K -> K -> K ;
  inv : K -> K ;
  one : K ;
  mult_comm : forall x y, mult x y = mult y x ;
  mult_assoc : forall x y z, mult x (mult y z) = mult (mult x y) z ;
  mult_one_r : forall x, mult x one = x ;
  mult_inv_r : forall x, x <> zero -> mult x (inv x) = one ;
  mult_distr_r : forall x y z, mult (plus x y) z = plus (mult x z) (mult y z)
}.
Class Field K := {
  field_group :> AbelianGroup K ;
  field_field :> Field_mixin K field_group
}.

Class AbsField_mixin K (KF : Field K) := {
  Kabs : K -> R ;
  Kabs_zero : Kabs zero = 0 ;
  Kabs_opp_one : Kabs (opp one) = 1 ;
  Kabs_triangle : forall x y, Kabs (plus x y) <= Kabs x + Kabs y ;
  Kabs_mult : forall x y, Kabs (mult x y) = Kabs x * Kabs y
}.
Class AbsField K := {
  absfield_group :> AbelianGroup K ;
  absfield_field :> Field_mixin K absfield_group ;
  absfield_abs :> AbsField_mixin K (Build_Field _ absfield_group absfield_field)
}.

Global Instance AbsField_Field {K} :
  AbsField K -> Field K.
Proof.
  intro MF.
  apply Build_Field with absfield_group.
  by apply MF.
Defined.

(** Arithmetic operations in fields *)

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
rewrite mult_comm mult_assoc (mult_comm x _).
rewrite H.
rewrite mult_comm mult_assoc (mult_comm _ r).
rewrite mult_inv_r; try assumption.
apply mult_one_l.
Qed.

Lemma inv_eq: forall K (FK : Field K) 
  (x y : K), x <> zero -> mult x y = one -> y = inv x.
Proof.
intros K FK x y Hx H.
apply mult_eq_compat_l with (FK:=FK) (r:=x).
assumption.
now rewrite H mult_inv_r.
Qed.

Lemma inv_mult :
  forall K (FK : Field K) (x y : K), mult x y <> zero ->
  inv (mult x y) = mult (inv x) (inv y).
Proof.
intros K FK x y Hxy.
apply sym_eq, inv_eq; try assumption.
rewrite (mult_comm x) mult_assoc.
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

Lemma plus_eq_compat_l: forall K (FK : Field K)
  (r x y: K), plus r x = plus r y -> x = y.
Proof.
intros K FK r x y H.
rewrite <- (plus_zero_l _ _ x).
rewrite <- (plus_opp_l _ _ r).
rewrite <- plus_assoc.
rewrite H.
now rewrite plus_assoc plus_opp_l plus_zero_l.
Qed.


Lemma opp_mult_r: forall K (FK : Field K) (x y: K),
  opp (mult x y) = mult x (opp y).
Proof.
intros K FK x y.
apply plus_eq_compat_l with (FK:=FK) (r:=(mult x y)).
rewrite plus_opp_r.
rewrite <- mult_distr_l.
now rewrite plus_opp_r mult_zero_r.
Qed.


Lemma opp_mult_l: forall K (FK : Field K) (x y: K),
  opp (mult x y) = mult (opp x) y.
Proof.
intros K FK x y.
now rewrite mult_comm opp_mult_r mult_comm.
Qed.

Lemma opp_mult_m1 : forall K (AF : AbsField K) x,
  opp x = mult (opp one) x.
Proof.
  intros K AF x.
  rewrite -(opp_mult_l K (AbsField_Field AF)) opp_mult_r.
  by rewrite mult_one_l.
Qed.

Lemma Kabs_one :
  forall K (AF : AbsField K), Kabs one = 1.
Proof.
  intros K AF.
  rewrite -(Rmult_1_l 1).
  rewrite -Kabs_opp_one -Kabs_mult.
  by rewrite -opp_mult_l opp_mult_r opp_opp mult_one_l.
Qed.

Lemma Kabs_opp :
  forall K (AF : AbsField K) x, Kabs (opp x) = Kabs x.
Proof.
  intros K AF x.
  rewrite opp_mult_m1.
  rewrite Kabs_mult Kabs_opp_one.
  by rewrite Rmult_1_l.
Qed.

Lemma Kabs_pos :
  forall K (AF : AbsField K) x, 0 <= Kabs x.
Proof.
  intros K AF x.
  apply Rmult_le_reg_l with 2.
  by apply Rlt_0_2.
  rewrite Rmult_0_r -Kabs_zero -(plus_opp_l _ _ x).
  apply Rle_trans with (1 := Kabs_triangle _ _).
  rewrite Kabs_opp.
  apply Req_le ; ring.
Qed.

(** ** Vector Spaces *)

Class VectorSpace_mixin V K {FK : Field K} (AG : AbelianGroup V) := {
  scal : K -> V -> V ;
  scal_assoc : forall x y u, scal x (scal y u) = scal (mult x y) u ;
  scal_one : forall u, scal one u = u ;
  scal_distr_l : forall x u v, scal x (plus u v) = plus (scal x u) (scal x v) ;
  scal_distr_r : forall x y u, scal (plus x y) u = plus (scal x u) (scal y u)
}.

Class VectorSpace V K {FK : Field K} := {
  vspace_group :> AbelianGroup V ;
  vspace_mixin :> VectorSpace_mixin V K vspace_group
}.

Global Instance VectorSpace_prod :
  forall U V K (FK : Field K) (VU : VectorSpace U K) (VV : VectorSpace V K),
  VectorSpace (U * V) K.
Proof.
intros U V K FK VU VV.
econstructor.
apply (@Build_VectorSpace_mixin _ K FK (AbelianGroup_prod _ _ _ _)
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

Global Instance VectorSpace_fct :
  forall U V K (FK : Field K) (VV : VectorSpace V K),
  VectorSpace (U -> V) K.
Proof.
intros U V K FK VV.
econstructor.
apply (@Build_VectorSpace_mixin _ K FK (AbelianGroup_fct _ _ _)
  (fun (x : K) (f : U -> V) t => scal x (f t))).
intros x y u.
apply functional_extensionality => t.
apply scal_assoc.
intros u.
apply functional_extensionality => t ; apply scal_one.
intros x u v.
simpl.
apply functional_extensionality => t ; apply scal_distr_l.
intros x y u.
simpl.
apply functional_extensionality => t ; apply scal_distr_r.
Defined.

(** * Filters *)

(** ** Definitions *) 

Class Filter {T : Type} (F : (T -> Prop) -> Prop) := {
  filter_true : F (fun _ => True) ;
  filter_and : forall P Q : T -> Prop, F P -> F Q -> F (fun x => P x /\ Q x) ;
  filter_imp : forall P Q : T -> Prop, (forall x, P x -> Q x) -> F P -> F Q
}.

Class ProperFilter {T : Type} (F : (T -> Prop) -> Prop) := {
  filter_ex : forall P, F P -> exists x, P x ;
  filter_filter :> Filter F
}.

Lemma filter_forall :
  forall {T : Type} {F} {FF: @Filter T F} (P : T -> Prop),
  (forall x, P x) -> F P.
Proof.
intros T F FF P H.
apply filter_imp with (fun _ => True).
easy.
apply filter_true.
Qed.

Lemma filter_const :
  forall {T : Type} {F} {FF: @ProperFilter T F} (P : Prop),
  F (fun _ => P) -> P.
Proof.
intros T F FF P H.
destruct (filter_ex (fun _ => P) H) as [_ H'].
exact H'.
Qed.

(** ** Limits expressed with filters *)

Definition filter_le {T : Type} (F G : (T -> Prop) -> Prop) :=
  forall P, G P -> F P.

Lemma filter_le_refl :
  forall T F, @filter_le T F F.
Proof.
now intros T F P.
Qed.

Lemma filter_le_trans :
  forall T F G H, @filter_le T F G -> filter_le G H -> filter_le F H.
Proof.
intros T F G H FG GH P K.
now apply FG, GH.
Qed.

Definition filtermap {T U : Type} (f : T -> U) (F : (T -> Prop) -> Prop) :=
  fun P => F (fun x => P (f x)).

Global Instance filtermap_filter :
  forall T U (f : T -> U) (F : (T -> Prop) -> Prop),
  Filter F -> Filter (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
constructor.
- apply filter_true.
- intros P Q HP HQ.
  now apply filter_and.
- intros P Q H HP.
  unfold filtermap.
  apply (filter_imp (fun x => P (f x))).
  intros x Hx.
  now apply H.
  exact HP.
Qed.

Global Instance filtermap_proper_filter :
  forall T U (f : T -> U) (F : (T -> Prop) -> Prop),
  ProperFilter F -> ProperFilter (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
split.
- intros P FP.
  destruct (filter_ex _ FP) as [x Hx].
  now exists (f x).
- apply filtermap_filter.
  apply filter_filter.
Qed.

Definition filterlim {T U : Type} (f : T -> U) F G :=
  filter_le (filtermap f F) G.

Lemma filterlim_id :
  forall T (F : (T -> Prop) -> Prop), filterlim (fun x => x) F F.
Proof.
now intros T F P HP.
Qed.

Lemma filterlim_compose :
  forall T U V (f : T -> U) (g : U -> V) F G H,
  filterlim f F G -> filterlim g G H ->
  filterlim (fun x => g (f x)) F H.
Proof.
intros T U V f g F G H FG GH P HP.
apply (FG (fun x => P (g x))).
now apply GH.
Qed.

Lemma filterlim_ext_loc :
  forall {T U F G} {FF : Filter F} (f g : T -> U),
  F (fun x => f x = g x) ->
  filterlim f F G ->
  filterlim g F G.
Proof.
intros T U F G FF f g Efg Lf P GP.
specialize (Lf P GP).
generalize (filter_and _ _ Efg Lf).
unfold filtermap.
apply filter_imp.
now intros x [-> H].
Qed.

Lemma filterlim_ext :
  forall {T U F G} {FF : Filter F} (f g : T -> U),
  (forall x, f x = g x) ->
  filterlim f F G ->
  filterlim g F G.
Proof.
intros T U F G FF f g Efg.
apply filterlim_ext_loc.
now apply filter_forall.
Qed.

(** ** Specific filters *)

(** Filters for pairs *)

Inductive filter_prod {T U : Type} (F G : _ -> Prop) (P : T * U -> Prop) : Prop :=
  Filter_prod (Q : T -> Prop) (R : U -> Prop) :
    F Q -> G R -> (forall x y, Q x -> R y -> P (x, y)) -> filter_prod F G P.

Global Instance filter_prod_filter :
  forall T U (F : (T -> Prop) -> Prop) (G : (U -> Prop) -> Prop),
  Filter F -> Filter G -> Filter (filter_prod F G).
Proof.
intros T U F G FF FG.
constructor.
- exists (fun _ => True) (fun _ => True).
  apply filter_true.
  apply filter_true.
  easy.
- intros P Q [AP BP P1 P2 P3] [AQ BQ Q1 Q2 Q3].
  exists (fun x => AP x /\ AQ x) (fun x => BP x /\ BQ x).
  now apply filter_and.
  now apply filter_and.
  intros x y [Px Qx] [Py Qy].
  split.
  now apply P3.
  now apply Q3.
- intros P Q HI [AP BP P1 P2 P3].
  exists AP BP ; try easy.
  intros x y Hx Hy.
  apply HI.
  now apply P3.
Qed.

Lemma filterlim_fst :
  forall {T U F G} {FG : Filter G},
  filterlim (@fst T U) (filter_prod F G) F.
Proof.
intros T U F G FG P HP.
exists P (fun _ => True) ; try easy.
apply filter_true.
Qed.

Lemma filterlim_snd :
  forall {T U F G} {FF : Filter F},
  filterlim (@snd T U) (filter_prod F G) G.
Proof.
intros T U F G FF P HP.
exists (fun _ => True) P ; try easy.
apply filter_true.
Qed.

Lemma filterlim_pair :
  forall {T U V F G H} {FF : Filter F},
  forall (f : T -> U) (g : T -> V),
  filterlim f F G ->
  filterlim g F H ->
  filterlim (fun x => (f x, g x)) F (filter_prod G H).
Proof.
intros T U V F G H FF f g Cf Cg P [A B GA HB HP].
unfold filtermap.
apply (filter_imp (fun x => A (f x) /\ B (g x))).
intros x [Af Bg].
now apply HP.
apply filter_and.
now apply Cf.
now apply Cg.
Qed.

Lemma filterlim_compose_2 :
  forall {T U V W F G H I} {FF : Filter F},
  forall (f : T -> U) (g : T -> V) (h : U -> V -> W),
  filterlim f F G ->
  filterlim g F H ->
  filterlim (fun x => h (fst x) (snd x)) (filter_prod G H) I ->
  filterlim (fun x => h (f x) (g x)) F I.
Proof.
intros T U V W F G H I FF f g h Cf Cg Ch.
change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))).
apply: filterlim_compose Ch.
now apply filterlim_pair.
Qed.

(** Restriction of a filter to a domain *)

Definition within {T : Type} D (F : (T -> Prop) -> Prop) (P : T -> Prop) :=
  F (fun x => D x -> P x).

Global Instance within_filter :
  forall T D F, Filter F -> Filter (@within T D F).
Proof.
intros T D F FF.
unfold within.
constructor.
- now apply filter_forall.
- intros P Q WP WQ.
  apply filter_imp with (fun x => (D x -> P x) /\ (D x -> Q x)).
  intros x [HP HQ] HD.
  split.
  now apply HP.
  now apply HQ.
  now apply filter_and.
- intros P Q H FP.
  apply filter_imp with (fun x => (D x -> P x) /\ (P x -> Q x)).
  intros x [H1 H2] HD.
  apply H2, H1, HD.
  apply filter_and.
  exact FP.
  now apply filter_forall.
Qed.

Lemma filterlim_within_ext :
  forall {T U F G} {FF : Filter F} D (f g : T -> U),
  (forall x, D x -> f x = g x) ->
  filterlim f (within D F) G ->
  filterlim g (within D F) G.
Proof.
intros T U F G FF D f g Efg.
apply filterlim_ext_loc.
unfold within.
now apply filter_forall.
Qed.

(** * Metric Spaces *)

Class MetricSpace T := {
  distance : T -> T -> R ;
  distance_refl : forall a, distance a a = 0 ;
  distance_comm : forall a b, distance a b = distance b a ;
  distance_triangle : forall a b c, distance a c <= distance a b + distance b c
}.

Lemma distance_ge_0 :
  forall {T} {MT : MetricSpace T} (a b : T),
  0 <= distance a b.
Proof.
intros T MT a b.
apply Rmult_le_reg_l with 2.
apply Rlt_0_2.
rewrite Rmult_0_r.
rewrite -(distance_refl a).
rewrite Rmult_plus_distr_r Rmult_1_l.
rewrite -> (distance_comm a b) at 2.
apply distance_triangle.
Qed.

(** A metric space is a topological space *)

Class MetricBall M := {
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : posreal), ball x e x ;
  ball_sym : forall x y e, ball x e y -> ball y e x ;
  ball_triangle : forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z ;
  ball_le : forall x e1 e2, e1 <= e2 -> forall y, ball x e1 y -> ball x e2 y
}.

Global Instance metric_ball {T} {MT : MetricSpace T} :
  MetricBall T.
Proof.
  exists (fun x eps y => distance x y < eps).
  + move => x eps.
    rewrite distance_refl.
    by apply eps.
  + move => x y e H.
    by rewrite distance_comm.
  + move => x y z e1 e2 Hxy Hyz.
    apply Rle_lt_trans with (1 := distance_triangle _ y _).
    by apply Rplus_lt_compat.
  + move => x e1 e2 He y H.
    apply Rlt_le_trans with (2 := He).
    by apply H.
Defined.

Definition locally_dist {T : Type} (d : T -> R) (P : T -> Prop) :=
  exists delta : posreal, forall y, d y < delta -> P y.

Global Instance locally_dist_filter :
  forall T (d : T -> R), Filter (locally_dist d).
Proof.
intros T d.
constructor.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy.
  split.
  apply HP.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

Definition locally {T} {MT : MetricBall T} (x : T) (P : T -> Prop) :=
  exists eps : posreal, forall y, ball x eps y -> P y.
Definition locally' {T} {MT : MetricBall T} (x : T) (P : T -> Prop) :=
  exists eps : posreal, forall y, ball x eps y -> y <> x -> P y.

Global Instance locally_filter :
  forall {T} {MT : MetricBall T} (x : T), ProperFilter (locally x).
Proof.
intros T MT x.
constructor ; [idtac|constructor].
- intros P [eps H].
  exists x.
  apply H.
  apply ball_center.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy.
  split.
  apply HP.
  apply ball_le with (2 := Hy).
  apply Rmin_l.
  apply HQ.
  apply ball_le with (2 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

Lemma filterlim_locally :
  forall {T U} {MU : MetricBall U} {F} {FF : Filter F} (f : T -> U) y,
  filterlim f F (locally y) <->
  forall eps : posreal, F (fun x => ball y eps (f x)).
Proof.
intros T U MU F FF f y.
split.
- intros Cf eps.
  apply (Cf (fun x => ball y eps x)).
  now exists eps.
- intros Cf P [eps He].
  apply: filter_imp (Cf eps).
  intros t.
  apply He.
Qed.

Lemma locally_locally :
  forall {T} {MT : MetricBall T} x (P : T -> Prop),
  locally x P -> locally x (fun y => locally y P).
Proof.
intros T MT x P [dp Hp].
exists (pos_div_2 dp).
intros y Hy.
exists (pos_div_2 dp) => /= z Hz.
apply Hp.
rewrite (double_var dp).
now apply ball_triangle with y.
Qed.

Lemma locally_singleton :
  forall {T} {MT : MetricBall T} x (P : T -> Prop),
  locally x P -> P x.
Proof.
intros T MT x P [dp H].
apply H.
by apply ball_center.
Qed.

Global Instance locally'_filter :
  forall T (MT : MetricSpace T) (x : T), Filter (locally' x).
Proof.
intros T MT x.
constructor.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy Hy'.
  split.
  apply HP with (2 := Hy').
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ with (2 := Hy').
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy Hy'.
  apply H.
  now apply HP.
Qed.

Lemma filterlim_locally_unique: forall {T U} {MU : MetricSpace U} {F} {FF: ProperFilter F}
  (f:T -> U) l l', filterlim f F (locally l) ->  filterlim f F (locally l') -> distance l l' = 0.
Proof.
intros T U MU F FF f l l' Hl Hl'.
destruct (Rle_lt_or_eq_dec 0 (distance l l')); try easy.
apply distance_ge_0.
exfalso.
assert (M:0 < distance l l' / 2).
apply Rdiv_lt_0_compat.
assumption.
apply Rlt_R0_R2.
assert (H:locally l (fun x => distance l x < distance l l' / 2)).
now exists (mkposreal _ M).
assert (locally l' (fun x => distance l' x < distance l l' / 2)).
now exists (mkposreal _ M).
specialize (Hl _ H).
specialize (Hl' _ H0).
unfold filtermap in Hl, Hl'.
apply filter_const.
generalize (filter_and _ _ Hl Hl').
apply filter_imp.
intros x (H1,H2).
apply (Rlt_irrefl (distance l l')).
apply Rle_lt_trans with (1:=distance_triangle _ (f x) _).
rewrite (double_var (distance l l')).
apply Rplus_lt_compat.
assumption.
now rewrite distance_comm.
Qed.

(** ** Open sets in metric spaces *)

Definition open {T} {MT : MetricBall T} (D : T -> Prop) :=
  forall x, D x -> locally x D.

Lemma open_ext :
  forall {T} {MT : MetricBall T} (D E : T -> Prop),
  (forall x, D x <-> E x) ->
  open D -> open E.
Proof.
intros T MT D E H OD x Ex.
generalize (OD x (proj2 (H x) Ex)).
apply filter_imp.
intros y.
apply H.
Qed.

Lemma open_and :
  forall {T} {MT : MetricBall T} (D E : T -> Prop),
  open D -> open E ->
  open (fun x => D x /\ E x).
Proof.
intros T MT D E OD OE x [Dx Ex].
apply filter_and.
now apply OD.
now apply OE.
Qed.

Lemma open_or :
  forall {T} {MT : MetricBall T} (D E : T -> Prop),
  open D -> open E ->
  open (fun x => D x \/ E x).
Proof.
intros T MT D E OD OE x [Dx|Ex].
generalize (OD x Dx).
apply filter_imp.
intros y Dy.
now left.
generalize (OE x Ex).
apply filter_imp.
intros y Ey.
now right.
Qed.

Lemma open_true :
  forall {T} {MT : MetricBall T},
  open (fun x : T => True).
Proof.
intros T MT x _.
apply filter_true.
Qed.

Lemma open_false :
  forall {T} {MT : MetricBall T},
  open (fun x : T => False).
Proof.
now intros T MT x Hx.
Qed.

(** ** Products of metric spaces *)

Fixpoint Tn (n : nat) (T : Type) : Type :=
  match n with
  | O => unit
  | S n => prod T (Tn n T)
  end.

Fixpoint Fn (n : nat) (T U : Type) : Type :=
  match n with
  | O => U
  | S n => T -> Fn n T U
  end.

Definition dist_prod {T U : Type} (dT : T -> T -> R) (dU : U -> U -> R) (x y : T * U) :=
  Rmax (dT (fst x) (fst y)) (dU (snd x) (snd y)).

Lemma dist_prod_refl :
  forall {T U} {MT : MetricSpace T} {MU : MetricSpace U} (x : T * U),
  dist_prod distance distance x x = 0.
Proof.
intros T U MT MU [xt xu].
unfold dist_prod.
apply Rmax_case ; apply distance_refl.
Qed.

Lemma dist_prod_comm :
  forall {T U} {MT : MetricSpace T} {MU : MetricSpace U} (x y : T * U),
  dist_prod distance distance x y = dist_prod distance distance y x.
Proof.
intros T U MT MU [xt xu] [yt yu].
unfold dist_prod.
rewrite distance_comm.
apply f_equal.
apply distance_comm.
Qed.

Lemma dist_prod_triangle :
  forall {T U} {MT : MetricSpace T} {MU : MetricSpace U} (x y z : T * U),
  dist_prod distance distance x z <= dist_prod distance distance x y + dist_prod distance distance y z.
Proof.
intros T U MT MU [xt xu] [yt yu] [zt zu].
unfold dist_prod.
apply Rmax_case.
apply Rle_trans with (distance xt yt + distance yt zt).
apply distance_triangle.
apply Rplus_le_compat ; apply Rmax_l.
apply Rle_trans with (distance xu yu + distance yu zu).
apply distance_triangle.
apply Rplus_le_compat ; apply Rmax_r.
Qed.

Global Instance prod_metric :
  forall T U, MetricSpace T -> MetricSpace U -> MetricSpace (T * U).
Proof.
intros T U MT MU.
apply (Build_MetricSpace _ (dist_prod distance distance)).
- exact dist_prod_refl.
- exact dist_prod_comm.
- exact dist_prod_triangle.
Defined.

Fixpoint dist_pow (n : nat) (T : Type) (d : T -> T -> R) : Tn n T -> Tn n T -> R :=
  match n with
  | O => fun _ _ => 0
  | S n => fun x y =>
    Rmax (d (fst x) (fst y)) (dist_pow n T d (snd x) (snd y))
  end.

Lemma dist_pow_refl :
  forall {T} {MT : MetricSpace T} n x,
  dist_pow n T distance x x = 0.
Proof.
induction n.
reflexivity.
intros [x xn].
simpl.
rewrite distance_refl IHn.
now apply Rmax_case.
Qed.

Lemma dist_pow_comm :
  forall {T} {MT : MetricSpace T} n x y,
  dist_pow n T distance x y = dist_pow n T distance y x.
Proof.
induction n.
reflexivity.
intros [x xn] [y yn].
simpl.
now rewrite distance_comm IHn.
Qed.

Lemma dist_pow_triangle :
  forall {T} {MT : MetricSpace T} n x y z,
  dist_pow n T distance x z <= dist_pow n T distance x y +  dist_pow n T distance y z.
Proof.
induction n.
simpl.
intros _ _ _.
rewrite Rplus_0_r.
apply Rle_refl.
intros [x xn] [y yn] [z zn].
simpl.
apply Rmax_case.
apply Rle_trans with (1 := distance_triangle x y z).
apply Rplus_le_compat ; apply Rmax_l.
apply Rle_trans with (1 := IHn xn yn zn).
apply Rplus_le_compat ; apply Rmax_r.
Qed.

Global Instance pow_metric : forall T, MetricSpace T -> forall n, MetricSpace (Tn n T).
Proof.
intros T MT n.
apply (Build_MetricSpace _ (dist_pow n T distance)).
- exact (dist_pow_refl n).
- exact (dist_pow_comm n).
- exact (dist_pow_triangle n).
Defined.

(** ** Functional metric spaces *)

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

(** ** Complete metric spaces *)

Class CompleteSpace_mixin T (MT : MetricBall T) := {
  cauchy := fun (F : (T -> Prop) -> Prop) => forall eps : posreal, exists x, F (ball x eps) ;
  complete_cauchy : forall F, ProperFilter F -> cauchy F -> {x : T | forall eps : posreal, F (ball x eps)}
}.

Class CompleteSpace T := {
  complete_metric :> MetricBall T ;
  complete_mixin :> CompleteSpace_mixin T complete_metric
}.

Global Instance MetricBall_fct {T M} :
  MetricBall M -> MetricBall (T -> M).
Proof.
  intros MM.
  exists (fun f eps g => forall t, ball (f t) eps (g t)).
  + intros x e t.
    exact: ball_center.
  + intros x y e H t.
    by apply ball_sym.
  + intros x y z e1 e2 H1 H2 t.
    now apply ball_triangle with (y t).
  + intros x e1 e2 He y H t.
    now apply ball_le with e1.
Defined.

Lemma cauchy_distance :
  forall {T} {MT : MetricBall T} {F} {FF : ProperFilter F},
  (forall eps : posreal, exists x, F (ball x eps)) <->
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball u eps v).
Proof.
  intros T MT F FF.
  split.

  intros H eps.
  case: (H (pos_div_2 eps)) => {H} x Hx.
  exists (ball x (pos_div_2 eps)).
  split.
  by [].
  move => u v Hu Hv.
  rewrite (double_var eps).
  apply ball_triangle with x.
  by apply ball_sym.
  exact Hv.

  intros H eps.
  case: (H eps) => {H} P [HP H].
  destruct (filter_ex P HP) as [x Hx].
  exists x.
  move: (fun v => H x v Hx) => {H} H.
  apply filter_imp with (1 := H).
  by [].
Qed.

Lemma filterlim_locally_cauchy :
  forall {T U} {CU : CompleteSpace U} {F} {FF : ProperFilter F} (f : T -> U),
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball (f u) eps (f v)) <->
  exists y, filterlim f F (fun P => exists eps : posreal, forall x, ball y eps x -> P x).
Proof.
intros T U CU F FF f.
split.
- intros H.
  destruct (complete_cauchy (filtermap f F)) as [y Hy].
  + now apply filtermap_proper_filter.
  + intros eps.
    destruct (H eps) as [P [FP H']].
    destruct (filter_ex _ FP) as [x Hx].
    exists (f x).
    unfold filtermap.
    generalize FP.
    apply filter_imp.
    intros x' Hx'.
    now apply H'.
  + exists y.
    intros P [eps HP].
    refine (_ (Hy eps)).
    unfold filtermap.
    apply filter_imp.
    intros x Hx.
    now apply HP.
- intros [y Hy] eps.
  exists (fun x => ball y (pos_div_2 eps) (f x)).
  split.
  apply Hy.
  now exists (pos_div_2 eps).
  intros u v Hu Hv.
  rewrite (double_var eps).
  apply ball_triangle with y.
  apply ball_sym.
  exact Hu.
  exact Hv.
Qed.

Lemma complete_cauchy_fct {T U} {CMS : CompleteSpace U} : 
  forall F : ((T -> U) -> Prop) -> Prop,
  ProperFilter F ->
    (forall eps : posreal, exists f : T -> U, F (ball f eps)) ->
    {f : T -> U | forall eps : posreal, F (ball f eps)}.
Proof.
  move => F FF HFc.
  
  set Fr := fun (t : T) (P : U -> Prop) => F (fun g => P (g t)).
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
  assert (HFrc : forall t, forall eps : posreal, exists x : U, Fr t (ball x eps)).
    move => t eps.
    case: (HFc eps) => f Hf.
    exists (f t).
    move: Hf ; apply FF => g.
    by [].
  assert (Hex : forall t, {x | forall eps : posreal, Fr t (ball x eps)}).
    move => t.
    by apply complete_cauchy.
  set f := fun t => projT1 (Hex t) ; exists f.

  move => eps.

  assert (forall t (eps : posreal), (Fr t) (fun x => ball (f t) eps x)).
    move => t.
    apply (projT2 (Hex t)).

  generalize (proj1 cauchy_distance HFc) => {HFc} HFc.

  case: (HFc (pos_div_2 eps)) => {HFc} P ; simpl ; case => HP H0.
  apply filter_imp with (2 := HP).
  move => g Hg t.
  move: (fun h => H0 g h Hg) => {H0} H0.
  move: (H t (pos_div_2 eps)) ; simpl => {H} H.
  unfold Fr in H ; generalize (filter_and _ _ H HP) => {H} H.
  apply filter_ex in H ; case: H => h H.
  rewrite (double_var eps).
  apply ball_triangle with (h t).
  by apply H.
  apply ball_sym, H0.
  by apply H.
Qed.

Global Instance CompleteSpace_fct {T U} : 
  CompleteSpace U -> CompleteSpace (T -> U).
Proof.
  intros.
  apply Build_CompleteSpace with (@MetricBall_fct T _ complete_metric).
  constructor.
  apply complete_cauchy_fct.
Defined.

Class MetricField K := {
  mfield_group :> AbelianGroup K ;
  mfield_field :> Field_mixin K mfield_group ;
  mfield_metric :> MetricSpace K
}.

Global Instance MetricField_Field {K} :
  MetricField K -> Field K.
Proof.
  intro MF.
  apply Build_Field with mfield_group.
  by apply MF.
Defined.

(** ** Metric Vector Spaces *)

Class MetricVectorSpace V K {FK : Field K} := {
  mvspace_vector :> VectorSpace V K ;
  mvspace_metric :> MetricSpace V ;
  mvspace_plus : forall x y, filterlim (fun z : V * V => plus (fst z) (snd z)) (filter_prod (locally x) (locally y)) (locally (plus x y)) ;
  mvspace_scal : forall x y, filterlim (fun z : V => scal x z) (locally y) (locally (scal x y))
}.

Global Instance vspace_of_field :
  forall K (FK : Field K), VectorSpace K K.
Proof.
intros K FK.
econstructor.
apply (@Build_VectorSpace_mixin K K FK field_group mult).
apply mult_assoc.
apply mult_one_l.
apply mult_distr_l.
apply mult_distr_r.
Defined.

Lemma scal_zero_r :
  forall V K (FK : Field K) (VV : VectorSpace V K) (x : K),
  (@scal V K FK _ _) x zero = zero.
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

(** * Normed Abelian Space *)

Class NormedAbelianGroup_mixin G (AG : AbelianGroup G) := {
  pnorm : G -> R ;
  pnorm_zero : pnorm zero = 0 ;
  pnorm_opp : forall x, pnorm (opp x) = pnorm x ;
  pnorm_triangle : forall x y, pnorm (plus x y) <= pnorm x + pnorm y
}.

Class NormedAbelianGroup G := {
  nagroup_abelian :> AbelianGroup G ;
  nagroup_mixin :> NormedAbelianGroup_mixin G nagroup_abelian
}.

Lemma pnorm_ge_0 :
  forall {G} {NG : NormedAbelianGroup G} (x : G),
  0 <= pnorm x.
Proof.
intros G NG x.
apply Rmult_le_reg_r with (1 := Rlt_R0_R2).
rewrite Rmult_0_l -pnorm_zero -(plus_opp_r x).
apply Rle_trans with (1 := pnorm_triangle _ _).
rewrite pnorm_opp.
apply Req_le.
ring.
Qed.

Lemma NAG_dist_refl {G} {NAG : NormedAbelianGroup G} :
  forall a : G, pnorm (minus a a) = 0.
Proof.
  move => a.
  by rewrite /minus plus_opp_r pnorm_zero.
Qed.
Lemma NAG_dist_comm {G} {NAG : NormedAbelianGroup G} :
  forall a b : G, pnorm (minus b a) = pnorm (minus a b).
Proof.
  move => a b.
  by rewrite /minus -pnorm_opp opp_plus opp_opp plus_comm.
Qed.
Lemma NAG_dist_triangle {G} {NAG : NormedAbelianGroup G} :
  forall a b c : G, pnorm (minus c a) <= pnorm (minus b a) + pnorm (minus c b).
Proof.
  move => a b c.
  apply Rle_trans with (2 := pnorm_triangle _ _).
  apply Req_le.
  rewrite plus_comm.
  unfold minus.
  rewrite plus_assoc -(plus_assoc c) plus_opp_l plus_zero_r.
  reflexivity.
Qed.

Global Instance NormedAbelianGroup_MetricSpace {G : Type} :
  NormedAbelianGroup G -> MetricSpace G.
Proof.
  intro NAG.
  apply Build_MetricSpace with (fun x y => pnorm (minus y x)).
  - by apply NAG_dist_refl.
  - by apply NAG_dist_comm.
  - by apply NAG_dist_triangle.
Defined.

Class CompleteNormedAbelianGroup T := {
  cnagroup_abelian :> AbelianGroup T ;
  cnagroup_pnormed :> NormedAbelianGroup_mixin T cnagroup_abelian ;
  cnagroup_nag := Build_NormedAbelianGroup T cnagroup_abelian cnagroup_pnormed ;
  cnagroup_complete :> CompleteSpace_mixin T _
}.

Global Instance CompleteNormedAbelianGroup_NormedAbelianGroup {U} :
  CompleteNormedAbelianGroup U -> NormedAbelianGroup U.
Proof.
  case ; intros.
  econstructor.
  exact cnagroup_pnormed0.
Defined.

Global Instance CompleteNormedAbelianGroup_CompleteSpace {U} :
  CompleteNormedAbelianGroup U -> CompleteSpace U.
Proof.
  case ; intros.
  econstructor.
  exact cnagroup_complete0.
Defined.

(** ** Functional Normed Abelian Groups *)

Lemma UnifFct_pnorm_ne {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G), exists s : R, s = 0 \/ exists x : T, s = pnorm (f x).
Proof.
  intro f.
  exists 0.
  by left.
Qed.
Definition UnifFct_pnorm {T G} {NAG : NormedAbelianGroup G} (f : T -> G) : R :=
    Rbar_min 1 (Lub_Rbar_ne _ (UnifFct_pnorm_ne f)).

Lemma UnifFct_pnorm_le_lub  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G), Rbar_le (UnifFct_pnorm f) (Lub_Rbar_ne _ (UnifFct_pnorm_ne f)).
Proof.
  intro f.
  unfold UnifFct_pnorm, Rbar_min ;
  case: Rbar_le_dec => H.
  exact H.
  apply Rbar_not_le_lt in H ; revert H.
  unfold Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] ;
  simpl ; intros [ub lub] H.
  by right.
  apply ub ; by left.
  apply ub ; by left.
Qed.

Lemma UnifFct_dist_pnorm {T G} {NAG : NormedAbelianGroup G} (f g : T -> G) :
  UnifFct_dist f g = UnifFct_pnorm (minus g f).
Proof.
  apply (f_equal real), f_equal.
  apply Lub_Rbar_ne_eqset.
  by unfold distance.
Qed.

Lemma UnifFct_pnorm_lub_lt_1  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G) (x : R), x <= 1
    -> ((UnifFct_pnorm f) < x <-> Rbar_lt (Lub_Rbar_ne _ (UnifFct_pnorm_ne f)) x).
Proof.
  intros f x.
  unfold UnifFct_pnorm, Rbar_min ; case Rbar_le_dec ; simpl ; try by auto.
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

Lemma UnifFct_pnorm_ge_fct  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G) (x : T), (UnifFct_pnorm f) < 1 -> pnorm (f x) <= UnifFct_pnorm f.
Proof.
  intros f x.
  rewrite /UnifFct_pnorm /Rbar_min ; case: Rbar_le_dec ; simpl ; try by auto.
  move => H H0.
  by apply Rlt_irrefl in H0.

  move/Rbar_not_le_lt.
  rewrite /Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] ; simpl ; intros [ub lub] H H0.
  apply Rbar_finite_le, ub.
  right ; by exists x.
  by auto.
  case: (ub 0) ; by auto.
Qed.

Lemma UnifFct_pnorm_maj  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G) (M : R), 0 <= M ->
    (forall x, pnorm (f x) <= M) -> UnifFct_pnorm f <= M.
Proof.
  intros f M Hm Hf.
  apply Rbar_finite_le.
  apply Rbar_le_trans with (1 := UnifFct_pnorm_le_lub f).
  apply Lub_Rbar_ne_correct.
  move => s ; case => [-> | [x ->]] {s}.
  by apply Rbar_finite_le.
  by apply Rbar_finite_le.
Qed.

Lemma UnifFct_pnorm_bw_0_1 {T M} {MNAG : NormedAbelianGroup M} : 
  forall (f : T -> M), 0 <= UnifFct_pnorm f <= 1.
Proof.
  intro f.
  rewrite /UnifFct_pnorm /Rbar_min ; case: Rbar_le_dec => H.
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

Lemma UnifFct_pnorm_zero {T G} {NAG : NormedAbelianGroup G} :
  @UnifFct_pnorm T G NAG zero = 0.
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
    rewrite pnorm_zero ; by right.
  - move => b Hb.
    apply Hb.
    by left.
Qed.

Lemma UnifFct_pnorm_opp  {T G} {NAG : NormedAbelianGroup G} :
  forall (f : T -> G), UnifFct_pnorm (opp f) = UnifFct_pnorm f.
Proof.
  intro f.
  apply (f_equal (fun x => real (Rbar_min 1 x))).
  apply Lub_Rbar_ne_eqset => s ; split ; simpl ; case => Hs ; try by left.
  case: Hs => x -> {s} ; right ; exists x.
  by apply pnorm_opp.
  case: Hs => x -> {s} ; right ; exists x.
  by apply sym_equal, pnorm_opp.
Qed.

Lemma UnifFct_pnorm_triangle  {T G} {NAG : NormedAbelianGroup G} :
  forall f g : T -> G,
  UnifFct_pnorm (plus f g) <= UnifFct_pnorm f + UnifFct_pnorm g.
Proof.
  move => f g ; simpl.
  - case: (Rle_lt_dec 1 (UnifFct_pnorm f)) => Hf.
    apply Rle_trans with (2 := Rplus_le_compat_r _ _ _ Hf).
    apply Rle_trans with 1.
    by apply UnifFct_pnorm_bw_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by apply UnifFct_pnorm_bw_0_1.
    move: (fun x => UnifFct_pnorm_ge_fct f x Hf) => {Hf} Hf.
  - case: (Rle_lt_dec 1 (UnifFct_pnorm g)) => Hg.
    apply Rle_trans with (2 := Rplus_le_compat_l _ _ _ Hg).
    apply Rle_trans with 1.
    by apply UnifFct_pnorm_bw_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by apply UnifFct_pnorm_bw_0_1.
    move: (fun x => UnifFct_pnorm_ge_fct g x Hg) => {Hg} Hg.
    apply UnifFct_pnorm_maj.
    apply Rplus_le_le_0_compat ;
    by apply UnifFct_pnorm_bw_0_1.
    move => x.
    apply Rle_trans with (1 := pnorm_triangle _ _).
    by apply Rplus_le_compat.
Qed.

Lemma NAG_UnifFct {T} {G} :
  NormedAbelianGroup G -> NormedAbelianGroup (T -> G).
Proof.
  move => NAG.
  exists (@AbelianGroup_fct T G (@nagroup_abelian G NAG)).
  exists UnifFct_pnorm.
  - by apply UnifFct_pnorm_zero.
  - move => f.
    by apply UnifFct_pnorm_opp.
  - move => f g.
    by apply UnifFct_pnorm_triangle.
Defined.

(*
Lemma CompleteNormedAbelianGroup_UnifFct {T U} :
  CompleteNormedAbelianGroup U -> CompleteNormedAbelianGroup (T -> U).
Proof.
  case ; intros.
  set (nagf := @NAG_UnifFct T U cnagroup_nag0).
  unfold NAG_UnifFct in nagf.
  exists (AbelianGroup_fct _ _ cnagroup_abelian0) (@nagroup_mixin _ nagf).
  constructor.
  intros F FF H'.
  assert (H := @complete_cauchy_UnifFct T U (Build_CompleteSpace U (@NormedAbelianGroup_MetricSpace U cnagroup_nag0) cnagroup_complete0) F FF).
  destruct H as [f Ff].
  intros eps.
  destruct (H' eps) as [f Hf].
  exists f.
  apply: filter_imp Hf.
  intros x.
  by rewrite /ball /distance /= UnifFct_dist_pnorm.
  exists f.
  intros P [c [eps BP]] Pf.
  apply Ff.
  exists c, eps.
  intros y.
  rewrite -BP.
  by rewrite /ball /distance /= UnifFct_dist_pnorm.
  exact Pf.
Defined.
*)

(** * Normed Vector Space *)

Class NormedVectorSpace_mixin V K {FK : AbsField K} (VS : VectorSpace V K) := {
  norm : V -> R ;
  norm_triangle : forall (x y : V), norm (plus x y) <= norm x + norm y ;
  norm_scal : forall (l : K) (x : V), norm (scal l x) = Kabs l * norm x
}.

Class NormedVectorSpace V K {FK : AbsField K} := {
  cmvspace_vector :> VectorSpace V K ;
  cmvspace_norm :> NormedVectorSpace_mixin V K cmvspace_vector
}.

Lemma norm_zero :
  forall V K (FK : AbsField K) (NVS : NormedVectorSpace V K),
  norm zero = 0.
Proof.
  intros V K FK NVS.
  rewrite -(scal_zero_r V K _ _ zero) norm_scal Kabs_zero.
  exact: Rmult_0_l.
Qed.

Global Instance Field_VectorSpace :
  forall K (F : Field K), VectorSpace K K.
Proof.
  move => K F.
  econstructor.
  apply Build_VectorSpace_mixin with mult.
  exact mult_assoc.
  exact: mult_one_l.
  exact: mult_distr_l.
  exact: mult_distr_r.
Defined.

Lemma AbsField_NormedVectorSpace_mixin :
  forall (K : Type) (AF : AbsField K),
  NormedVectorSpace_mixin K K (Field_VectorSpace K (AbsField_Field AF)).
Proof.
  intros K AF.
  apply Build_NormedVectorSpace_mixin with Kabs.
  exact Kabs_triangle.
  exact Kabs_mult.
Defined.
Global Instance AbsField_NormedVectorSpace :
  forall K (AF : AbsField K), NormedVectorSpace K K.
Proof.
  move => K AF.
  apply Build_NormedVectorSpace with (Field_VectorSpace _ _).
  exact: AbsField_NormedVectorSpace_mixin.
Defined.

Global Instance Normed_Metric_VectorSpace :
  forall V K (FK : AbsField K),
  NormedVectorSpace V K -> MetricSpace V.
Proof.
  intros V K FK NVS.
  apply Build_MetricSpace with (fun x y => norm (minus y x)).
  + move => a.
    by rewrite /minus plus_opp_r norm_zero.
  + move => a b.
    rewrite /minus.
    rewrite -{1}(opp_opp b) -opp_plus -scal_opp_one.
    rewrite norm_scal.
    rewrite Kabs_opp_one Rmult_1_l.
    by rewrite plus_comm.
  + move => a b c.
    replace (minus c a) with (plus (minus b a) (minus c b)).
    by apply norm_triangle.
    rewrite plus_comm /minus.
    rewrite -?plus_assoc.
    apply f_equal.
    by rewrite plus_assoc plus_opp_l plus_zero_l.
Defined.

(** * The topology on natural numbers *)

Definition eventually (P : nat -> Prop) :=
  exists N : nat, forall n, (N <= n)%nat -> P n.

Global Instance eventually_filter : ProperFilter eventually.
Proof.
constructor.
  intros P [N H].
  exists N.
  apply H.
  apply le_refl.
constructor.
- now exists 0%nat.
- intros P Q [NP HP] [NQ HQ].
  exists (max NP NQ).
  intros n Hn.
  split.
  apply HP.
  apply le_trans with (2 := Hn).
  apply Max.le_max_l.
  apply HQ.
  apply le_trans with (2 := Hn).
  apply Max.le_max_r.
- intros P Q H [NP HP].
  exists NP.
  intros n Hn.
  apply H.
  now apply HP.
Qed.

(** * The topology on real numbers *)

Global Instance R_abelian_group : AbelianGroup R.
Proof.
apply (@Build_AbelianGroup R Rplus Ropp R0).
apply Rplus_comm.
intros x y z.
apply sym_eq, Rplus_assoc.
apply Rplus_0_r.
apply Rplus_opp_r.
Defined.

Lemma R_NormedAbelianGroup_mixin :
  NormedAbelianGroup_mixin R R_abelian_group.
Proof.
  exists (fun x => Rabs x).
  by apply Rabs_R0.
  move => x ; by apply Rabs_Ropp.
  move => x y ; by apply Rabs_triang.
Defined.

Global Instance R_NormedAbelianGroup : NormedAbelianGroup R.
Proof.
  apply (Build_NormedAbelianGroup _ _).
  exact: R_NormedAbelianGroup_mixin.
Defined.

Lemma R_field_mixin : Field_mixin R R_abelian_group.
Proof.
  econstructor => /=.
  exact Rmult_comm.
  move => x y z ; by rewrite Rmult_assoc.
  exact Rmult_1_r.
  exact Rinv_r.
  apply Rmult_plus_distr_r.
Defined.

Lemma R_absfield_mixin : AbsField_mixin R
  {| field_group := R_abelian_group; field_field := R_field_mixin |}.
Proof.
  apply Build_AbsField_mixin with Rabs ; simpl.
  exact Rabs_R0.
  rewrite Rabs_Ropp ; exact Rabs_R1.
  exact Rabs_triang.
  exact Rabs_mult.
Defined.

Global Instance R_metric_field : AbsField R.
Proof.
  apply Build_AbsField with R_abelian_group R_field_mixin.
  by apply R_absfield_mixin.
Defined.

Lemma R_complete :
  forall F : (R -> Prop) -> Prop,
  ProperFilter F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  {x : R | forall eps :posreal, F (ball x eps)}.
Proof.
intros F FF HF.
set (E := fun x : R => F (ball x (mkposreal _ Rlt_0_1))).
destruct (completeness E) as [x [Hx1 Hx2]].
  destruct (HF (mkposreal _ Rlt_0_1)) as [y Fy].
  exists (y + 2).
  intros x Fx.
  apply filter_const.
  generalize (filter_and _ _ Fy Fx).
  apply filter_imp.
  intros z [Hz1 Hz2].
  apply Rplus_le_reg_r with (-y).
  replace (y + 2 + -y) with 2 by ring.
  apply Rabs_le_between.
  change (Rabs (x + - y)) with (distance y x).
  apply Rle_trans with (1 := distance_triangle y z x).
  apply Rlt_le.
  apply Rplus_lt_compat with (1 := Hz1).
  now rewrite distance_comm.
  destruct (HF (mkposreal _ Rlt_0_1)) as [y Fy].
  now exists y.
exists (x - 1).
intros eps.
set (eps' := pos_div_2 (mkposreal _ (Rmin_case _ _ _ Rlt_R0_R2 (cond_pos eps)))).
destruct (HF eps') as [z Hz].
assert (H1 : z - Rmin 2 eps / 2 + 1 <= x).
  apply Hx1.
  revert Hz.
  unfold E.
  apply filter_imp.
  simpl ; intros u Bu.
  apply (Rabs_lt_between' u z) in Bu.
  apply Rabs_lt_between'.
  simpl in Bu |- *.
  clear -Bu.
  destruct Bu as [Bu1 Bu2].
  assert (H := Rmin_l 2 eps).
  split ; Fourier.fourier.
assert (H2 : x <= z + Rmin 2 eps / 2 + 1).
  apply Hx2.
  intros v Hv.
  apply filter_const.
  generalize (filter_and _ _ Hz Hv).
  apply filter_imp.
  simpl ; intros w [Hw1 Hw2].
  apply (Rabs_lt_between' w z) in Hw1.
  destruct Hw1 as [_ Hw1].
  apply (Rabs_lt_between' w v) in Hw2.
  destruct Hw2 as [Hw2 _].
  clear -Hw1 Hw2.
  simpl in Hw1, Hw2.
  Fourier.fourier.
revert Hz.
apply filter_imp.
simpl ; intros u Hu.
apply (Rabs_lt_between' u z) in Hu.
apply Rabs_lt_between'.
assert (H3 := Rmin_l 2 eps).
assert (H4 := Rmin_r 2 eps).
clear -H1 H2 Hu H3 H4.
destruct Hu.
split ; Fourier.fourier.
Qed.

Global Instance R_complete_metric : CompleteSpace R.
Proof.
apply (Build_CompleteSpace R _).
constructor.
apply R_complete.
Defined.

Notation at_left x := (within (fun u : R => Rlt u x) (locally (x)%R)).
Notation at_right x := (within (fun u : R => Rlt x u) (locally (x)%R)).

(** Some open sets of [R] *)

Lemma open_lt :
  forall y : R, open (fun u : R => u < y).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
exists (mkposreal _ Hxy).
intros z Bz.
replace y with (x + (y - x)) by ring.
apply Rabs_lt_between'.
apply Bz.
Qed.

Lemma open_gt :
  forall y : R, open (fun u : R => y < u).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
exists (mkposreal _ Hxy).
intros z Bz.
replace y with (x - (x - y)) by ring.
apply Rabs_lt_between'.
apply Bz.
Qed.

Lemma open_neq :
  forall y : R, open (fun u : R => u <> y).
Proof.
intros y.
apply (open_ext (fun u => u < y \/ y < u)).
intros u.
split.
apply Rlt_dichotomy_converse.
apply Rdichotomy.
apply open_or.
apply open_lt.
apply open_gt.
Qed.

Lemma locally_interval (P : R -> Prop) (x : R) (a b : Rbar) :
  Rbar_lt a x -> Rbar_lt x b ->
  (forall (y : R), Rbar_lt a y -> Rbar_lt y b -> P y) ->
  locally x P.
Proof.
  move => Hax Hxb Hp.
  case: (Rbar_lt_locally _ _ _ Hax Hxb) => d Hd.
  exists d => y Hy.
  apply Hp ; by apply Hd.
Qed.

Lemma locally_ex_dec :
  forall P (x : R),
  (forall x, P x \/ ~P x) ->
  locally x P ->
  {d:posreal | forall y, Rabs (y-x) < d -> P y}.
Proof.
intros P x P_dec H.
set (Q := fun z => forall y,  Rabs (y-x) < z -> P y).
destruct (ex_lub_Rbar_ne Q) as ([d| |],(H1,H2)).
destruct H as (d1,Hd1).
now exists d1.
(* *)
assert (Zd: 0 < d).
destruct H as (d1,Hd1).
apply Rlt_le_trans with (1 := cond_pos d1).
apply Rbar_finite_le.
now apply H1.
exists (mkposreal d Zd).
simpl.
intros y Hy.
destruct (P_dec y) as [Py|Py].
exact Py.
elim (Rlt_not_le _ _ Hy).
apply Rbar_finite_le.
apply H2.
intros u Hu.
apply Rbar_finite_le.
apply Rnot_lt_le.
contradict Py.
now apply Hu.
(* *)
exists (mkposreal 1 Rlt_0_1).
simpl.
intros y Hy.
destruct (P_dec y) as [Py|Py].
exact Py.
elim (Rlt_not_le _ _ Hy).
apply Rbar_finite_le.
apply Rbar_le_trans with p_infty.
now left.
apply H2.
intros u Hu.
apply Rbar_finite_le.
apply Rnot_lt_le.
contradict Py.
now apply Hu.
(* *)
elimtype False.
destruct H as (d1,Hd1).
now destruct (H1 d1).
Qed.

(** * Topology on [R]² *)

Definition locally_2d (P : R -> R -> Prop) x y :=
  exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.

Lemma locally_2d_locally :
  forall P x y,
  locally_2d P x y <-> locally (x,y) (fun z => P (fst z) (snd z)).
Proof.
intros P x y.
split ; intros [d H] ; exists d.
- simpl.
  intros [u v] H'.
  apply H.
  apply Rle_lt_trans with (2 := H').
  apply Rmax_l.
  apply Rle_lt_trans with (2 := H').
  apply Rmax_r.
- intros u v Hu Hv.
  rewrite /= /dist_prod  in H.
  apply (H (u,v)).
  now apply Rmax_case.
Qed.

Lemma locally_2d_locally' :
  forall P x y,
  locally_2d P x y <-> locally ((x,(y,tt)) : Tn 2 R) (fun z : Tn 2 R => P (fst z) (fst (snd z))).
Proof.
intros P x y.
split ; intros [d H] ; exists d.
- simpl.
  move => [u [v t]] /= {t} H'.
  apply H.
  apply Rle_lt_trans with (2 := H').
  apply Rmax_l.
  apply Rle_lt_trans with (2 := H').
  rewrite (Rmax_left _ 0).
  apply Rmax_r.
  apply Rabs_pos.
- intros u v Hu Hv.
  simpl in H.
  apply (H (u,(v,tt))).
  apply Rmax_case.
  exact Hu.
  apply Rmax_case.
  exact Hv.
  apply cond_pos.
Qed.

Lemma locally_2d_impl_strong :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => locally_2d P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y Li LP.
apply locally_2d_locally in Li.
apply locally_2d_locally in LP.
apply locally_locally in LP.
apply locally_2d_locally.
generalize (filter_and _ _ Li LP).
apply: filter_imp.
intros [u v] [H1 H2].
apply H1.
now apply locally_2d_locally.
Qed.

Lemma locally_2d_singleton :
  forall (P : R -> R -> Prop) x y, locally_2d P x y -> P x y.
Proof.
intros P x y LP.
apply locally_2d_locally in LP.
apply locally_singleton with (1 := LP).
Qed.

Lemma locally_2d_impl :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y (d,H).
apply locally_2d_impl_strong.
exists d => u v Hu Hv Hp.
apply H => //.
now apply locally_2d_singleton.
Qed.

Lemma locally_2d_forall :
  forall (P : R -> R -> Prop) x y, (forall u v, P u v) -> locally_2d P x y.
Proof.
intros P x y Hp.
now exists (mkposreal _ Rlt_0_1) => u v _ _.
Qed.

Lemma locally_2d_and :
  forall (P Q : R -> R -> Prop) x y, locally_2d P x y -> locally_2d Q x y ->
  locally_2d (fun u v => P u v /\ Q u v) x y.
Proof.
intros P Q x y H.
apply: locally_2d_impl.
apply: locally_2d_impl H.
apply locally_2d_forall.
now split.
Qed.

Lemma locally_2d_align :
  forall (P Q : R -> R -> Prop) x y,
  ( forall eps : posreal, (forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> P u v) ->
    forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> Q u v ) ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y K (d,H).
exists d => u v Hu Hv.
now apply (K d).
Qed.

Lemma locally_2d_1d_const_x :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally y (fun t => P x t).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
rewrite Rminus_eq_0 Rabs_R0; apply cond_pos.
exact Hz.
Qed.

Lemma locally_2d_1d_const_y :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally x (fun t => P t y).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
exact Hz.
rewrite Rminus_eq_0 Rabs_R0; apply cond_pos.
Qed.

Lemma locally_2d_1d_strong :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 ->
    locally t (fun z => locally_2d P (x + z * (u - x)) (y + z * (v - y)))) x y.
Proof.
intros P x y.
apply locally_2d_align => eps HP u v Hu Hv t Ht.
assert (Zm: 0 <= Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmax_case ; apply Rabs_pos.
destruct Zm as [Zm|Zm].
(* *)
assert (H1: Rmax (Rabs (u - x)) (Rabs (v - y)) < eps).
now apply Rmax_case.
set (d1 := mkposreal _ (Rlt_Rminus _ _ H1)).
assert (H2: 0 < pos_div_2 d1 / Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_lt_0_compat.
apply cond_pos.
now apply Rinv_0_lt_compat.
set (d2 := mkposreal _ H2).
exists d2 => z Hz.
exists (pos_div_2 d1) => p q Hp Hq.
apply HP.
(* . *)
replace (p - x) with (p - (x + z * (u - x)) + (z - t + t) * (u - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 d1 + (eps - pos_div_2 d1)) by ring.
apply Rplus_lt_le_compat with (1 := Hp).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_l.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* . *)
replace (q - y) with (q - (y + z * (v - y)) + (z - t + t) * (v - y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 d1 + (eps - pos_div_2 d1)) by ring.
apply Rplus_lt_le_compat with (1 := Hq).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_r.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* *)
apply: filter_forall => z.
exists eps => p q.
replace (u - x) with 0.
replace (v - y) with 0.
rewrite Rmult_0_r 2!Rplus_0_r.
apply HP.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_r.
apply Rabs_pos.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_l.
apply Rabs_pos.
Qed.

Lemma locally_2d_1d :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 -> locally_2d P (x + t * (u - x)) (y + t * (v - y))) x y.
Proof.
intros P x y H.
apply locally_2d_1d_strong in H.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H t Ht.
specialize (H t Ht).
apply locally_singleton with (1 := H).
Qed.

Lemma locally_2d_ex_dec: forall P x y, (forall x y, P x y \/ ~P x y) -> locally_2d P x y
   -> {d:posreal| forall u v, Rabs (u-x) < d -> Rabs (v-y) < d -> P u v}.
Proof.
intros P x y P_dec H.
set (Q := fun z => forall u v,   Rabs (u-x) < z -> Rabs (v-y) < z -> P u v).
destruct (ex_lub_Rbar_ne Q) as ([d| |],(H1,H2)).
destruct H as (d1,Hd1).
now exists d1.
(* *)
assert (Zd: 0 < d).
destruct H as (d1,Hd1).
apply Rlt_le_trans with (1 := cond_pos d1).
apply Rbar_finite_le.
now apply H1.
exists (mkposreal d Zd).
simpl.
intros u v Hu Hv.
destruct (P_dec  u v) as [Puv|Puv].
exact Puv.
assert (Hi:(Rmax (Rabs (u - x)) (Rabs (v - y)) < d)).
now apply Rmax_case.
elim (Rlt_not_le _ _ Hi).
apply Rbar_finite_le.
apply H2.
intros z Hz.
apply Rbar_finite_le.
apply Rnot_lt_le.
contradict Puv.
apply Hz.
apply Rle_lt_trans with (2:=Puv).
apply Rmax_l.
apply Rle_lt_trans with (2:=Puv).
apply Rmax_r.
(* *)
exists (mkposreal 1 Rlt_0_1).
simpl.
intros u v Hu Hv.
destruct (P_dec u v) as [Puv|Puv].
exact Puv.
assert (Hi:(Rmax (Rabs (u - x)) (Rabs (v - y)) < 1)).
now apply Rmax_case.
elim (Rlt_not_le _ _ Hi).
apply Rbar_finite_le.
apply Rbar_le_trans with p_infty.
now left.
apply H2.
intros z Hz.
apply Rbar_finite_le.
apply Rnot_lt_le.
contradict Puv.
apply Hz.
apply Rle_lt_trans with (2:=Puv).
apply Rmax_l.
apply Rle_lt_trans with (2:=Puv).
apply Rmax_r.
(* *)
elimtype False.
destruct H as (d1,Hd1).
now destruct (H1 d1).
Qed.

(** * Some Topology on extended real numbers *)

Definition Rbar_locally' (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally' a P
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.
Definition Rbar_locally (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally a P
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.

Global Instance Rbar_locally'_filter :
  forall x, ProperFilter (Rbar_locally' x).
Proof.
intros [x| |] ; (constructor ; [idtac | constructor]).
- intros P [eps HP].
  exists (x + eps / 2).
  apply HP.
  unfold distance ; simpl.
  ring_simplify (x + eps / 2 + - x).
  rewrite Rabs_pos_eq.
  apply Rminus_lt_0.
  replace (eps - eps / 2) with (eps / 2) by field.
  apply is_pos_div_2.
  apply Rlt_le, is_pos_div_2.
  apply Rgt_not_eq, Rminus_lt_0 ; ring_simplify.
  apply is_pos_div_2.
- now exists (mkposreal _ Rlt_0_1).
- intros P Q [dP HP] [dQ HQ].
  exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
  simpl.
  intros y Hy H.
  split.
  apply HP with (2 := H).
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ with (2 := H).
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy H'.
  apply H.
  now apply HP.
- intros P [N HP].
  exists (N + 1).
  apply HP.
  apply Rlt_plus_1.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Rmax MP MQ).
  intros y Hy.
  split.
  apply HP.
  apply Rle_lt_trans with (2 := Hy).
  apply Rmax_l.
  apply HQ.
  apply Rle_lt_trans with (2 := Hy).
  apply Rmax_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
- intros P [N HP].
  exists (N - 1).
  apply HP.
  apply Rlt_minus_l, Rlt_plus_1.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Rmin MP MQ).
  intros y Hy.
  split.
  apply HP.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

Global Instance Rbar_locally_filter :
  forall x, ProperFilter (Rbar_locally x).
Proof.
intros [x| |].
- apply locally_filter.
- exact (Rbar_locally'_filter p_infty).
- exact (Rbar_locally'_filter m_infty).
Qed.

Lemma open_Rbar_lt :
  forall y, open (fun u : R => Rbar_lt u y).
Proof.
intros [y| |].
- apply open_lt.
- apply open_true.
- apply open_false.
Qed.

Lemma open_Rbar_gt :
  forall y, open (fun u : R => Rbar_lt y u).
Proof.
intros [y| |].
- apply open_gt.
- apply open_false.
- apply open_true.
Qed.

Lemma open_Rbar_lt' :
  forall x y, Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof.
intros [x| |] y Hxy.
- now apply open_Rbar_lt.
- easy.
- destruct y as [y| |].
  now exists y.
  now apply filter_forall.
  easy.
Qed.

Lemma open_Rbar_gt' :
  forall x y, Rbar_lt y x -> Rbar_locally x (fun u => Rbar_lt y u).
Proof.
intros [x| |] y Hxy.
- now apply open_Rbar_gt.
- destruct y as [y| |].
  now exists y.
  easy.
  now apply filter_forall.
- now destruct y as [y| |].
Qed.

Lemma Rbar_locally'_le :
  forall x, filter_le (Rbar_locally' x) (Rbar_locally x).
Proof.
intros [x| |] P [eps HP] ; exists eps ; intros ; now apply HP.
Qed.

Lemma Rbar_locally'_le_finite :
  forall x : R, filter_le (Rbar_locally' x) (locally x).
Proof.
intros x P [eps HP] ; exists eps ; intros ; now apply HP.
Qed.



(** * Some limits on real functions *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + / (INR n + 1)
    | p_infty => INR n
    | m_infty => - INR n
  end.

Lemma filterlim_Rbar_loc_seq :
  forall x, filterlim (Rbar_loc_seq x) eventually (Rbar_locally' x).
Proof.
  intros x P.
  unfold Rbar_loc_seq.
  case: x => /= [x | | ] [delta Hp].
(* x \in R *)
  case: (nfloor_ex (/delta)) => [ | N [_ HN]].
  by apply Rlt_le, Rinv_0_lt_compat, delta.
  exists N => n Hn.
  apply Hp ; simpl.
  ring_simplify (x + / (INR n + 1) + - x).
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
  apply Rgt_not_eq, Rminus_lt_0.
  ring_simplify.
  by apply RinvN_pos.
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

(* TODO : Bouger dans Limit ? *)

Lemma filterlim_const :
  forall {T U} {MU : MetricSpace U} {F : (T -> Prop) -> Prop} {FF : Filter F},
  forall a : U, filterlim (fun _ => a) F (locally a).
Proof.
intros T U MU F FF a P [eps HP].
unfold filtermap.
apply filter_forall.
intros _.
apply HP.
apply ball_center.
Qed.

Lemma filterlim_opp :
  forall x,
  filterlim Ropp (Rbar_locally x) (Rbar_locally (Rbar_opp x)).
Proof.
intros [x| |] P [eps He].
- exists eps.
  intros y Hy.
  apply He.
  by rewrite /= /distance /Rminus Ropp_involutive Rplus_comm Rabs_minus_sym.
- exists (-eps).
  intros y Hy.
  apply He.
  apply Ropp_lt_cancel.
  by rewrite Ropp_involutive.
- exists (-eps).
  intros y Hy.
  apply He.
  apply Ropp_lt_cancel.
  by rewrite Ropp_involutive.
Qed.

Lemma filterlim_plus :
  forall x y,
  ex_Rbar_plus x y ->
  filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally (Rbar_plus x y)).
Proof.
  intros x y.
  wlog: x y / (Rbar_le 0 (Rbar_plus x y)).
    intros Hw.
    case: (Rbar_le_lt_dec 0 (Rbar_plus x y)) => Hz Hp.
    by apply Hw.
    apply (filterlim_ext (fun z => - (- fst z + - snd z))).
    intros z.
    ring.
    rewrite -(Rbar_opp_involutive (Rbar_plus x y)).
    eapply filterlim_compose.
    2: apply filterlim_opp.
    assert (Hw' : filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_plus (Rbar_opp x) (Rbar_opp y)))).
    apply Hw.
    rewrite Rbar_plus_opp.
    replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
    apply Rbar_opp_le.
    by left.
    revert Hp.
    clear.
    now destruct x as [x| |] ; destruct y as [y| |].
    clear Hw.
    rewrite -Rbar_plus_opp.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists (fun x => Q (- x)) (fun x => R (- x)).
    now apply filterlim_opp.
    now apply filterlim_opp.
    intros u v HQ HR.
    exact (H3 _ _ HQ HR).

  unfold Rbar_plus, ex_Rbar_plus.
  case Hlp: Rbar_plus' => [[z| |]|] Hz Hp ;
  try by case: Hz.

(* x + y \in R *)
  case: x y Hlp Hz {Hp} => [x| |] ;
  case => [y| |] //= ; case => <- Hlp.
  intros P [eps He].
  exists (fun u => Rabs (u - x) < pos_div_2 eps) (fun v => Rabs (v - y) < pos_div_2 eps).
  now exists (pos_div_2 eps).
  now exists (pos_div_2 eps).
  intros u v Hu Hv.
  apply He.
  simpl.
  replace (u + v + - (x + y)) with ((u - x) + (v - y)) by ring.
  rewrite (double_var eps) ;
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
  now apply Hu.
  now apply Hv.

(* x + y = p_infty *)
  wlog: x y Hlp {Hp Hz} / (is_finite x) => [Hw|Hx].
    case: x y Hlp {Hp Hz} => [x| |] ;
    case => [y| |] // _.
    now apply (Hw x p_infty).
    assert (Hw': filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally y) (Rbar_locally p_infty)) (Rbar_locally p_infty)).
    exact: Hw.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists R Q ; try assumption.
    intros u v Hu Hv.
    rewrite Rplus_comm.
    now apply (H3 v u).
    clear Hw.
    intros P [N HN].
    exists (fun x => N/2 < x) (fun x => N/2 < x).
    now exists (N/2).
    now exists (N/2).
    intros x y Hx Hy.
    simpl.
    apply HN.
    rewrite (double_var N).
    now apply Rplus_lt_compat.
  case: x y Hlp Hx => [x| |] ;
  case => [y| | ] //= _ _.
  intros P [N HN].
  exists (fun u => Rabs (u - x) < 1) (fun v => N - x + 1 < v).
  now exists (mkposreal _ Rlt_0_1).
  now exists (N - x + 1).
  intros u v Hu Hv.
  simpl.
  apply HN.
  replace N with (x - 1 + (N - x + 1)) by ring.
  apply Rplus_lt_compat.
  now apply Rabs_lt_between'.
  exact Hv.
Qed.

Lemma filterlim_mult :
  forall x y,
  ex_Rbar_mult x y ->
  filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally (Rbar_mult x y)).
Proof.
  intros x y.
  wlog: x y / (Rbar_le 0 x).
    intros Hw.
    case: (Rbar_le_lt_dec 0 x) => Hx Hp.
    by apply Hw.
    apply (filterlim_ext (fun z => - (- fst z * snd z))).
    intros z.
    ring.
    rewrite -(Rbar_opp_involutive (Rbar_mult x y)).
    eapply filterlim_compose.
    2: apply filterlim_opp.
    assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally y)) (Rbar_locally (Rbar_mult (Rbar_opp x) y))).
    apply Hw.
    replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
    apply Rbar_opp_le.
    by apply Rbar_lt_le.
    rewrite /ex_Rbar_mult Rbar_mult'_comm Rbar_mult'_opp_r.
    revert Hp.
    rewrite /ex_Rbar_mult Rbar_mult'_comm.
    now case Rbar_mult'.
    clear Hw.
    rewrite -Rbar_mult_opp_l.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists (fun x => Q (- x)) R.
    now apply filterlim_opp.
    exact H2.
    intros u v HQ HR.
    exact (H3 _ _ HQ HR).
  wlog: x y / (Rbar_le 0 y).
    intros Hw.
    case: (Rbar_le_lt_dec 0 y) => Hy Hx Hp.
    by apply Hw.
    apply (filterlim_ext (fun z => - (fst z * -snd z))).
    intros z.
    ring.
    rewrite -(Rbar_opp_involutive (Rbar_mult x y)).
    eapply filterlim_compose.
    2: apply filterlim_opp.
    assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally x) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_mult x (Rbar_opp y)))).
    apply Hw.
    replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
    apply Rbar_opp_le.
    by apply Rbar_lt_le.
    by [].
    revert Hp.
    rewrite /ex_Rbar_mult Rbar_mult'_opp_r.
    now case Rbar_mult'.
    clear Hw.
    rewrite -Rbar_mult_opp_r.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists Q (fun x => R (- x)).
    exact H1.
    now apply filterlim_opp.
    intros u v HQ HR.
    exact (H3 _ _ HQ HR).
  wlog: x y / (Rbar_le x y).
    intros Hw.
    case: (Rbar_le_lt_dec x y) => Hl Hx Hy Hp.
    by apply Hw.
    assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally y) (Rbar_locally x)) (Rbar_locally (Rbar_mult y x))).
    apply Hw ; try assumption.
    by apply Rbar_lt_le.
    by rewrite /ex_Rbar_mult Rbar_mult'_comm.
    rewrite Rbar_mult_comm.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists R Q ; try assumption.
    intros u v HR HQ.
    simpl.
    rewrite Rmult_comm.
    exact (H3 _ _ HQ HR).
  case: x => [x| |] ; case: y => [y| |] /= Hl Hy Hx Hp ;
  try (by case: Hl) || (by case: Hx) || (by case: Hy).
(* x, y \in R *)
  apply Rbar_finite_le in Hx.
  apply Rbar_finite_le in Hy.
  intros P [eps HP].
  assert (He: 0 < eps / (x + y + 1)).
  apply Rdiv_lt_0_compat.
  apply cond_pos.
  apply Rplus_le_lt_0_compat.
  now apply Rplus_le_le_0_compat.
  apply Rlt_0_1.
  set (d := mkposreal _ (Rmin_stable_in_posreal (mkposreal _ Rlt_0_1) (mkposreal _ He))).
  exists (fun u => Rabs (u - x) < d) (fun v => Rabs (v - y) < d).
  now exists d.
  now exists d.
  simpl.
  intros u v Hu Hv.
  apply HP.
  simpl.
  replace (u * v + - (x * y)) with (x * (v - y) + y * (u - x) + (u - x) * (v - y)) by ring.
  replace (pos eps) with (x * (eps / (x + y + 1)) + y * (eps / (x + y + 1)) + 1 * (eps / (x + y + 1))).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_lt_compat.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_compat.
  rewrite Rabs_mult Rabs_pos_eq //.
  apply Rmult_le_compat_l with (1 := Hx).
  apply Rlt_le.
  apply Rlt_le_trans with (1 := Hv).
  apply Rmin_r.
  rewrite Rabs_mult Rabs_pos_eq //.
  apply Rmult_le_compat_l with (1 := Hy).
  apply Rlt_le.
  apply Rlt_le_trans with (1 := Hu).
  apply Rmin_r.
  rewrite Rabs_mult.
  apply Rmult_le_0_lt_compat ; try apply Rabs_pos.
  apply Rlt_le_trans with (1 := Hu).
  apply Rmin_l.
  apply Rlt_le_trans with (1 := Hv).
  apply Rmin_r.
  field.
  apply Rgt_not_eq.
  apply Rplus_le_lt_0_compat.
  now apply Rplus_le_le_0_compat.
  apply Rlt_0_1.
(* x \in R and y = p_infty *)
  case: Rle_dec Hp => // Hx' Hp.
  case: Rle_lt_or_eq_dec Hp => // {Hl Hx Hy Hx'} Hx _.
  intros P [N HN].
  exists (fun u => Rabs (u - x) < x / 2) (fun v => Rmax 0 (N / (x / 2)) < v).
  now exists (pos_div_2 (mkposreal _ Hx)).
  now exists (Rmax 0 (N / (x / 2))).
  intros u v Hu Hv.
  simpl.
  apply HN.
  apply Rle_lt_trans with ((x - x / 2) * Rmax 0 (N / (x / 2))).
  apply Rmax_case_strong => H.
  rewrite Rmult_0_r ; apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
  repeat apply Rdiv_lt_0_compat => //.
  by apply Rlt_R0_R2.
  apply Req_le ; field.
  by apply Rgt_not_eq.
  apply Rmult_le_0_lt_compat.
  field_simplify ; rewrite Rdiv_1 ; apply Rlt_le, Rdiv_lt_0_compat ; intuition.
  apply Rmax_l.
  now apply Rabs_lt_between'.
  exact Hv.
  by apply Rbar_finite_le in Hx.
(* l1 = l2 = p_infty *)
  clear.
  intros P [N HN].
  exists (fun u => 1 < u) (fun v => Rabs N < v).
  now exists 1.
  now exists (Rabs N).
  intros u v Hu Hv.
  simpl.
  apply HN.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite -(Rmult_1_l (Rabs N)).
  apply Rmult_le_0_lt_compat.
  by apply Rle_0_1.
  by apply Rabs_pos.
  exact Hu.
  exact Hv.
Qed.

Lemma filterlim_scal_l :
  forall (a : R) (l : Rbar),
  filterlim (Rmult a) (Rbar_locally l) (Rbar_locally (Rbar_mult a l)).
Proof.
  intros a l.
  case: (Req_dec a 0) => [->|Ha].
  apply (filterlim_ext (fun _ => 0)).
  intros x.
  apply sym_eq, Rmult_0_l.
  replace (Rbar_mult 0 l) with (Finite 0).
  apply filterlim_const.
  case: l => [x| |] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  eapply filterlim_compose_2.
  apply filterlim_const.
  apply filterlim_id.
  apply filterlim_mult.
  case: l => [x| |] //=.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  intros H'.
  now elim Ha.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  intros H'.
  now elim Ha.
Qed.

Lemma filterlim_scal_r :
  forall (a : R) (l : Rbar),
  filterlim (fun x => Rmult x a) (Rbar_locally l) (Rbar_locally (Rbar_mult l a)).
Proof.
intros a l.
apply (filterlim_ext (fun x => a * x)).
apply Rmult_comm.
rewrite Rbar_mult_comm.
apply filterlim_scal_l.
Qed.

Lemma continuity_pt_locally :
  forall f x,
  continuity_pt f x <->
  forall eps : posreal, locally x (fun u => Rabs (f u - f x) < eps).
Proof.
intros f x.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
rewrite /= /R_dist /D_x /no_cond in H2.
exists (mkposreal d H1) => y H.
destruct (Req_dec x y) as [<-|Hxy].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
by apply H2.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d.
split.
apply cond_pos.
intros h [Zh Hh].
exact: H.
Qed.

Lemma continuity_pt_locally' :
  forall f x,
  continuity_pt f x <->
  forall eps : posreal, locally' x (fun u => Rabs (f u - f x) < eps).
Proof.
intros f x.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
rewrite /= /R_dist /D_x /no_cond in H2.
exists (mkposreal d H1) => y H H'.
destruct (Req_dec x y) as [<-|Hxy].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
by apply H2.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d.
split.
apply cond_pos.
intros h [Zh Hh].
apply H.
exact Hh.
apply proj2 in Zh.
now contradict Zh.
Qed.

Lemma continuity_pt_filterlim :
  forall (f : R -> R) (x : R),
  continuity_pt f x <->
  filterlim f (locally x) (locally (f x)).
Proof.
intros f x.
eapply iff_trans.
apply continuity_pt_locally.
apply iff_sym.
exact (filterlim_locally f (f x)).
Qed.

Lemma continuity_pt_filterlim' :
  forall f x,
  continuity_pt f x <->
  filterlim f (locally' x) (locally (f x)).
Proof.
intros f x.
eapply iff_trans.
apply continuity_pt_locally'.
apply iff_sym.
exact (filterlim_locally f (f x)).
Qed.

Lemma locally_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x ->
  locally x (fun x => P (f x)).
Proof.
intros Lf Cf.
apply continuity_pt_filterlim in Cf.
now apply Cf.
Qed.

Global Instance R_metric_vector : MetricVectorSpace R R.
Proof.
econstructor.
intros x y.
now apply filterlim_plus with (x := Finite x) (y := Finite y).
intros x y.
apply filterlim_scal_l with (l := Finite y).
Defined.
