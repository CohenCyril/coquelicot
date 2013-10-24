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

Require Import Reals Rbar ssreflect.
Require Import Rcomplements List Lub.
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

(** * Topological spaces *)

(** ** Definitions *)

Inductive neighborhood_ {T} (basis : (T -> Prop) -> Prop) (x : T) (D : T -> Prop) : Prop :=
  Neighborhood (P : T -> Prop) : basis P -> P x -> (forall y, P y -> D y) -> neighborhood_ basis x D.

Class TopologicalSpace T := {
  basis : (T -> Prop) -> Prop ;
  open := fun (D : T -> Prop) =>
    forall x, D x -> neighborhood_ basis x D ;
  basis_and : forall P Q, basis P -> basis Q ->
    forall x, P x -> Q x -> neighborhood_ basis x (fun y => P y /\ Q y) ;
  basis_true : forall x, exists P, basis P /\ P x
}.

Definition neighborhood {T} {TT : TopologicalSpace T} : T -> (T -> Prop) -> Prop :=
  neighborhood_ basis.

Global Instance neighborhood_filter :
  forall T (TT : TopologicalSpace T) (x : T), ProperFilter (neighborhood x).
Proof.
intros T TT x.
split ; [idtac | split].
- intros P [Q BQ Qx H].
  exists x.
  now apply H.
- destruct (basis_true x) as [P [BP Px]].
  by exists P.
- intros P Q [P' BP' Px HP] [Q' BQ' Qx HQ].
  destruct (basis_and P' Q' BP' BQ' x Px Qx) as [R BR Rx HR].
  apply Neighborhood with (1 := BR).
  exact Rx.
  intros y Ry.
  destruct (HR y Ry) as [Py Qy].
  split.
  now apply HP.
  now apply HQ.
- intros P Q H [P' BP' Px HP].
  apply Neighborhood with (1 := BP').
  exact Px.
  intros y Py.
  apply H.
  now apply HP.
Qed.

Lemma neighborhood_imp :
  forall {T} {TT : TopologicalSpace T} x (P Q : T -> Prop),
  (forall x, P x -> Q x) ->
  neighborhood x P -> neighborhood x Q.
Proof.
intros T TT x P Q H [R BR Rx HR].
exists R ; try easy.
intros y Ry.
apply H.
now apply HR.
Qed.

Lemma neighborhood_basis :
  forall {T} {TT : TopologicalSpace T} x P,
  basis P -> P x -> neighborhood x P.
Proof.
intros T TT x P BP Px.
now exists P.
Qed.

Class FinerTopology {T} (T1 T2 : TopologicalSpace T) :=
  finer_topology : forall x P, @basis T T2 P -> P x -> @neighborhood T T1 x P.

Lemma neighborhood_finer_topology :
  forall {T} (T1 T2 : TopologicalSpace T) {FT : FinerTopology T2 T1},
  forall x P, @neighborhood T T1 x P -> @neighborhood T T2 x P.
Proof.
intros T T1 T2 FT x P [Q BQ Qx HQ].
apply neighborhood_imp with (1 := HQ).
now apply finer_topology.
Qed.

Global Instance FinerTopology_refl :
  forall T (TT : TopologicalSpace T), FinerTopology TT TT.
Proof.
intros T TT x P BP Px.
now exists P.
Qed.

Inductive disjoint_spec {T} {TT : TopologicalSpace T} (x y : T) :=
  Disjoint_spec P Q : basis P -> basis Q -> P x -> Q y ->
    (forall z, P z -> Q z -> False) -> disjoint_spec x y.

Class SeparatedSpace T := {
  seperated_topological :> TopologicalSpace T ;
  separated_disjoint : forall x y : T, x <> y -> disjoint_spec x y
}.

Class FilterCompatibility {T} {TT : TopologicalSpace T} (F : T -> (T -> Prop) -> Prop) := {
  filter_compat1 : forall P x, basis P -> P x -> F x P ;
  filter_compat2 : forall P x, F x P -> exists Q, basis Q /\ Q x /\ forall y, Q y -> P y
}.

Global Instance topology_prod {T U} :
  TopologicalSpace T -> TopologicalSpace U
    -> TopologicalSpace (T * U).
Proof.
  move => TT TU.
  exists (fun (P : _ -> Prop) => forall x, P x ->
    exists Q R, basis Q /\ basis R /\
      Q (fst x) /\ R (snd x) /\ (forall y z, Q y -> R z -> P (y,z))).
  + move => P P' HP HP' x Px P'x.
    case: (HP x Px) => {HP} Q [R [BQ [BR [Qx [Rx HP]]]]].
    case: (HP' x P'x) => {HP'} Q' [R' [BQ' [BR' [Q'x [R'x HP']]]]].
    case: (basis_and Q Q' BQ BQ' _ Qx Q'x) => Q0 BQ0 Q0x HQ0.
    case: (basis_and R R' BR BR' _ Rx R'x) => R0 BR0 R0x HR0.
    exists (fun z => Q0 (fst z) /\ R0 (snd z)).
    move => y [Q0y R0y].
    exists Q0, R0.
    by repeat split.
    by split.
    case => y z [Q0y R0y].
    split.
    apply HP.
    by apply HQ0, Q0y.
    by apply HR0, R0y.
    apply HP'.
    by apply HQ0, Q0y.
    by apply HR0, R0y.
  + case => x y.
    case: (basis_true x) => Q [BQ Qx].
    case: (basis_true y) => R [BR Ry].
    exists (fun z => Q (fst z) /\ R (snd z)).
    split.
    move => z [Qz Rz].
    exists Q, R.
    by repeat split.
    by split.
Defined.

(** ** Open sets *)

Lemma open_basis :
  forall {T} {TT : TopologicalSpace T} P,
  basis P -> open P.
Proof.
intros T TT P BP x Px.
now apply (Neighborhood _ _ _ P).
Qed.

Lemma open_ext :
  forall {T} {TT : TopologicalSpace T} P Q,
  (forall x, P x <-> Q x) ->
  open P -> open Q.
Proof.
intros T TT P Q H OP x Qx.
destruct (OP x) as [R BR Rx HR].
now apply H.
apply (Neighborhood _ _ _ R BR Rx).
intros y Ry.
apply H.
now apply HR.
Qed.

Lemma open_and :
  forall {T} {TT : TopologicalSpace T} D E,
  open D -> open E -> open (fun x => D x /\ E x).
Proof.
intros T TT D E OD OE x [Dx Ex].
destruct (OD x Dx) as [P BP Px HP].
destruct (OE x Ex) as [Q BQ Qx HQ].
destruct (basis_and P Q BP BQ x Px Qx) as [R BR Rx HR].
apply (Neighborhood _ _ _ R BR Rx).
intros y Ry.
destruct (HR y Ry) as [Py Qy].
split.
now apply HP.
now apply HQ.
Qed.

Lemma open_ex :
  forall {T} {TT : TopologicalSpace T} {A} (D : A -> (T -> Prop)),
  (forall a, open (D a)) ->
  open (fun x => exists a, D a x).
Proof.
intros T TT A D OD x [a Dx].
destruct (OD a x Dx) as [P BP Px HP].
apply (Neighborhood _ _ _ P BP Px).
intros y Py.
exists a.
now apply HP.
Qed.

Lemma open_or :
  forall {T} {TT : TopologicalSpace T} D E,
  open D -> open E -> open (fun x => D x \/ E x).
Proof.
intros T TT D E OD OE x [Dx|Ex].
destruct (OD x Dx) as [P BP Px HP].
apply (Neighborhood _ _ _ P BP Px).
intros y Py.
left.
now apply HP.
destruct (OE x Ex) as [P BP Px HP].
apply (Neighborhood _ _ _ P BP Px).
intros y Py.
right.
now apply HP.
Qed.

Lemma open_false :
  forall {T} {TT : TopologicalSpace T},
  open (fun _ => False).
Proof.
intros T TT x [].
Qed.

Lemma filter_open :
  forall {T} {TT : TopologicalSpace T},
  forall {F} {FF : forall x, Filter (F x)} {FC : FilterCompatibility F},
  forall D, open D <-> forall x, D x -> F x D.
Proof.
intros T TT F FF FC D.
split.
- intros OD x Dx.
  destruct (OD x Dx) as [P BP Px PD].
  apply filter_imp with (1 := PD).
  now apply filter_compat1.
- intros H x Dx.
  destruct (filter_compat2 D x (H x Dx)) as [Q [BQ [Qx HQP]]].
  now exists Q.
Qed.

(** ** Limits and continuity in topological spaces *)

(** Limit of a filter *)

Definition is_filter_lim {T} {TT : TopologicalSpace T} (F : (T -> Prop) -> Prop) (x : T) :=
  forall P, basis P -> P x -> F P.

Lemma is_filter_lim_unique :
  forall {T} {ST : SeparatedSpace T} {F} {FF : ProperFilter F} (x y : T),
  is_filter_lim F x ->
  is_filter_lim F y ->
  not (x <> y).
Proof.
intros T ST F FF x y Fx Fy H.
destruct (separated_disjoint x y H) as [P Q BP BQ Px Qy H'].
apply filter_const.
generalize (filter_and _ _ (Fx P BP Px) (Fy Q BQ Qy)).
apply filter_imp.
intros z [Pz Qz].
now apply (H' z).
Qed.

Lemma is_filter_lim_neighborhood :
  forall {T} {TT : TopologicalSpace T} (x : T),
  is_filter_lim (neighborhood x) x.
Proof.
intros T TT x P BP Px.
now apply Neighborhood with (1 := BP).
Qed.

(** Continuity *)

Definition continuity {U V} {TU : TopologicalSpace U} {TV : TopologicalSpace V} (f : U -> V) (x : U) :=
  forall P, basis P -> P (f x) -> neighborhood x (fun x => P (f x)).

Lemma continuity_finer_topology_l :
  forall {U V} {TV : TopologicalSpace V} (TU1 TU2 : TopologicalSpace U)
    {FT : FinerTopology TU2 TU1} (f : U -> V) x,
  @continuity U V TU1 TV f x -> @continuity U V TU2 TV f x.
Proof.
intros U V TV TU1 TU2 FT f x Cf P BP Pfx.
apply neighborhood_finer_topology with (1 := FT).
now apply Cf.
Qed.

Lemma continuity_finer_topology_r :
  forall {U V} {TU : TopologicalSpace U} (TV1 TV2 : TopologicalSpace V)
    {FT : FinerTopology TV1 TV2} (f : U -> V) x,
  @continuity U V TU TV1 f x -> @continuity U V TU TV2 f x.
Proof.
intros U V TU TV1 TV2 FT f x Cf P BP Pfx.
destruct (FT (f x) P BP Pfx) as [Q BQ Qfx HQ].
eapply neighborhood_imp.
intros y.
apply HQ.
now apply Cf.
Qed.

Lemma is_filter_lim_continuity :
  forall {T U} {TT : TopologicalSpace T} {TU : TopologicalSpace U} (f : T -> U) (x : T),
  (forall F, Filter F -> is_filter_lim F x -> is_filter_lim (filtermap f F) (f x)) <->
  continuity f x.
Proof.
intros T U TT TU f x.
split.
- intros Cf Q BQ Qfx.
  apply Cf ; try easy.
  apply neighborhood_filter.
  apply is_filter_lim_neighborhood.
- intros Cf F FF Fx P BP Pfx.
  destruct (Cf P BP Pfx) as [Q BQ Qx HQ].
  unfold filtermap.
  apply filter_imp with (1 := HQ).
  now apply Fx.
Qed.

Lemma filterlim_neighborhood_continuity :
  forall {U V} {TU : TopologicalSpace U} {TV : TopologicalSpace V} (f : U -> V) (x : U),
  filterlim f (neighborhood x) (neighborhood (f x)) <-> continuity f x.
Proof.
intros U V TU TV f x.
split.
- intros Cf P BP Pfx.
  apply Cf.
  now exists P.
- intros Cf P [Q BQ Qfx HQP].
  unfold filtermap.
  generalize (Cf Q BQ Qfx).
  apply filter_imp.
  intros u.
  apply HQP.
Qed.

Lemma continuity_comp {T U V} {TT : TopologicalSpace T} {TU : TopologicalSpace U} {TV : TopologicalSpace V} :
  forall (f : T -> U) (g : U -> V) (x : T),
  continuity f x -> continuity g (f x) -> continuity (fun y => g (f y)) x.
Proof.
  move => f g x Cf Cg P BP /= Px.
  case: (Cg P BP Px) => Q BQ Qx QP.
  case: (Cf Q BQ Qx) => R BR Rx RQ.
  exists R => //=.
  move => y Ry.
  by apply QP, RQ.
Qed.

Lemma continuity_comp2 {T U V W X} {TT : TopologicalSpace T} {TU : TopologicalSpace U}
  {TV : TopologicalSpace V} {TW : TopologicalSpace W} {TX : TopologicalSpace X} :
  forall (f : T -> V) (g : U -> W) (h : V -> W -> X) (x : T) (y : U),
  continuity f x -> continuity g y -> 
  continuity (fun z => h (fst z) (snd z)) (f x, g y)
    -> continuity (fun z => h (f (fst z)) (g (snd z))) (x,y).
Proof.
  move => f g h x y Cf Cg Ch P /= BP Pxy.
  case: (Ch P BP Pxy) => /= {Ch} Q BQ Qxy QP.
  case: (BQ _ Qxy) => {BQ} Qv [Qw [BQv [BQw [Qvx [Qwx HQ]]]]].
  case: (Cf Qv BQv Qvx) => {Cf} R BR Rx HR.
  case: (Cg Qw BQw Qwx) => {Cg} S BS Sx HS.
  exists (fun z => R (fst z) /\ S (snd z)) => /=.
  move => z [Rz Sz].
  exists R, S.
  by repeat split.
  by split.
  move => z [Rz Sz].
  apply (QP (f (fst z),g (snd z))).
  apply HQ.
  by apply HR.
  by apply HS.
Qed.

Lemma continuity_fst :
  forall {T U} {TT : TopologicalSpace T} {TU : TopologicalSpace U} (z : T * U),
  continuity (@fst T U) z.
Proof.
intros T U TT TU z P BP Pz.
destruct (basis_true (snd z)) as [Q [BQ Qz]].
exists (fun z => P (fst z) /\ Q (snd z)).
intros x [Px Qx].
exists P, Q.
now repeat split.
now split.
now intros y [Py Qy].
Qed.

Lemma continuity_snd :
  forall {T U} {TT : TopologicalSpace T} {TU : TopologicalSpace U} (z : T * U),
  continuity (@snd T U) z.
Proof.
intros T U TT TU z Q BQ Qz.
destruct (basis_true (fst z)) as [P [BP Pz]].
exists (fun z => P (fst z) /\ Q (snd z)).
intros x [Px Qx].
exists P, Q.
now repeat split.
now split.
now intros y [Py Qy].
Qed.

Lemma continuity_pair :
  forall {T U V} {TT : TopologicalSpace T} {TU : TopologicalSpace U} {TV : TopologicalSpace V}
    {TW : TopologicalSpace (U * V)} {FT : FinerTopology (topology_prod TU TV) TW}
    (f : T -> U) (g : T -> V) (x : T),
  continuity f x ->
  continuity g x ->
  @continuity _ _ _ TW (fun x => (f x, g x)) x.
Proof.
intros T U V TT TU TV TW FT f g x Cf Cg.
apply continuity_finer_topology_r with (1 := FT).
intros P BP Pfg.
destruct (BP _ Pfg) as [Q [R [BQ [BR [Qf [Rg HP]]]]]].
destruct (Cf Q BQ Qf) as [Q' BQ' Q'x Q'f].
destruct (Cg R BR Rg) as [R' BR' R'x R'g].
destruct (basis_and Q' R' BQ' BR' x Q'x R'x) as [P' BP' P'x H'].
exists P' ; try easy.
intros y P'y.
apply HP.
apply Q'f.
now apply H'.
apply R'g.
now apply H'.
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

Definition ball {T} {MT : MetricSpace T} x (eps : posreal) y := distance x y < eps.

Lemma ball_center {T} {TMS : MetricSpace T} :
  forall (x : T) (eps : posreal), ball x eps x.
Proof.
  move => x eps.
  rewrite /ball distance_refl.
  by apply eps.
Qed.

Lemma metric_topological_and :
  forall {T} {MT : MetricSpace T} P Q,
  (exists x eps, forall y : T, ball x eps y <-> P y) ->
  (exists x eps, forall y : T, ball x eps y <-> Q y) ->
  forall x, P x -> Q x ->
  neighborhood_ (fun D => exists x eps, forall y, ball x eps y <-> D y) x (fun y => P y /\ Q y).
Proof.
intros T MT P Q [xP [epsP HP]] [xQ [epsQ HQ]] x Px Qx.
assert (H : 0 < Rmin (epsP - distance xP x) (epsQ - distance xQ x)).
apply Rmin_case.
apply Rlt_Rminus.
now apply HP.
apply Rlt_Rminus.
now apply HQ.
apply (Neighborhood _ _ _ (ball x (mkposreal _ H))).
exists x.
now eexists.
unfold ball.
rewrite distance_refl.
apply cond_pos.
intros y Hy.
split.
apply HP.
apply Rle_lt_trans with (1 := distance_triangle xP x y).
apply Rplus_lt_reg_r with (- distance xP x).
ring_simplify (distance xP x + distance x y + - distance xP x).
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
apply HQ.
apply Rle_lt_trans with (1 := distance_triangle xQ x y).
apply Rplus_lt_reg_r with (- distance xQ x).
ring_simplify (distance xQ x + distance x y + - distance xQ x).
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
Qed.

Lemma metric_topological_true :
  forall {T} {MT : MetricSpace T} (x : T),
  exists P, (exists x eps, forall y, ball x eps y <-> P y) /\ P x.
Proof.
intros T MT x.
exists (ball x (mkposreal 1 Rlt_0_1)).
split.
now exists x, (mkposreal 1 Rlt_0_1).
apply ball_center.
Qed.

Global Instance metric_topological :
  forall T, MetricSpace T -> TopologicalSpace T.
Proof.
intros T MT.
apply (Build_TopologicalSpace _
  (fun D => exists x, exists eps, forall y, ball x eps y <-> D y)).
apply metric_topological_and.
apply metric_topological_true.
Defined.

(* TODO : heritage from neigborhood ? *)

Definition locally_dist {T : Type} (d : T -> R) (P : T -> Prop) :=
  exists delta : posreal, forall y, d y < delta -> P y.
Definition locally {T} {MT : MetricSpace T} (x : T) :=
  locally_dist (distance x).
Definition locally' {T} {MT : MetricSpace T} (x : T) (P : T -> Prop) :=
  locally_dist (distance x) (fun y => y <> x -> P y).

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

Global Instance locally_filter :
  forall T (MT : MetricSpace T) (x : T), ProperFilter (locally x).
Proof.
intros T MT x.
constructor.
  intros P [eps H].
  exists x.
  apply H.
  rewrite distance_refl.
  apply cond_pos.
apply locally_dist_filter.
Qed.

Global Instance locally_compat :
  forall T (MT : MetricSpace T), FilterCompatibility locally.
Proof.
intros T MT.
split.
- intros P x [c [eps B]] Px.
  assert (H := proj2 (B x) Px).
  exists (mkposreal _ (Rlt_Rminus _ _ H)).
  simpl.
  intros z Hz.
  apply B.
  apply Rle_lt_trans with (1 := distance_triangle c x z).
  replace (pos eps) with (distance c x + (eps - distance c x)) by ring.
  now apply Rplus_lt_compat_l.
- intros P x [e He].
  exists (ball x e).
  repeat split.
  exists x.
  now exists e.
  unfold ball.
  rewrite distance_refl.
  apply cond_pos.
  intros y Hy.
  now apply He.
Qed.

Lemma filterlim_locally :
  forall {T U} {MU : MetricSpace U} {F} {FF : Filter F} (f : T -> U) y,
  filterlim f F (locally y) <->
  forall eps : posreal, F (fun x => distance y (f x) < eps).
Proof.
intros T U MU F FF f y.
split.
- intros Cf eps.
  apply (Cf (fun x => distance y x < eps)).
  now exists eps.
- intros Cf P [eps He].
  apply: filter_imp (Cf eps).
  intros t.
  apply He.
Qed.

Lemma locally_open :
  forall {T} {MT : MetricSpace T} x (P : T -> Prop),
  locally x P -> locally x (fun y => locally y P).
Proof.
intros T MT x P [dp Hp].
exists dp.
intros y Hy.
exists (mkposreal _ (Rlt_Rminus _ _ Hy)) => /= z Hz.
apply Hp.
apply Rle_lt_trans with (1 := distance_triangle x y z).
replace (pos dp) with (distance x y + (dp - distance x y)) by ring.
now apply Rplus_lt_compat_l.
Qed.

Lemma locally_singleton :
  forall {T} {MT : MetricSpace T} x (P : T -> Prop),
  locally x P -> P x.
Proof.
intros T MT P x [dp H].
apply H.
rewrite distance_refl.
apply cond_pos.
Qed.

Lemma is_filter_lim_locally :
  forall {T} {MT : MetricSpace T} (x : T),
  is_filter_lim (locally x) x.
Proof.
intros T MT x P [y [eps H]] Px.
assert (Dx: 0 < eps - distance y x).
  apply Rplus_lt_reg_r with (distance y x).
  ring_simplify.
  now apply H.
exists (mkposreal _ Dx).
intros z Dz.
apply H.
apply Rle_lt_trans with (1 := distance_triangle _ x _).
replace (pos eps) with (distance y x + (eps - distance y x)) by ring.
apply Rplus_lt_compat_l with (1 := Dz).
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

Lemma is_filter_lim_filterlim {T} {MT : MetricSpace T}
  (F : (T -> Prop) -> Prop) {FF : Filter F} (x : T) :
  is_filter_lim F x <-> filterlim (fun t => t) F (locally x).
Proof.
  split.
  + move => Hfx P [d Hp].
    rewrite /filtermap.
    apply filter_imp with (1 := Hp).
    apply Hfx.
    by exists x, d.
    rewrite distance_refl ; by apply d.
  + move/filterlim_locally => HF P [y [d HP]] Hpx.
    apply HP, Rminus_lt_0 in Hpx.
    move: (HF FF (mkposreal _ Hpx)).
    apply filter_imp => /= z Hz.
    apply HP.
    apply Rle_lt_trans with (1 := distance_triangle y x z).
    rewrite Rplus_comm ; by apply Rlt_minus_r.
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

Global Instance prod_metric_topology_1 :
  forall T U (MT : MetricSpace T) (MU : MetricSpace U),
  FinerTopology (topology_prod _ _) (metric_topological _ (prod_metric T U _ _)).
Proof.
intros T U MT MU z P [[u v] [eps H]] Pz.
apply neighborhood_basis with (2 := Pz).
intros [x y] Pxy.
exists (ball u eps), (ball v eps).
assert (K := proj2 (H _) Pxy).
repeat split.
now exists u, eps.
now exists v, eps.
apply Rle_lt_trans with (2 := K).
apply Rmax_l.
apply Rle_lt_trans with (2 := K).
apply Rmax_r.
intros p q Hp Hq.
apply H.
unfold ball.
simpl.
unfold dist_prod.
now apply Rmax_case.
Qed.

Global Instance prod_metric_topology_2 :
  forall T U (MT : MetricSpace T) (MU : MetricSpace U),
  FinerTopology (metric_topological _ (prod_metric T U _ _)) (topology_prod _ _).
Proof.
intros T U MT MU z P BP Pz.
destruct (BP _ Pz) as [Q [R [[cQ [eQ BQ]] [[cR [eR BR]] [Qz [Rz H]]]]]].
assert (H': 0 < Rmin (eQ - distance cQ (fst z)) (eR - distance cR (snd z))).
  apply Rmin_case ; apply -> Rminus_lt_0.
  by apply BQ.
  by apply BR.
exists (ball z (mkposreal _ H')).
eexists.
now eexists.
apply ball_center.
intros [x y] B.
apply H.
apply BQ.
apply Rle_lt_trans with (1 := distance_triangle cQ (fst z) x).
apply Rplus_lt_reg_r with (- distance cQ (fst z)).
rewrite Rplus_comm -Rplus_assoc Rplus_opp_l Rplus_0_l.
apply Rlt_le_trans with (2 := Rmin_l _ (eR - distance cR (snd z))).
apply Rle_lt_trans with (2 := B).
apply Rmax_l.
apply BR.
apply Rle_lt_trans with (1 := distance_triangle cR (snd z) y).
apply Rplus_lt_reg_r with (- distance cR (snd z)).
rewrite Rplus_comm -Rplus_assoc Rplus_opp_l Rplus_0_l.
apply Rlt_le_trans with (2 := Rmin_r (eQ - distance cQ (fst z)) _).
apply Rle_lt_trans with (2 := B).
apply Rmax_r.
Qed.

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

Class CompleteMetricSpace_mixin T (MT : MetricSpace T) := {
  cauchy := fun (F : (T -> Prop) -> Prop) => forall eps, exists x, F (ball x eps) ;
  complete_cauchy : forall F, ProperFilter F -> cauchy F -> {x : T | is_filter_lim F x}
}.

Class CompleteMetricSpace T := {
  complete_metric :> MetricSpace T ;
  complete_mixin :> CompleteMetricSpace_mixin T complete_metric
}.

Lemma cauchy_distance :
  forall {T} {MT : MetricSpace T} {F} {FF : ProperFilter F},
  (forall eps, exists x, F (ball x eps)) <->
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> distance u v < eps).
Proof.
  intros T MT F FF.
  split.

  intros H eps.
  case: (H (pos_div_2 eps)) => {H} x Hx.
  exists (ball x (pos_div_2 eps)).
  split.
  by [].
  move => u v Hu Hv.
  apply Rle_lt_trans with (1 := distance_triangle _ x _).
  rewrite (double_var eps).
  apply Rplus_lt_compat.
  rewrite distance_comm ; by apply Hu.
  by apply Hv.

  intros H eps.
  case: (H eps) => {H} P [HP H].
  destruct (filter_ex P HP) as [x Hx].
  exists x.
  move: (fun v => H x v Hx) => {H} H.
  apply filter_imp with (1 := H).
  by [].
Qed.

Lemma filterlim_locally_cauchy :
  forall {T U} {CU : CompleteMetricSpace U} {F} {FF : ProperFilter F} (f : T -> U),
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> distance (f u) (f v) < eps) <->
  exists y, filterlim f F (locally y).
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
    refine (_ (Hy (ball y eps) _ _)).
    unfold filtermap.
    apply filter_imp.
    intros x Hx.
    now apply HP.
    exists y.
    now exists eps.
    unfold ball.
    rewrite distance_refl.
    apply cond_pos.
- intros [y Hy] eps.
  exists (fun x => ball y (pos_div_2 eps) (f x)).
  split.
  apply Hy.
  now exists (pos_div_2 eps).
  intros u v Hu Hv.
  apply Rle_lt_trans with (1 := distance_triangle (f u) y (f v)).
  rewrite (double_var eps).
  apply Rplus_lt_compat.
  rewrite distance_comm.
  exact Hu.
  exact Hv.
Qed.

Lemma complete_cauchy_UnifFct {T U} {CMS : CompleteMetricSpace U} : 
  let MS := MetricSpace_UnifFct _ in
  forall F : ((T -> U) -> Prop) -> Prop,
  ProperFilter F ->
    (forall eps : posreal, exists f : T -> U, F (ball f eps)) ->
    {f : T -> U | is_filter_lim F f}.
Proof.
  move => MS F FF HFc.
  
  cut ({f | forall eps : posreal, F (fun g => distance f g < eps)}).
    case => f Hf.
    exists f.
    apply is_filter_lim_filterlim.
    by apply FF.
    by apply filterlim_locally.

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
    apply (Rbar_le_lt_trans (distance (f t) (g t)) (Lub_Rbar_ne _ (UnifFct_dist_ne f g)) eps).
      rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l ; simpl => Hl.
      apply Hl.
      right ; by exists t.
      by apply H.
      by apply Rlt_le.
  assert (Hex : forall t, {x | is_filter_lim (Fr t) x}).
    move => t.
    apply: complete_cauchy.
    apply: (HFrc t).
  set f := fun t => projT1 (Hex t) ; exists f.

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
    apply (projT2 (Hex t)).

  generalize (proj1 cauchy_distance HFc) => {HFc} HFc.

  case: (HFc (pos_div_2 eps)) => {HFc} P ; simpl ; case => HP H0.
  apply filter_imp with (2 := HP).
  move => g Hg t.
  move: (fun h => H0 g h Hg) => {H0} H0.
  move: (H t (pos_div_2 eps)) ; simpl => {H} H.
  unfold Fr in H ; generalize (filter_and _ _ H HP) => {H} H.
  apply filter_ex in H ; case: H => h H.
  apply Rle_lt_trans with (1 := distance_triangle (f t) (h t) (g t)).
  rewrite (double_var eps).
  apply Rplus_lt_compat.
  by apply H.
  move: (H0 _ (proj2 H)) => {H0} H0.
  apply Rle_lt_trans with (2 := H0).
  rewrite distance_comm.
  apply: (UnifFct_dist_ge_fct g h t).
  apply Rlt_le_trans with (1 := H0).
  apply Rle_div_l.
  by apply Rlt_0_2.
  apply Rle_trans with (1 := Heps), Rminus_le_0 ; ring_simplify ; by apply Rle_0_1.
Qed.

Lemma CompleteMetricSpace_UnifFct {T U} : 
  CompleteMetricSpace U -> CompleteMetricSpace (T -> U).
Proof.
  intros.
  apply Build_CompleteMetricSpace with (MetricSpace_UnifFct _).
  constructor.
  by apply complete_cauchy_UnifFct.
Defined.



(** ** Topological Abelian Groups *)

Class TopologicalAbelianGroup_mixin G (AG : AbelianGroup G) (TG : TopologicalSpace G) := {
  continuity_plus' : forall z : G * G, continuity (fun z => plus (fst z) (snd z)) z ;
  continuity_opp : forall x : G, continuity opp x
}.

Class TopologicalAbelianGroup G := {
  tagroup_abelian :> AbelianGroup G ;
  tagroup_topological :> TopologicalSpace G ;
  tagroup_mixin :> TopologicalAbelianGroup_mixin G tagroup_abelian tagroup_topological
}.

Lemma continuity_plus :
  forall {G} {TAG : TopologicalAbelianGroup G} {TG2 : TopologicalSpace (G * G)}
    {FT : FinerTopology TG2 (topology_prod _ _)} (x : G * G),
  @continuity _ _ TG2 _ (fun y => plus (fst y) (snd y)) x.
Proof.
intros G TAG TG2 FT x.
apply (continuity_finer_topology_l _ _ (FT := FT)).
apply continuity_plus'.
Qed.

Lemma continuity_minus :
  forall {G} {TAG : TopologicalAbelianGroup G} {TG2 : TopologicalSpace (G * G)}
    {FT : FinerTopology TG2 (topology_prod _ _)} (x : G * G),
  @continuity _ _ TG2 _ (fun y => minus (fst y) (snd y)) x.
Proof.
intros G TAG TG2 FT x.
apply (continuity_finer_topology_l _ _ (FT := FT)).
apply (fun H => continuity_comp (fun x => (fst x, opp (snd x))) _ x H (continuity_plus' _)).
apply continuity_pair.
apply continuity_fst.
apply continuity_comp.
apply continuity_snd.
apply continuity_opp.
Qed.

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
  cnagroup_complete :> CompleteMetricSpace_mixin T _
}.

Global Instance CompleteNormedAbelianGroup_NormedAbelianGroup {U} :
  CompleteNormedAbelianGroup U -> NormedAbelianGroup U.
Proof.
  case ; intros.
  econstructor.
  exact cnagroup_pnormed0.
Defined.

Global Instance CompleteNormedAbelianGroup_CompleteMetricSpace {U} :
  CompleteNormedAbelianGroup U -> CompleteMetricSpace U.
Proof.
  case ; intros.
  econstructor.
  exact cnagroup_complete0.
Defined.

(** ** Continuity in Normed Abelian Groups *)

Lemma NormedAbelianGroup_continuity_opp {T} {NAG : NormedAbelianGroup T} :
  forall (x : T), continuity opp x.
Proof.
  move => x.
  apply -> (is_filter_lim_continuity opp x).
  move => F HF Hx P [y [d HP]] Pfx.
  apply (Hx (fun x => P (opp x))).
  exists (opp y), d => z ; split => H.
  apply HP.
  move: H ; unfold ball, distance ; simpl.
  by rewrite /minus opp_opp -opp_plus pnorm_opp.
  apply HP in H ; move: H.
  unfold ball, distance ; simpl.
  by rewrite /minus opp_opp -opp_plus pnorm_opp.
  by [].
Qed.

Lemma NormedAbelianGroup_continuity_plus {T} {NAG : NormedAbelianGroup T} :
  forall (x : T * T), continuity (TU := topology_prod _ _) (fun y => plus (fst y) (snd y)) x.
Proof.
  move => x.
  eapply continuity_finer_topology_l.
  apply prod_metric_topology_1.
  apply -> (is_filter_lim_continuity (fun y : T * T => plus (fst y) (snd y)) x).
  move => F HF Hx P [y [d HP]] Pfx.
  apply HP in Pfx.
  apply Rminus_lt_0 in Pfx.
  assert (H : F (ball x (pos_div_2 (mkposreal _ Pfx)))).
    apply Hx.
    by exists x, (pos_div_2 (mkposreal _ Pfx)).
    by apply ball_center.
  move: H.
  unfold filtermap ; apply filter_imp => z Hz.
  apply HP.
  apply Rle_lt_trans with (1 := distance_triangle _ (plus (fst x) (snd x)) _).
  simpl.
  rewrite Rplus_comm.
  apply Rlt_minus_r.
  rewrite /ball /= /dist_prod in Hz.
  apply Rlt_div_r in Hz.
  apply Rle_lt_trans with (2 := Hz).
  rewrite Rmult_comm.
  replace (minus (plus (fst z) (snd z)) (plus (fst x) (snd x)))
    with (plus (minus (fst z) (fst x)) (minus (snd z) (snd x))).
  apply Rle_trans with (1 := pnorm_triangle _ _).
  by apply Rplus_le_Rmax.
  case: (x) => /= xx xy ; case (z) => /= zx zy.
  rewrite /minus opp_plus -?plus_assoc.
  apply f_equal.
  rewrite ?plus_assoc.
  apply f_equal2.
  apply plus_comm.
  by [].
  by apply Rlt_0_2.
Qed.

Global Instance NormedAbelianGroup_TopologicalAbelianGroup :
  forall G, NormedAbelianGroup G -> TopologicalAbelianGroup G.
Proof.
intros G NAG.
econstructor.
constructor.
apply NormedAbelianGroup_continuity_plus.
apply NormedAbelianGroup_continuity_opp.
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

Lemma CompleteNormedAbelianGroup_UnifFct {T U} :
  CompleteNormedAbelianGroup U -> CompleteNormedAbelianGroup (T -> U).
Proof.
  case ; intros.
  set (nagf := @NAG_UnifFct T U cnagroup_nag0).
  unfold NAG_UnifFct in nagf.
  exists (AbelianGroup_fct _ _ cnagroup_abelian0) (@nagroup_mixin _ nagf).
  constructor.
  intros F FF H'.
  assert (H := @complete_cauchy_UnifFct T U (Build_CompleteMetricSpace U (@NormedAbelianGroup_MetricSpace U cnagroup_nag0) cnagroup_complete0) F FF).
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

Lemma nat_topology_and : forall P Q : nat -> Prop,
  eventually P ->
  eventually Q ->
  forall x : nat,
  P x -> Q x -> neighborhood_ eventually x (fun y : nat => P y /\ Q y).
Proof.
  move => P Q [NP HP] [NQ HQ] x Px Qx.
  apply Neighborhood with (fun y : nat => P y /\ Q y).
  exists (NP + NQ)%nat => n Hn.
  split.
  by apply HP, le_trans with (2 := Hn), le_plus_l.
  by apply HQ, le_trans with (2 := Hn), le_plus_r.
  by split.
  by auto.
Qed.
Lemma nat_topology_true : forall n : nat,
  exists P : nat -> Prop, eventually P /\ P n.
Proof.
  move => n.
  exists (fun m => (n <= m)%nat) ; split.
  by exists n.
  by apply le_refl.
Qed.
Global Instance nat_TopologicalSpace :
  TopologicalSpace nat.
Proof.
  apply Build_TopologicalSpace with eventually.
  exact nat_topology_and.
  exact nat_topology_true.
Defined.

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

Global Instance R_SeparatedSpace : SeparatedSpace R.
Proof.
  apply (Build_SeparatedSpace R _).
  move => x y Hxy.
  apply sym_not_eq, Rminus_eq_contra in Hxy.
  apply Rabs_pos_lt in Hxy.
  exists (ball x (pos_div_2 (mkposreal _ Hxy))) (ball y (pos_div_2 (mkposreal _ Hxy))).
  + exists x ; by exists (pos_div_2 (mkposreal _ Hxy)).
  + exists y ; by exists (pos_div_2 (mkposreal _ Hxy)).
  + by apply ball_center.
  + by apply ball_center.
  + unfold ball ; move => /= z Hxz Hyz.
    apply (Rlt_irrefl (distance x y)).
    apply Rle_lt_trans with (1 := distance_triangle x z y).
    rewrite (double_var (distance x y)).
    apply Rplus_lt_compat.
    by apply Hxz.
    rewrite distance_comm ; by apply Hyz.
Defined.

Lemma R_complete :
  forall F : (R -> Prop) -> Prop,
  ProperFilter F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  {x : R | is_filter_lim F x}.
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
intros P [y [eps BP]] Px.
assert (H : 0 < Rmin ((y + eps) - (x - 1)) ((x - 1) - (y - eps))).
  apply Rmin_case.
  apply Rplus_lt_reg_r with (x - 1 - y).
  rewrite Rplus_0_l.
  ring_simplify (y + eps - (x - 1) + (x - 1 - y)).
  apply Rabs_lt_between.
  now apply BP.
  apply Rplus_lt_reg_r with (-eps).
  rewrite Rplus_0_l.
  replace (x - 1 - (y - eps) + - eps) with (x - 1 - y) by ring.
  apply (Rabs_lt_between (x - 1 - y)).
  now apply BP.
set (eps' := pos_div_2 (mkposreal _ (Rmin_case _ _ _ Rlt_R0_R2 H))).
set (eps'' := (Rmin 2 (Rmin (y + eps - (x - 1)) (x - 1 - (y - eps))))).
fold eps'' in eps'.
destruct (HF eps') as [z Hz].
assert (H1 : z - eps'' / 2 + 1 <= x).
  apply Hx1.
  revert Hz.
  unfold E.
  apply filter_imp.
  intros u Bu.
  apply (Rabs_lt_between' u z) in Bu.
  apply Rabs_lt_between'.
  simpl in Bu |- *.
  clear -Bu.
  destruct Bu as [Bu1 Bu2].
  assert (H := Rmin_l 2 (Rmin (y + eps - (x - 1)) (x - 1 - (y - eps)))).
  fold eps'' in H.
  split ; Fourier.fourier.
assert (H2 : x <= z + eps'' / 2 + 1).
  apply Hx2.
  intros v Hv.
  apply filter_const.
  generalize (filter_and _ _ Hz Hv).
  apply filter_imp.
  intros w [Hw1 Hw2].
  apply (Rabs_lt_between' w z) in Hw1.
  destruct Hw1 as [_ Hw1].
  apply (Rabs_lt_between' w v) in Hw2.
  destruct Hw2 as [Hw2 _].
  clear -Hw1 Hw2.
  simpl in Hw1, Hw2.
  Fourier.fourier.
revert Hz.
apply filter_imp.
intros u Hu.
apply BP.
apply (Rabs_lt_between' u z) in Hu.
apply Rabs_lt_between'.
assert (eps'' <= y + eps - (x - 1)).
  apply Rle_trans with (1 := Rmin_r _ _).
  apply Rmin_l.
assert (eps'' <= x - 1 - (y - eps)).
  apply Rle_trans with (1 := Rmin_r _ _).
  apply Rmin_r.
simpl in H2, Hu.
clear -H2 Hu H0 H1 H3.
destruct Hu.
split ; Fourier.fourier.
Qed.

Global Instance R_complete_metric : CompleteMetricSpace R.
Proof.
apply (Build_CompleteMetricSpace R _).
constructor.
apply R_complete.
Defined.

Notation at_left x := (within (fun u : R => Rlt u x) (locally (x)%R)).
Notation at_right x := (within (fun u : R => Rlt x u) (locally (x)%R)).

Lemma open_lt :
  forall (y : R), open (fun (u : R) => u < y).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
apply (Neighborhood _ _ _ (ball x (mkposreal _ Hxy))).
- exists x.
  now eexists.
- unfold ball.
  now rewrite distance_refl.
- unfold ball.
  simpl.
  intros u Hu.
  apply Rabs_lt_between in Hu.
  apply Rplus_lt_reg_r with (1 := proj2 Hu).
Qed.

Lemma open_gt :
  forall (y : R), open (fun (u : R) => y < u).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
apply (Neighborhood _ _ _ (ball x (mkposreal _ Hxy))).
- exists x.
  now eexists.
- unfold ball.
  now rewrite distance_refl.
- unfold ball.
  simpl.
  intros u Hu.
  apply Rabs_lt_between in Hu.
  apply Rplus_lt_reg_r with (- x).
  generalize (proj1 Hu).
  now rewrite Ropp_minus_distr.
Qed.

Lemma open_neq :
  forall (y : R), open (fun (u : R) => u <> y).
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

(** Continuity of distance and norm *)

Lemma continuity_distance :
  forall {T} {MT : MetricSpace T} (z : T * T),
  continuity (fun z => distance (fst z) (snd z)) z.
Proof.
intros T MT [x y] P [c [eps BP]] H.
set (d := eps - Rabs (distance x y - c)).
assert (Hd: 0 < d).
  apply BP in H.
  apply Rlt_Rminus.
  apply H.
exists (ball (x, y) (pos_div_2 (mkposreal _ Hd))).
now eexists ; eexists.
apply ball_center.
intros [u v] Huv.
apply BP.
unfold ball.
simpl.
replace (distance u v + - c) with (distance u v - distance x y + (distance x y - c)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_lt_reg_r with (- Rabs (distance x y - c)).
rewrite Rplus_assoc Rplus_opp_r Rplus_0_r.
apply Rle_lt_trans with (distance u x + distance v y).
- apply Rabs_le_between'.
  split.
  + apply Rplus_le_reg_r with (distance u x + distance v y).
    unfold Rminus.
    rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
    apply Rle_trans with (1 := distance_triangle x u y).
    rewrite distance_comm.
    apply Rplus_le_reg_l with (- distance u x).
    ring_simplify.
    apply distance_triangle.
  + apply Rle_trans with (1 := distance_triangle u x v).
    apply Rplus_le_reg_l with (- distance u x).
    ring_simplify.
    rewrite (distance_comm v).
    apply distance_triangle.
- apply Rle_lt_trans with (2 * Rmax (distance u x) (distance v y)).
  + rewrite Rmult_plus_distr_r Rmult_1_l.
    apply Rplus_le_compat.
    apply Rmax_l.
    apply Rmax_r.
  + apply Rmult_lt_reg_r with (1 := pos_half_prf).
    rewrite -> Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l.
    rewrite (distance_comm u x) (distance_comm v y).
    exact Huv.
    apply Rgt_not_eq, Rlt_0_2.
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
apply locally_open in LP.
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
apply: locally_singleton LP.
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
apply: locally_singleton H.
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
- intros x _.
  exists (ball x (mkposreal _ Rlt_0_1)).
  exists x.
  now eexists.
  unfold ball.
  rewrite distance_refl.
  apply cond_pos.
  easy.
- apply open_false.
Qed.

Lemma open_Rbar_gt :
  forall y, open (fun u : R => Rbar_lt y u).
Proof.
intros [y| |].
- apply open_gt.
- apply open_false.
- intros x _.
  exists (ball x (mkposreal _ Rlt_0_1)).
  exists x.
  now eexists.
  unfold ball.
  rewrite distance_refl.
  apply cond_pos.
  easy.
Qed.

Lemma open_Rbar_lt' :
  forall x y, Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof.
intros [x| |] y Hxy.
- change (locally x (fun u => Rbar_lt u y)).
  apply filter_open with (2 := Hxy).
  apply open_Rbar_lt.
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
- change (locally x (fun u => Rbar_lt y u)).
  apply filter_open with (2 := Hxy).
  apply open_Rbar_gt.
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
rewrite distance_refl.
apply cond_pos.
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

Lemma continuity_Reals (f : R -> R) (x : R) :
  continuity f x <-> continuity_pt f x.
Proof.
  rewrite continuity_pt_locally.
  split => Cf.
  - move => eps.
    case: (Cf (ball (f x) eps)).
    by exists (f x), eps.
    by apply ball_center.
    move => P [y [d BP]] Px HP.
    apply BP in Px.
    apply Rminus_lt_0 in Px.
    exists (mkposreal _ Px) => z /= Hz.
    apply HP, BP.
    rewrite /ball /=.
    generalize (distance_triangle y x z) => /= H.
    apply Rle_lt_trans with (1 := H) => {H}.
    rewrite Rplus_comm ; by apply Rlt_minus_r.
  - move => P [y [eps BP]] Px.
    apply BP in Px.
    apply Rminus_lt_0 in Px.
    case: (Cf (mkposreal _ Px)) => delta {Cf} Cf.
    exists (ball x delta).
    by exists x, delta.
    by apply ball_center.
    move => z Hz.
    apply BP.
    rewrite /ball.
    apply Rle_lt_trans with (1 := distance_triangle _ (f x) _).
    rewrite Rplus_comm ; apply Rlt_minus_r.
    by apply Cf.
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
apply: filterlim_locally.
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
apply: filterlim_locally.
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
