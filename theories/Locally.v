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

Require Import Reals Rbar.
Require Import ssreflect.
Require Import Rcomplements.
Require Import List.

Open Scope R_scope.

(** * Definitions *)

Class Filter {T : Type} (F : (T -> Prop) -> Prop) := {
  filter_true : F (fun _ => True) ;
  filter_and : forall P Q : T -> Prop, F P -> F Q -> F (fun x => P x /\ Q x) ;
  filter_imp : forall P Q : T -> Prop, (forall x, P x -> Q x) -> F P -> F Q
}.

Lemma filter_forall :
  forall {T : Type} F {FF: @Filter T F} (P : T -> Prop),
  (forall x, P x) -> F P.
Proof.
intros.
apply filter_imp with (fun _ => True).
easy.
apply filter_true.
Qed.

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

Global Instance filtermap_filter : forall T U f F, @Filter T F ->
  @Filter U (filtermap f F).
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

Definition filterlim {T U : Type} (f : T -> U) F G :=
  filter_le (filtermap f F) G.

Lemma filterlim_compose :
  forall T U V (f : T -> U) (g : U -> V) F G H,
  filterlim f F G -> filterlim g G H ->
  filterlim (fun x => g (f x)) F H.
Proof.
intros T U V f g F G H FG GH P HP.
unfold filtermap.
apply (FG (fun x => P (g x))).
now apply GH.
Qed.

Lemma filterlim_ext_loc :
  forall T U (f g : T -> U) (F G : _ -> Prop),
  Filter F ->
  F (fun x => f x = g x) ->
  filterlim f F G ->
  filterlim g F G.
Proof.
intros T U f g F G HF Efg Lf P GP.
specialize (Lf P GP).
unfold filtermap.
generalize (filter_and _ _ Efg Lf).
apply filter_imp.
now intros x [-> H].
Qed.

Definition locally x (P : R -> Prop) :=
  exists delta : posreal, forall y, Rabs (y - x) < delta -> P y.

Global Instance locally_filter : forall x, Filter (locally x).
Proof.
intros x.
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

Definition eventually (P : nat -> Prop) :=
  exists N : nat, forall n, (N <= n)%nat -> P n.

Global Instance eventually_filter : Filter eventually.
Proof.
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

Definition within {T : Type} D (F : (T -> Prop) -> Prop) (P : T -> Prop) :=
  F (fun x => D x -> P x).

Global Instance within_filter : forall T D F, Filter F -> Filter (@within T D F).
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

Notation at_left x := (within (fun u : R => Rlt u x) (locally x)).
Notation at_right x := (within (fun u : R => Rlt x u) (locally x)).

Definition locally_2d (P : R -> R -> Prop) x y :=
  exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.

(** * Logical connective *)

Lemma locally_align :
  forall (P Q : R -> Prop) x,
  ( forall eps : posreal, (forall v, Rabs (v - x) < eps -> P v) ->
    forall u, Rabs (u - x) < eps -> Q u ) ->
  locally x P -> locally x Q.
Proof.
intros P Q x K (d,H).
exists d => y Hy.
now apply (K d).
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

Lemma locally_impl_strong :
  forall (P Q : R -> Prop) x, locally x (fun y => locally y P -> Q y) ->
  locally x P -> locally x Q.
Proof.
intros P Q x (dpq,Hpq) (dp,Hp).
exists (mkposreal _ (Rmin_stable_in_posreal dp dpq)) => /= y Hy.
apply Hpq.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
set (d := mkposreal _ (Rlt_Rminus _ _ Hy)).
exists d => z Hz.
apply Hp.
replace (z - x) with ((z - y) + (y - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos dp) with (d + (dp - d)) by ring.
apply Rplus_lt_le_compat with (1 := Hz).
simpl.
apply Rplus_le_reg_r with (- (Rabs (y - x))).
ring_simplify.
apply Rge_le.
apply Rge_minus.
apply Rle_ge.
apply Rmin_l.
Qed.

Lemma locally_2d_impl_strong :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => locally_2d P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y (dpq,Hpq) (dp,Hp).
exists (mkposreal _ (Rmin_stable_in_posreal dp dpq)) => /= u v Hu Hv.
apply Hpq.
apply Rlt_le_trans with (1 := Hu).
apply Rmin_r.
apply Rlt_le_trans with (1 := Hv).
apply Rmin_r.
assert (Huv: Rmax (Rabs (u - x)) (Rabs (v - y)) < Rmin dp dpq).
now apply Rmax_case.
set (d := mkposreal _ (Rlt_Rminus _ _ Huv)).
exists d => w z Hw Hz.
apply Hp.
replace (w - x) with ((w - u) + (u - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos dp) with (d + (dp - d)) by ring.
apply Rplus_lt_le_compat with (1 := Hw).
simpl.
apply Rplus_le_reg_r with (- Rmax (Rabs (u - x)) (Rabs (v - y))).
ring_simplify.
apply Rle_trans with R0.
apply Rle_minus.
apply Rmax_l.
apply Rge_le.
apply Rge_minus.
apply Rle_ge.
apply Rmin_l.
replace (z - y) with ((z - v) + (v - y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos dp) with (d + (dp - d)) by ring.
apply Rplus_lt_le_compat with (1 := Hz).
simpl.
apply Rplus_le_reg_r with (- Rmax (Rabs (u - x)) (Rabs (v - y))).
ring_simplify.
apply Rle_trans with R0.
apply Rle_minus.
apply Rmax_r.
apply Rge_le.
apply Rge_minus.
apply Rle_ge.
apply Rmin_l.
Qed.

Lemma locally_singleton :
  forall (P : R -> Prop) x, locally x P -> P x.
Proof.
intros P x (D,H).
apply H.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
Qed.

Lemma locally_2d_singleton :
  forall (P : R -> R -> Prop) x y, locally_2d P x y -> P x y.
Proof.
intros P x y (D,H).
apply H ;
  rewrite /Rminus Rplus_opp_r Rabs_R0 ;
  apply cond_pos.
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

Lemma locally_2d_1d_const_x :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally y (fun t => P x t).
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
now apply locally_singleton in H.
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

Lemma continuity_pt_filterlim :
  forall f x,
  continuity_pt f x <->
  filterlim f (locally x) (locally (f x)).
Proof.
intros f x.
split.
intros Cf P [eps He].
destruct (proj1 (continuity_pt_locally f x) Cf eps) as [d Hd].
exists d => y Hy.
apply He.
now apply Hd.
intros H.
apply continuity_pt_locally.
intros eps.
destruct (H (fun y => Rabs (y - f x) < eps)) as [d Hd].
now exists eps.
exists d.
intros y Hy.
apply Hd.
now apply Hy.
Qed.

(** * Intervals *)

Lemma locally_interval (P : R -> Prop) (x : R) (a b : Rbar) :
  Rbar_lt a x -> Rbar_lt x b 
  -> (forall (y : R), Rbar_lt a y -> Rbar_lt y b -> P y)
    -> locally x P.
Proof.
  move => Hax Hxb Hp.
  case: (Rbar_lt_locally _ _ _ Hax Hxb) => d Hd.
  exists d => y Hy.
  apply Hp ; by apply Hd.
Qed.

(** * Continuity *)

Lemma locally_comp' (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x
  -> locally x (fun x => P (f x)).
Proof.
intros Lf Cf.
apply continuity_pt_filterlim in Cf.
now apply Cf.
Qed.

Lemma locally_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x
  -> locally x (fun x => P (f x)).
Proof.
  move => Hp Hf.
  case: Hp => eps Hp.
  case: (Hf eps) => {Hf} [ | d [Hd Hf]].
  by apply eps.
  exists (mkposreal _ Hd) => /= y Hy.
  apply Hp.
  case: (Req_dec x y) => [<- | Hxy].
  rewrite Rminus_eq_0 Rabs_R0 ; apply eps.
  apply Hf ; repeat split ; intuition.
Qed.


(** * locally in Set *)

Require Import Markov Lub.


Lemma locally_ex_dec: forall P x, (forall x, P x \/ ~P x) -> locally x P -> {d:posreal| forall y, Rabs (y-x) < d -> P y}.
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


Lemma derivable_pt_lim_locally :
  forall f x l,
  derivable_pt_lim f x l <->
  forall eps : posreal, locally x (fun y => y <> x -> Rabs ((f y - f x) / (y - x) - l) < eps).
Proof.
intros f x l.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d H].
exists d => y Hy Zy.
specialize (H (y - x) (Rminus_eq_contra _ _ Zy) Hy).
now ring_simplify (x + (y - x)) in H.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d => h Zh Hh.
specialize (H (x + h)).
ring_simplify (x + h - x) in H.
apply H => //.
contradict Zh.
apply Rplus_eq_reg_l with x.
now rewrite Rplus_0_r.
Qed.

(** * Rbar_locally *)

Definition Rbar_locally (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => exists delta : posreal, 
	forall x, Rabs (x-a) < delta -> x <> a -> P x
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.

Global Instance Rbar_locally_filter : forall x, Filter (Rbar_locally x).
Proof.
intros [x| |] ; constructor.
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

Definition Rbar_locally' (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => exists delta : posreal,
	forall x, Rabs (x-a) < delta -> P x
    | p_infty => exists M : R, forall x, M < x -> P x
    | m_infty => exists M : R, forall x, x < M -> P x
  end.

Global Instance Rbar_locally'_filter : forall x, Filter (Rbar_locally' x).
Proof.
intros [x| |].
- apply locally_filter.
- exact (Rbar_locally_filter p_infty).
- exact (Rbar_locally_filter m_infty).
Qed.

Lemma Rbar_locally_const (a : Rbar) (P : Prop) :
  Rbar_locally a (fun _ => P) -> P.
Proof.
  case: a => [a | | ] [d H].
  apply (H (a+d/2)).
  ring_simplify (a + d / 2 - a).
  rewrite Rabs_pos_eq.
  apply Rminus_lt_0.
  field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  apply Rlt_le, is_pos_div_2.
  apply Rgt_not_eq, Rminus_lt_0 ; ring_simplify.
  by apply is_pos_div_2.
  apply (H (d+1)).
  by apply Rlt_plus_1.
  apply (H (d-1)).
  by apply Rlt_minus_l, Rlt_plus_1.
Qed.

Lemma Rbar_locally_and_1 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally a (fun x => P x /\ Q x)
    -> Rbar_locally a P.
Proof.
  case: a => /= [a | | ] [d0 Hp] ;
  exists d0 => H ; by apply Hp.
Qed.

Lemma Rbar_locally_and_2 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally a (fun x => P x /\ Q x)
    -> Rbar_locally a Q.
Proof.
  case: a => /= [a | | ] [d0 Hp] ;
  exists d0 => H ; by apply Hp.
Qed.

Lemma Rbar_locally_or_1 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally a P -> Rbar_locally a (fun x => P x \/ Q x).
Proof.
  apply filter_imp => x Hx.
  by left.
Qed.

Lemma Rbar_locally_or_2 (P Q : R -> Prop) (a : Rbar) :
  Rbar_locally a Q -> Rbar_locally a (fun x => P x \/ Q x).
Proof.
  apply filter_imp => x Hx.
  by right.
Qed.

(** A particular sequence converging to a point *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + / (INR n + 1)
    | p_infty => INR n
    | m_infty => - INR n
  end.

Lemma Rbar_loc_seq_carac (P : R -> Prop) (x : Rbar) :
  Rbar_locally x P
    -> (exists N, forall n, (N <= n)%nat -> P (Rbar_loc_seq x n)).
Proof.
  case: x => /= [x | | ] [delta Hp].
(* x \in R *)
  case: (nfloor_ex (/delta)) => [ | N [_ HN]].
  by apply Rlt_le, Rinv_0_lt_compat, delta.
  exists N => n Hn.
  apply Hp.
  ring_simplify (x + / (INR n + 1) - x).
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
