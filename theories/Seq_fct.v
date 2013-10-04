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

Require Import Reals ssreflect Rbar.
Require Import Rcomplements Locally.
Require Import Limit Continuity Derive Series.

Open Scope R_scope.

(** * Sequence of functions *)

(** ** Definitions *)

Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) :=
  forall x : R, D x -> ex_finite_lim_seq (fun n => fn n x).

Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) :=
  forall eps : posreal, eventually (fun n => forall x : R,
    D x -> Rabs ((fn n x) - real (Lim_seq (fun n => fn n x))) < eps).
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) :=
  forall eps : posreal, exists N : nat,
  forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat
    -> Rabs (fn n x - fn m x) < eps.

(** Equivalence with standard library *)

Lemma CVU_dom_Reals (fn : nat -> R -> R) (f : R -> R) (x : R) (r : posreal) :
  (forall y, (Boule x r y) -> (Finite (f y)) = Lim_seq (fun n => fn n y)) ->
  (CVU fn f x r <-> CVU_dom fn (Boule x r)).
Proof.
  split ; move => Hcvu.
  have Hf : forall y, Boule x r y -> is_lim_seq (fun n => fn n y) (f y).
    move => y Hy.
    apply is_lim_seq_spec.
    move => [e He] /=.
    case: (Hcvu e He) => {Hcvu} N Hcvu.
    exists N => n Hn.
    rewrite -Ropp_minus_distr' Rabs_Ropp.
    by apply Hcvu.
  move => [e He] /=.
  case: (Hcvu e He) => {Hcvu} N Hcvu.
  exists N => n Hn y Hy.
  rewrite (is_lim_seq_unique (fun n0 : nat => fn n0 y) _ (Hf y Hy)).
  simpl.
  rewrite -/(Rminus (fn n y) (f y)) -Ropp_minus_distr' Rabs_Ropp.
  by apply Hcvu.

  move => e He ; set eps := mkposreal e He.
  case: (Hcvu eps) => {Hcvu} N Hcvu.
  exists N => n y Hn Hy.
  move: (Hcvu n Hn y Hy).
  rewrite -(H y Hy) /=.
  by rewrite -Ropp_minus_distr' Rabs_Ropp.
Qed.

(** Various inclusions and equivalences between definitions *)

Lemma CVU_CVS_dom (fn : nat -> R -> R) (D : R -> Prop) :
  CVU_dom fn D -> CVS_dom fn D.
Proof.
  move => Hcvu x Hx.
  exists (real (Lim_seq (fun n => fn n x))).
  apply is_lim_seq_spec.
  intros eps.
  case: (Hcvu eps) => {Hcvu} N Hcvu.
  exists N => n Hn.
  by apply Hcvu.
Qed.
Lemma CVU_dom_cauchy (fn : nat -> R -> R) (D : R -> Prop) :
  CVU_dom fn D <-> CVU_cauchy fn D.
Proof.
  split => H eps.
(* CVU_dom -> CVU_cauchy *)
  case: (H (pos_div_2 eps)) => {H} N /= H.
  exists N => n m x Hx Hn Hm.
  rewrite (double_var eps).
  replace (fn n x - fn m x)
    with ((fn n x - real (Lim_seq (fun n0 : nat => fn n0 x)))
      - (fn m x - real (Lim_seq (fun n0 : nat => fn n0 x))))
    by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _) ; rewrite Rabs_Ropp.
  apply Rplus_lt_compat ; by apply H.
(* CVU_cauchy -> CVU_dom *)
  rewrite /Lim_seq.
  case: (H (pos_div_2 eps)) => {H} N /= H.
  exists N => n Hn x Hx.
  rewrite /LimSup_seq ; case: ex_LimSup_seq ; case => [ls | | ] /= Hls.
  rewrite /LimInf_seq ; case: ex_LimInf_seq ; case => [li | | ] /= Hli.
  replace (fn n x - (ls + li) / 2)
    with (((fn n x - ls) + (fn n x - li))/2)
    by field.
  rewrite Rabs_div ; [ | by apply Rgt_not_eq, Rlt_R0_R2].
  rewrite (Rabs_pos_eq 2) ; [ | by apply Rlt_le, Rlt_R0_R2].
  rewrite Rlt_div_l ; [ | by apply Rlt_R0_R2].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (eps * 2) with (eps + eps) by ring.
  apply Rplus_lt_compat ; apply Rabs_lt_between'.
  case: (Hls (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
  case: (H0 N) => {H0} m [Hm H0].
  apply Rlt_trans with (fn m x - eps/2).
  replace (ls - eps)
    with ((ls - eps / 2) - eps/2)
    by field.
  by apply Rplus_lt_compat_r.
  replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
  replace (fn m x - eps / 2) with ((fn m x - fn n x) + (fn n x - eps/2)) by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  apply Rlt_trans with (fn (n+N0)%nat x + eps/2).
  replace (fn n x) with (fn (n + N0)%nat x + (fn n x - fn (n+N0)%nat x)) by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  replace (ls + eps) with ((ls + eps/2) + eps/2) by field.
  apply Rplus_lt_compat_r.
  apply H1 ; by intuition.
  case: (Hli (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
  apply Rlt_trans with (fn (n+N0)%nat x - eps/2).
  replace (li - eps) with ((li - eps/2) - eps/2) by field.
  apply Rplus_lt_compat_r.
  apply H1 ; by intuition.
  replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
  replace (fn (n + N0)%nat x - eps / 2)
    with ((fn (n + N0)%nat x - fn n x) + (fn n x - eps/2))
    by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  case: (H0 N) => {H0} m [Hm H0].
  apply Rlt_trans with (fn m x + eps/2).
  replace (fn n x) with (fn m x + (fn n x - fn m x)) by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  replace (li + eps)
    with ((li + eps / 2) + eps/2)
    by field.
  by apply Rplus_lt_compat_r.
  case: (Hli (fn n x + eps / 2)) => {Hls Hli} N0 H0.
  move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn (N + N0)%nat x)
    with (fn n x + (fn (N + N0)%nat x - fn n x))
    by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  case: (Hli (fn n x - eps / 2) N) => {Hls Hli} m [Hm H0].
  contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn m x) with (eps/2 + (fn m x - eps/2)) by ring.
  replace (fn n x - eps / 2)
    with ((fn n x - fn m x) + (fn m x - eps/2)) by ring.
  apply Rplus_lt_compat_r, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  case: (Hls (fn n x + eps / 2) N) => {Hls} m [Hm H0].
  contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn m x) with (fn n x + (fn m x - fn n x)) by ring.
  apply Rplus_lt_compat_l, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  case: (Hls (fn n x - eps / 2)) => {Hls} N0 H0.
  move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn (N + N0)%nat x)
    with (eps/2 + (fn (N + N0)%nat x - eps/2))
    by ring.
  replace (fn n x - eps / 2)
    with ((fn n x - fn (N+N0)%nat x) + (fn (N+N0)%nat x - eps/2)) by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
Qed.

Lemma CVU_dom_include (fn : nat -> R -> R) (D1 D2 : R -> Prop) :
  (forall y, D2 y -> D1 y) -> CVU_dom fn D1 -> CVU_dom fn D2.
Proof.
  move => H H1 eps.
  case: (H1 eps) => {H1} N H1.
  exists N => n Hn x Hx.
  apply H1.
  exact Hn.
  by apply H.
Qed.

(** ** Limits, integrals and differentiability *)

Definition is_connected (D : R -> Prop) :=
  forall a b x, D a -> D b -> a <= x <= b -> D x.

Lemma CVU_limits_open (fn : nat -> R -> R) (D : R -> Prop) :
  open D
  -> CVU_dom fn D
  -> (forall x n, D x -> ex_finite_lim (fn n) x)
  -> forall x, D x -> ex_finite_lim_seq (fun n => real (Lim (fn n) x))
    /\ ex_finite_lim (fun y => real (Lim_seq (fun n => fn n y))) x
    /\ real (Lim_seq (fun n => real (Lim (fn n) x)))
      = real (Lim (fun y => real (Lim_seq (fun n => fn n y))) x).
Proof.
  move => Ho' Hfn Hex x Hx.
  assert (Ho : forall x, D x -> locally x D).
    now apply filter_open.
  clear Ho'.
  have H : ex_finite_lim_seq (fun n : nat => real (Lim (fn n) x)).
    apply CVU_dom_cauchy in Hfn.
    apply ex_lim_seq_cauchy_corr => eps.
    case: (Hfn (pos_div_2 eps)) => {Hfn} /= N Hfn.
    exists N => n m Hn Hm.
    case: (Hex x n Hx) => ln Hex_n ;
    rewrite (is_lim_unique _ _ _ Hex_n).
    case: (Hex x m Hx) => {Hex} lm Hex_m ;
    rewrite (is_lim_unique _ _ _ Hex_m).
    apply is_lim_spec in Hex_n.
    apply is_lim_spec in Hex_m.
    case: (Hex_n (pos_div_2 (pos_div_2 eps))) => {Hex_n} /= dn Hex_n.
    case: (Hex_m (pos_div_2 (pos_div_2 eps))) => {Hex_m} /= dm Hex_m.
    case: (Ho x Hx) => {Ho} d0 Ho.
    set y := x + Rmin (Rmin dn dm) d0 / 2.
    have Hd : 0 < Rmin (Rmin dn dm) d0 / 2.
      apply Rdiv_lt_0_compat.
      apply Rmin_case ; [ | by apply d0].
      apply Rmin_case ; [ by apply dn | by apply dm].
      exact: Rlt_R0_R2.
    have Hy : Rabs (y - x) < d0.
      rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
      rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
      apply Rle_lt_trans with (d0/2).
      apply Rmult_le_compat_r.
      by intuition.
      exact: Rmin_r.
      rewrite -(Rplus_0_l (d0/2)) {2}(double_var d0).
      by apply Rplus_lt_compat_r, is_pos_div_2.
    move : (Ho y Hy) => {Ho Hy} Hy.
    replace (ln - lm)
      with (- (fn n y - ln) + (fn m y - lm) + (fn n y - fn m y))
      by ring.
    rewrite (double_var eps) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    rewrite (double_var (eps/2)) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    rewrite Rabs_Ropp ; apply Hex_n.
    rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
    apply Rle_lt_trans with (Rmin dn dm / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_l.
    apply Rle_lt_trans with (dn / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_l.
    rewrite -(Rplus_0_l (dn/2)) {2}(double_var dn).
    by apply Rplus_lt_compat_r, is_pos_div_2.
    apply Rgt_not_eq, Rlt_gt, Rminus_lt_0.
    rewrite /y ; by ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    apply Hex_m.
    rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
    apply Rle_lt_trans with (Rmin dn dm / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_l.
    apply Rle_lt_trans with (dm / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_r.
    rewrite -(Rplus_0_l (dm/2)) {2}(double_var dm).
    by apply Rplus_lt_compat_r, is_pos_div_2.
    apply Rgt_not_eq, Rlt_gt, Rminus_lt_0.
    rewrite /y ; by ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    by apply Hfn.
  split.
  exact: H.
  apply Lim_seq_correct' in H.
  move: (real (Lim_seq (fun n : nat => real (Lim (fn n) x)))) H => l H.
  have H0 : is_lim (fun y : R => real (Lim_seq (fun n : nat => fn n y))) x l.
    apply is_lim_spec.
    move => eps.
    apply is_lim_seq_spec in H.
    case: (Hfn (pos_div_2 (pos_div_2 eps))) => {Hfn} /= n1 Hfn.
    case: (H (pos_div_2 (pos_div_2 eps))) => {H} /= n2 H.
    set n := (n1 + n2)%nat.
    move: (fun y Hy => Hfn n (le_plus_l _ _) y Hy) => {Hfn} Hfn.
    move: (H n (le_plus_r _ _)) => {H} H.
    move: (Hex x n Hx) => {Hex} Hex.
    apply Lim_correct' in Hex.
    apply is_lim_spec in Hex.
    case: (Hex (pos_div_2 eps)) => {Hex} /= d1 Hex.
    case: (Ho x Hx) => {Ho} /= d0 Ho.
    have Hd : 0 < Rmin d0 d1.
      apply Rmin_case ; [by apply d0 | by apply d1].
    exists (mkposreal _ Hd) => /= y Hy Hxy.
    replace (real (Lim_seq (fun n0 : nat => fn n0 y)) - l)
      with ((real (Lim (fn n) x) - l)
            - (fn n y - real (Lim_seq (fun n : nat => fn n y)))
            + (fn n y - real (Lim (fn n) x)))
      by ring.
    rewrite (double_var eps) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    rewrite (double_var (eps/2)) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    exact: H.
    rewrite Rabs_Ropp ; apply Hfn.
    by apply Ho, Rlt_le_trans with (1 := Hy), Rmin_l.
    apply Hex.
    by apply Rlt_le_trans with (1 := Hy), Rmin_r.
    exact: Hxy.
  split.
  by exists l.
  replace l with (real l) by auto.
  by apply sym_eq, (f_equal real), is_lim_unique.
Qed.
Lemma CVU_cont_open (fn : nat -> R -> R) (D : R -> Prop) :
  open D ->
  CVU_dom fn D ->
  (forall n, forall x, D x -> continuity_pt (fn n) x)
    -> forall x, D x -> continuity_pt (fun y => real (Lim_seq (fun n => fn n y))) x.
Proof.
  move => Ho Hfn Hc x Hx.
  case: (fun H => CVU_limits_open fn D Ho Hfn H x Hx)
    => [{x Hx} x n Hx | Hex_s [Hex_f Heq]].
  exists (fn n x).
  apply is_lim_spec.
  intros eps.
  case: (Hc n x Hx eps (cond_pos eps)) => {Hc} d [Hd Hc].
  exists (mkposreal d Hd) => /= y Hy Hxy.
  apply (Hc y).
  split.
  split.
  exact: I.
  by apply sym_not_eq, Hxy.
  exact: Hy.
  apply Lim_correct' in Hex_f.
  rewrite -Heq in Hex_f => {Heq}.
  replace (Lim_seq (fun n : nat => real (Lim (fn n) x)))
    with (Lim_seq (fun n : nat => (fn n) x)) in Hex_f.
  move => e He.
  apply is_lim_spec in Hex_f.
  case: (Hex_f (mkposreal e He)) => {Hex_f} /= delta Hex_f.
  exists delta ; split => [ | y [[_ Hxy] Hy]].
  by apply delta.
  apply Hex_f.
  exact: Hy.
  by apply sym_not_eq.
  apply Lim_seq_ext => n.
  replace (fn n x) with (real (fn n x)) by auto.
  apply sym_eq, f_equal, is_lim_unique.
  apply is_lim_spec.
  move => eps.
  case: (Hc n x Hx eps (cond_pos eps)) => {Hc} d [Hd Hc].
  exists (mkposreal d Hd) => /= y Hy Hxy.
  apply (Hc y).
  split.
  split.
  exact: I.
  by apply sym_not_eq, Hxy.
  exact: Hy.
Qed.
(*Lemma CVU_Nint (fn Fn : nat -> R -> R) (F : R -> R) (a b : R) (Hab : a < b) :
  CVU_dom fn (fun x => a <= x <= b)
  -> (forall n, forall x, a <= x <= b -> continuity_pt (fn n) x)
  -> (forall n x, a <= x <= b -> is_derive (Fn n) x (fn n x)) -> (forall n, Fn n a = 0)
  -> (forall x, a <= x <= b -> is_derive F x (Lim_seq (fun n => fn n x))) -> (F a = 0)
  -> CVU_dom Fn (fun x => a <= x <= b)
    /\ (forall x, a <= x <= b -> Lim_seq (fun n => Fn n x) = F x).

Lemma CVU_Rint (fn : nat -> R -> R) (a b : R) (Hab : a < b) :
  CVU_dom fn (fun x => a <= x <= b)
  -> (forall n, forall x, a <= x <= b -> continuity_pt (fn n) x)
  -> CVU_dom (fun n x => RInt (fn n) a x) (fun x => a <= x <= b)
    /\ (forall x, a <= x <= b ->
  Lim_seq (fun n => RInt (fn n) a x) = RInt (fun y => Lim_seq (fun n => fn n y)) a x).
*)
Lemma CVU_Derive (fn : nat -> R -> R) (D : R -> Prop) :
  open D -> is_connected D
  -> CVU_dom fn D
  -> (forall n x, D x -> ex_derive (fn n) x)
  -> (forall n x, D x -> continuity_pt (Derive (fn n)) x)
  -> CVU_dom (fun n x => Derive (fn n) x) D
  -> (forall x , D x ->
       (is_derive (fun y => real (Lim_seq (fun n => fn n y))) x
         (real (Lim_seq (fun n => Derive (fn n) x))))).
Proof.
  move => Ho Hc Hfn Edn Cdn Hdn.

  set rn := fun x n h => match (Req_EM_T h 0) with
    | left _ => Derive (fn n) x
    | right _ => (fn n (x+h) - fn n x)/h
  end.

  assert (Ho' : forall x : R, D x -> open (fun h : R => D (x + h))).
    intros x Dx.
    apply filter_open.
    intros h Hh.
    destruct (proj1 (filter_open D) Ho _ Hh) as [d Hd].
    exists d => /= y Hy.
    apply Hd ; simpl ; unfold distR ; ring_simplify (x + y - (x + h)).
    by apply Hy.

  have Crn : forall x, D x -> forall n h, D (x+h) -> is_lim (rn x n) h (rn x n h).
    move => x Hx n h Hh.
    rewrite {2}/rn ; case: (Req_EM_T h 0) => [-> | Hh0].
    apply is_lim_spec.
    move => eps.
    suff H : @locally _ R_metric 0 (fun y : R => y <> 0 ->
      Rabs ((fn n (x + y) - fn n x) / y - Derive (fn n) x) < eps).
    case: H => d H.
    exists d => y Hy Hxy.
    rewrite /rn ; case: Req_EM_T => // _ ; by apply H.
    move: (Edn n x Hx) => {Edn} Edn.
    apply Derive_correct in Edn.
    case: (Edn eps (cond_pos eps)) => {Edn} delta Edn.
    exists delta => y Hy Hxy.
    rewrite /= /distR Rminus_0_r in Hy.
    by apply Edn.

    have H : continuity_pt (fun h => ((fn n (x + h) - fn n x) / h)) h.
      apply derivable_continuous_pt.
      apply derivable_pt_div.
      apply derivable_pt_minus.
      apply derivable_pt_comp.
      apply (derivable_pt_plus (fun _ => x) (fun h => h) h).
      exact: derivable_pt_const.
      exact: derivable_pt_id.
      exists (Derive (fn n) (x + h)) ; by apply Derive_correct, Edn.
      exact: derivable_pt_const.
      exact: derivable_pt_id.
      exact: Hh0.

    apply is_lim_spec.
    move => eps.
    case: (H eps (cond_pos eps)) => {H} d [Hd H].
    have Hd0 : 0 < Rmin d (Rabs h).
      apply Rmin_case.
      exact: Hd.
      by apply Rabs_pos_lt.
    exists (mkposreal _ Hd0) => /= y Hy Hhy.
    rewrite /rn ; case: Req_EM_T => /= Hy'.
    contradict Hy.
    apply Rle_not_lt ; rewrite Hy' Rminus_0_l Rabs_Ropp ; by apply Rmin_r.
    apply (H y) ; split.
    split.
    exact: I.
    by apply sym_not_eq.
    by apply Rlt_le_trans with (1 := Hy), Rmin_l.


  have Hrn : forall x, D x -> CVU_dom (rn x) (fun h : R => D (x + h)).
    move => x Hx.
    apply CVU_dom_cauchy => eps.
    apply CVU_dom_cauchy in Hdn.
    case: (Hdn eps) => {Hdn} /= N Hdn.
    exists N => n m h Hh Hn Hm.
    rewrite /rn ; case: Req_EM_T => Hh0.
    exact: (Hdn n m x Hx Hn Hm).
    replace ((fn n (x + h) - fn n x) / h - (fn m (x + h) - fn m x) / h)
      with (((fn n (x + h) - fn m (x + h)) - (fn n x - fn m x))/h)
      by (field ; auto).
    case: (MVT_gen (fun x => (fn n x - fn m x)) x (x+h)) => [y Hy | y Hy | z [Hz ->]].
    apply ex_derive_minus ; apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    split ; apply Rlt_le ; by apply Hy.
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    split ; apply Rlt_le ; by apply Hy.
    apply derivable_continuous_pt, derivable_pt_minus.
    exists (Derive (fn n) y) ; apply Derive_correct, Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hy.
    exists (Derive (fn m) y) ; apply Derive_correct, Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hy.
    replace (Derive (fun x1 : R => fn n x1 - fn m x1) z * (x + h - x) / h)
      with (Derive (fun x1 : R => fn n x1 - fn m x1) z)
      by (field ; auto).
    rewrite Derive_minus.
    apply (Hdn n m z).
    apply (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hz.
    exact: Hn.
    exact: Hm.
    apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hz.
    apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hz.

  have Lrn : forall x, D x -> (forall (y : R) (n : nat),
    (fun h : R => D (x + h)) y -> ex_finite_lim (rn x n) y).
    intros ; exists (rn x n y) ; by intuition.

  move => x Hx.

  case: (CVU_limits_open (rn x) _ (Ho' x Hx) (Hrn x Hx) (Lrn x Hx) 0) => [ | H [H0 H1]].
  by rewrite Rplus_0_r.

  have : ex_derive (fun y : R => real (Lim_seq (fun n : nat => fn n y))) x
    /\ Derive (fun y : R => real (Lim_seq (fun n : nat => fn n y))) x
      = real (Lim_seq (fun n : nat => Derive (fn n) x)).

  split.
  case: H0 => df H0.
  exists df => e He.
  apply is_lim_spec in H0.
  case: (H0 (mkposreal e He)) => {H0} /= delta H0.
  destruct (proj1 (filter_open D) Ho x Hx) as [dx Hd].
  have H2 : 0 < Rmin delta dx.
    apply Rmin_case ; [by apply delta | by apply dx].
  exists (mkposreal _ H2) => /= h Hh0 Hh.
  replace (real (Lim_seq (fun n : nat => fn n (x + h))) -
    real (Lim_seq (fun n : nat => fn n x))) with
    (real (Rbar_minus (Lim_seq (fun n : nat => fn n (x + h))) (Lim_seq (fun n : nat => fn n x)))).
  rewrite -Lim_seq_minus.
  replace (real (Lim_seq (fun n : nat => fn n (x + h) - fn n x)) / h)
  with (real (Rbar_mult (/h) (Lim_seq (fun n : nat => fn n (x + h) - fn n x)))).
  rewrite -Lim_seq_scal_l.
  replace (Lim_seq (fun n : nat => / h * (fn n (x + h) - fn n x)))
    with (Lim_seq (fun n : nat => rn x n h)).
  apply H0.
  rewrite Rminus_0_r ; apply Rlt_le_trans with (1 := Hh), Rmin_l.
  exact: Hh0.
  apply Lim_seq_ext => n.
  rewrite /rn /Rdiv ; case: Req_EM_T => // _ ; exact: Rmult_comm.
  case: (Lim_seq (fun n : nat => fn n (x + h) - fn n x))
    => [l | | ] //=.
    by field.
    rewrite /Rdiv Rmult_0_l.
    case: Rle_dec => // Hh1.
    case: Rle_lt_or_eq_dec => //.
    rewrite /Rdiv Rmult_0_l.
    case: Rle_dec => // Hh1.
    case: Rle_lt_or_eq_dec => //.

  apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
  exact: Hfn.
  apply Hd.
  simpl.
  unfold distR.
  ring_simplify (x + h - x) ; apply Rlt_le_trans with (1 := Hh), Rmin_r.
  apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
  exact: Hfn.
  apply Hd.
  rewrite distance_refl.
  apply cond_pos.
  apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
  move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
  move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
  rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
  rewrite (is_lim_seq_unique  (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
  easy.
  apply F0.
  rewrite distance_refl.
  apply cond_pos.
  apply F.
  simpl.
  unfold distR.
  ring_simplify (x + h - x).
  apply Rlt_le_trans with (1 := Hh), Rmin_r.
  apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
  move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
  move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
  rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
  rewrite (is_lim_seq_unique  (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
  by [].
  apply F0.
  rewrite distance_refl.
  apply cond_pos.
  apply F.
  simpl.
  unfold distR.
  ring_simplify (x + h - x).
  apply Rlt_le_trans with (1 := Hh), Rmin_r.

  rewrite /Derive.
  replace (Lim_seq (fun n : nat => real (Lim (fun h : R => (fn n (x + h) - fn n x) / h) 0)))
    with (Lim_seq (fun n : nat => real (Lim (rn x n) 0))).
  rewrite H1.
  case: H0 => drn H0.
  rewrite (is_lim_unique _ _ _ H0).
  apply f_equal, is_lim_unique.
  apply is_lim_spec.
  intros eps.
  apply is_lim_spec in H0.
  case: (H0 eps) => {H0} delta H0.
  destruct (proj1 (filter_open D) Ho x Hx) as [dx Hd].
  have H2 : 0 < Rmin delta dx.
    apply Rmin_case ; [by apply delta | by apply dx].
  exists (mkposreal _ H2) => /= h Hh0 Hh.
  replace (real (Lim_seq (fun n : nat => fn n (x + h))) -
    real (Lim_seq (fun n : nat => fn n x))) with
    (real (Rbar_minus (Lim_seq (fun n : nat => fn n (x + h))) (Lim_seq (fun n : nat => fn n x)))).
  rewrite -Lim_seq_minus.
  replace (real (Lim_seq (fun n : nat => fn n (x + h) - fn n x)) / h)
  with (real (Rbar_mult (/h) (Lim_seq (fun n : nat => fn n (x + h) - fn n x)))).
  rewrite -Lim_seq_scal_l.
  replace (Lim_seq (fun n : nat => / h * (fn n (x + h) - fn n x)))
    with (Lim_seq (fun n : nat => rn x n h)).
  apply H0.
  apply Rlt_le_trans with (1 := Hh0), Rmin_l.
  exact: Hh.
  apply Lim_seq_ext => n.
  rewrite /rn /Rdiv ; case: Req_EM_T => // _ ; exact: Rmult_comm.
  case: (Lim_seq (fun n : nat => fn n (x + h) - fn n x))
    => [l | | ] //=.
    by field.
    rewrite /Rdiv Rmult_0_l.
    case: Rle_dec => // Hh1.
    case: Rle_lt_or_eq_dec => //.
    rewrite /Rdiv Rmult_0_l.
    case: Rle_dec => // Hh1.
    case: Rle_lt_or_eq_dec => //.

  apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
  exact: Hfn.
  apply Hd.
  simpl.
  unfold distR.
  ring_simplify (x + h - x) ; rewrite -(Rminus_0_r h) ;
  apply Rlt_le_trans with (1 := Hh0), Rmin_r.
  apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
  exact: Hfn.
  apply Hd.
  rewrite distance_refl.
  apply cond_pos.
  apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
  move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
  move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
  rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
  rewrite (is_lim_seq_unique  (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
  easy.
  apply F0.
  rewrite distance_refl.
  apply cond_pos.
  apply F.
  simpl.
  unfold distR.
  ring_simplify (x + h - x).
  rewrite Rminus_0_r in Hh0.
  apply Rlt_le_trans with (1 := Hh0), Rmin_r.
  apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
  move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
  move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
  rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
  rewrite (is_lim_seq_unique  (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
  by [].
  apply F0.
  rewrite distance_refl.
  apply cond_pos.
  apply F.
  simpl.
  unfold distR.
  ring_simplify (x + h - x).
  rewrite Rminus_0_r in Hh0.
  apply Rlt_le_trans with (1 := Hh0), Rmin_r.

  apply Lim_seq_ext => n.
  apply sym_eq, f_equal, is_lim_unique.
  have Hx' : D (x + 0).
    by rewrite Rplus_0_r.
  rewrite (is_lim_unique _ _ _ (Crn x Hx n 0 Hx')).
  apply is_lim_spec.
  move: (Crn x Hx n 0 Hx') => H2 eps.
  apply is_lim_spec in H2.
  case: (H2 eps) => {H2} delta H2.
  exists delta => y Hy Hy0.
  move: (H2 y Hy Hy0).
  rewrite {1}/rn ; by case: Req_EM_T.

  case => H2 H3.
  rewrite -H3.
  by apply Derive_correct.
Qed.

(** ** Dini's theorem *)

Lemma Dini (fn : nat -> R -> R) (a b : R) :
  a < b -> CVS_dom fn (fun x => a <= x <= b)
  -> (forall (n : nat) (x : R), a <= x <= b -> continuity_pt (fn n) x)
  -> (forall (x : R), a <= x <= b -> continuity_pt (fun y => Lim_seq (fun n => fn n y)) x)
  -> (forall (n : nat) (x y : R), a <= x -> x <= y -> y <= b -> fn n x <= fn n y)
  -> CVU_dom fn (fun x => a <= x <= b).
Proof.
  set AB := fun x => a <= x <= b.
  set f : R -> R := (fun y : R => Lim_seq (fun n : nat => fn n y)).
  move => Hab Hcvs Cfn Cf Hfn.

  have CUf : uniform_continuity f AB.
    apply Heine.
    by apply compact_P3.
    by apply Cf.
  suff H : forall eps : posreal, exists N : nat,
    forall n : nat, (N <= n)%nat -> forall x : R, AB x ->
    Rabs (fn n x - Lim_seq (fun n0 : nat => fn n0 x)) < 5 * eps.
    move => eps.
    replace (pos eps) with (5 * (eps / 5)) by field.
    suff He : 0 < eps / 5.
    by apply (H (mkposreal _ He)).
    apply Rdiv_lt_0_compat.
    by apply eps.
    repeat (apply Rplus_lt_0_compat || apply Rmult_lt_0_compat) ; apply Rlt_0_1.

  move => eps.
  case: (CUf eps) => {CUf} eta CUf.
  move: (interval_finite_subdiv_between  a b (pos_div_2 eta) (Rlt_le _ _ Hab)).
  case: (interval_finite_subdiv a b (pos_div_2 eta) (Rlt_le _ _ Hab)) =>
    a_ Ha_ /= Ha_0.
  have : exists N, forall n i, (N <= n)%nat -> (i < seq.size a_)%nat
    -> Rabs (fn n (seq.nth 0 a_ i) - f (seq.nth 0 a_ i)) < eps.
    case: a_ Ha_ Ha_0 => [ | a0 a_] Ha_ /= Ha_0.
    contradict Hab.
    rewrite -(proj1 Ha_) -(proj1 (proj2 Ha_)).
    by apply Rlt_irrefl.
    elim: (a_) (a0) Ha_0 => /= [ | x1 l IH] x0 Hl.
    move: (Hcvs x0 (Hl O (lt_n_Sn _))) ;
    move/Lim_seq_correct' => {Hcvs} Hcvs.
    apply is_lim_seq_spec in Hcvs.
    case: (Hcvs eps) => {Hcvs} N Hcvs.
    exists N => n i Hn Hi.
    case: i Hi => /= [ | i] Hi.
    by apply Hcvs.
    by apply lt_S_n, lt_n_O in Hi.
    case: (IH x1).
    move => i Hi.
    by apply (Hl (S i)), lt_n_S.
    move => N0 HN0.
    move: (Hcvs x0 (Hl O (lt_O_Sn _))) ;
    move/Lim_seq_correct' => {Hcvs} Hcvs.
    apply is_lim_seq_spec in Hcvs.
    case: (Hcvs eps) => {Hcvs} N Hcvs.
    exists (N + N0)%nat => n i Hn Hi.
    case: i Hi => /= [ | i ] Hi.
    apply Hcvs ; by intuition.
    apply HN0 ; by intuition.
  case => N HN.
  exists N => n Hn x Hx.
  have : exists i, (S i < seq.size a_)%nat /\ seq.nth 0 a_ i <= x <= seq.nth 0 a_ (S i).
    case: a_ Ha_ Ha_0 {HN} => [ | a0 a_] Ha_ /= Ha_0.
    contradict Hab.
    rewrite -(proj1 Ha_) -(proj1 (proj2 Ha_)).
    by apply Rlt_irrefl.
    case: a_ Ha_ Ha_0 => [ | a1 a_] Ha_ /= Ha_0.
    contradict Hab.
    rewrite -(proj1 Ha_) -(proj1 (proj2 Ha_)).
    by apply Rlt_irrefl.
    rewrite -(proj1 Ha_) in AB Hcvs CUf Hx Hab Cfn Cf Hfn Ha_0 |- * ; case: Ha_ => {a} _ Ha_.
    rewrite -(proj1 Ha_) in AB Hcvs CUf Hx Hab Cfn Cf Hfn Ha_0 |- * ; case: Ha_ => {b} _ Ha_.
    clear Hcvs CUf ;
    revert AB Hx ;
    elim: (a_) (a0) (a1) => /= [ | x2 l IH] x0 x1 Hx.
    exists O ; split => /=.
    by apply lt_n_Sn.
    by apply Hx.
    case: (Rlt_le_dec x x1) => Hx'.
    exists O ; split => /=.
    by apply lt_n_S, lt_O_Sn.
    split ; intuition.
    case: (IH x1 x2).
    by intuition.
    move => i [Hi Hx0].
    exists (S i) ; by intuition.
  case => i [Hi Hx'].
  replace (fn n x - Lim_seq (fun n0 : nat => fn n0 x))
    with ((f (seq.nth 0 a_ i) - f x) + (fn n x - f (seq.nth 0 a_ i)))
    by (rewrite /f ; ring).
  replace (5 * eps) with (eps + 4 * eps) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_compat.
  apply CUf.
  apply Ha_0 ; by intuition.
  by apply Hx.
  rewrite -Rabs_Ropp Ropp_minus_distr' Rabs_pos_eq.
  apply Rle_lt_trans with (seq.nth 0 a_ (S i) - seq.nth 0 a_ i).
  apply Rplus_le_compat_r.
  by apply Hx'.
  apply Rle_lt_trans with (eta/2).
  apply Rle_minus_l.
  rewrite Rplus_comm.
  by apply Ha_.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  apply Rle_minus_r ; rewrite Rplus_0_l.
  by apply Hx'.
  replace (fn n x - f (seq.nth 0 a_ i))
    with ((fn n (seq.nth 0 a_ i) - f (seq.nth 0 a_ i)) + (fn n x - fn n (seq.nth 0 a_ i)))
    by ring.
  replace (4 * eps) with (eps + 3 * eps) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_compat.
  apply HN ; by intuition.
  rewrite Rabs_pos_eq.
  apply Rle_lt_trans with (fn n (seq.nth 0 a_ (S i)) - fn n (seq.nth 0 a_ i)).
  apply Rplus_le_compat_r.
  apply Hfn.
  by apply Hx.
  by apply Hx'.
  by apply Ha_0.
  replace (fn n (seq.nth 0 a_ (S i)) - fn n (seq.nth 0 a_ i))
    with ((fn n (seq.nth 0 a_ (S i)) - f (seq.nth 0 a_ (S i)))
      - (fn n (seq.nth 0 a_ i) - f (seq.nth 0 a_ i))
      + (f (seq.nth 0 a_ (S i)) - f (seq.nth 0 a_ i)))
    by ring.
  replace (3 * eps) with ((eps + eps) + eps) by ring.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_compat.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_compat.
  apply HN ; by intuition.
  rewrite Rabs_Ropp.
  apply HN ; by intuition.
  apply CUf.
  apply Ha_0 ; by intuition.
  apply Ha_0 ; by intuition.
  rewrite Rabs_pos_eq.
  apply Rle_lt_trans with (eta/2).
  apply Rle_minus_l.
  rewrite Rplus_comm.
  by apply Ha_.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  apply Rle_minus_r ; rewrite Rplus_0_l.
  apply Rle_trans with x ; apply Hx'.
  apply Rle_minus_r ; rewrite Rplus_0_l.
  apply Hfn.
  apply Ha_0 ; by intuition.
  by apply Hx'.
  by apply Hx.
Qed.

(** ** Series of functions *)

Lemma CVN_CVU_r (fn : nat -> R -> R) (r : posreal) :
  CVN_r fn r -> forall x, (Rabs x < r) -> exists e : posreal,
    CVU (fun n => SP fn n) (fun x => Series (fun n => fn n x)) x e.
Proof.
  case => An [l [H H0]] x Hx.
  have H1 : ex_series An.
    apply ex_series_equiv_1.
    exists l => e He.
    case: (H e He) => {H} N H.
    exists N => n Hn.
    replace (sum_f_R0 An n) with (sum_f_R0 (fun k : nat => Rabs (An k)) n).
    by apply H.
    elim: n {Hn} => /= [ | n IH].
    apply Rabs_pos_eq.
    apply Rle_trans with (Rabs (fn O 0)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
    rewrite IH Rabs_pos_eq.
    by [].
    apply Rle_trans with (Rabs (fn (S n) 0)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.

  have H2 : is_lim_seq (fun n => Series (fun k => An (n + k)%nat)) 0.
    apply is_lim_seq_incr_1.
    apply is_lim_seq_ext with (fun n => Series An - sum_f_R0 An n).
    move => n ; rewrite (Series_decal_n An (S n)) /=.
    ring.
    by apply lt_O_Sn.
    by apply H1.
    replace (Finite 0) with (Rbar_plus (Series An) (- Series An))
      by (simpl ; apply Rbar_finite_eq ; ring).
    apply (is_lim_seq_plus _ _ (Series An) (-Series An)).
    by apply is_lim_seq_const.
    replace (Finite (-Series An)) with (Rbar_opp (Series An))
      by (simpl ; apply Rbar_finite_eq ; ring).
    apply -> is_lim_seq_opp.
    rewrite /Series ;
    apply (is_lim_seq_ext (sum_f_R0 (fun k => An k))).
    elim => /= [ | n IH].
    by [].
    by rewrite IH.
    apply Lim_seq_correct', H1.
    easy.

  have H3 : forall y, Boule 0 r y -> ex_series (fun n => Rabs (fn n y)).
  move => y Hy.
  move: H1 ; apply Comp_ex_series.
  move => n ; split.
  by apply Rabs_pos.
  by apply H0.

  apply Rminus_lt_0 in Hx.
  set r0 := mkposreal _ Hx.
  exists r0 => e He ; set eps := mkposreal e He.
  apply is_lim_seq_spec in H2.
  case: (H2 eps) => {H2} N H2.
  exists N => n y Hn Hy.

  have H4 : Boule 0 r y.
  rewrite /Boule /= in Hy |- *.
  apply Rle_lt_trans with (1 := Rabs_triang_inv _ _) in Hy.
  rewrite /Rminus ?(Rplus_comm _ (-Rabs x)) in Hy.
  apply Rplus_lt_reg_l in Hy.
  by rewrite Rminus_0_r.

  apply Rle_lt_trans with (2 := H2 (S n) (le_trans _ _ _ (le_n_Sn _) (le_n_S _ _ Hn))).
  rewrite Rminus_0_r /SP.
  rewrite (Series_decal_n (fun k : nat => fn k y) (S n)) /=.
  ring_simplify (sum_f_R0 (fun k : nat => fn k y) n +
    Series (fun k : nat => fn (S (n + k)) y) -
    sum_f_R0 (fun k : nat => fn k y) n).

  apply Rle_trans with (2 := Rle_abs _).
  apply Rle_trans with (Series (fun k : nat => Rabs (fn (S (n + k)) y))).
  apply Series_Rabs.
  apply ex_series_ext with (fun n0 : nat => Rabs (fn (S (n) + n0)%nat y)).
    move => n0 ; by rewrite plus_Sn_m.
  apply (ex_series_decal_n (fun n => Rabs (fn n y))).
  by apply H3.
  apply Series_compar.
  move => k ; split.
  by apply Rabs_pos.
  by apply H0.
  apply ex_series_ext with (fun k : nat => An (S n + k)%nat).
  move => k ; by rewrite plus_Sn_m.
  by apply ex_series_decal_n.
  by apply lt_O_Sn.
  apply ex_series_Rabs.
  by apply H3.
Qed.

(** * Swich limits *)

Require Import Lub Hierarchy.

Lemma is_Lub_Rbar_ne_unique (E : R -> Prop) (pr : exists x : R, E x) (l : Rbar) :
  is_lub_Rbar E l -> Lub_Rbar_ne E pr = l.
Admitted.

Global Instance NormedAbelianGroup_MetricSpace {G : Type} :
  NormedAbelianGroup G -> MetricSpace G.
Proof.
  case ; intros.
  exists (fun x y => norm (plus x (opp y))).
  - move => a.
    by rewrite plus_opp_r norm_zero.
  - move => a b.
    by rewrite -norm_opp opp_plus opp_opp plus_comm.
  - move => a b c.
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le.
    by rewrite plus_assoc -(plus_assoc a) plus_opp_l plus_zero_r.
Defined.

Axiom ext_fct_ax : forall T U (f g : T -> U), (forall (x : T), f x = g x) -> f = g.

Global Instance AbelianGroup_Fct {T G} :
  AbelianGroup G -> AbelianGroup (T -> G).
Proof.
  case ; intros.
Check Build_AbelianGroup.
  apply (Build_AbelianGroup _ (fun f g => (fun x => plus (f x) (g x)))
         (fun f => (fun x => opp (f x)))
         (fun _ => zero)).
  - move => f g.
    apply ext_fct_ax => x.
    by apply plus_comm.
  - move => f g h.
    apply ext_fct_ax => x.
    by apply plus_assoc.
  - move => f.
    apply ext_fct_ax => x.
    by apply plus_zero_r.
  - move => f.
    apply ext_fct_ax => x.
    by apply plus_opp_r.
Defined.

Lemma UnifFct_norm_ne {T} {G} {TT : TopologicalSpace T} {NAG : NormedAbelianGroup G}
  (f : T -> G) : exists s : R, s = 0 \/ exists x : T, s = norm (f x).
Proof.
  exists 0 ; by left.
Qed.

Definition UnifFct_norm {T} {G} {TT : TopologicalSpace T} {NAG : NormedAbelianGroup G}
  (f : T -> G) : R :=
    Rbar_min 1 (Lub_Rbar_ne _ (UnifFct_norm_ne f)).

Lemma UnifFct_0_le_lub  {T} {G} {TT : TopologicalSpace T} {NAG : NormedAbelianGroup G}
  (f : T -> G) : Rbar_le 0 (Lub_Rbar_ne _ (UnifFct_norm_ne f)).
Proof.
  rewrite /Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] //= [ub lub].
  apply ub ; by left.
  by left.
  apply ub ; by left.
Qed.

Lemma UnifFct_norm_le_lub  {T} {G} {TT : TopologicalSpace T} {NAG : NormedAbelianGroup G}
  (f : T -> G) : Rbar_le (UnifFct_norm f) (Lub_Rbar_ne _ (UnifFct_norm_ne f)).
Proof.
  rewrite /UnifFct_norm /Rbar_min ; case: Rbar_le_dec => //=.
  move/Rbar_not_le_lt.
  rewrite /Lub_Rbar_ne ; case ex_lub_Rbar_ne ; case => [l | | ] //= [ub lub] H.
  by right.
  apply ub ; by left.
Qed.

Lemma UnifFct_norm_zero {T} {G} {TT : TopologicalSpace T} {NAG : NormedAbelianGroup G} :
  UnifFct_norm zero = 0.
Proof.
  replace 0 with (real (Finite 0)) by auto.
  apply (f_equal real).
  replace (Lub_Rbar_ne _ _) with (Finite 0).
  rewrite /Rbar_min ; case: Rbar_le_dec => //= H.
  contradict H ; apply Rbar_lt_not_le.
  by apply Rlt_0_1.
  apply sym_eq, is_Lub_Rbar_ne_unique ; split.
  - move => s /= Hs.
    case: Hs => Hs.
    rewrite -Hs ; by right.
    case: Hs => x -> {s}.
    replace ((@zero (T -> G) (AbelianGroup_Fct nagroup_abelian)) x) with (@zero G nagroup_abelian).
    rewrite norm_zero ; by right.
    by case: (@nagroup_abelian G NAG) => /=.
  - move => b Hb.
    apply Hb.
    by left.
Qed.

Lemma UnifFct_norm_opp  {T} {G} {TT : TopologicalSpace T} {NAG : NormedAbelianGroup G}
  (f : T -> G) :
    UnifFct_norm (opp f) = UnifFct_norm f.
Proof.
  apply (f_equal (fun x => real (Rbar_min 1 x))).
  apply Lub_Rbar_ne_eqset => s ; split ; case => Hs ; try by left.
  case: Hs => x -> {s} ; right ; exists x.
  replace ((@opp (T -> G) (AbelianGroup_Fct nagroup_abelian)) f x) with (@opp G nagroup_abelian (f x)).
  by apply norm_opp.
  by case: (@nagroup_abelian G NAG) => /=.
  case: Hs => x -> {s} ; right ; exists x ;
  replace ((@opp (T -> G) (AbelianGroup_Fct nagroup_abelian)) f x) with (@opp G nagroup_abelian (f x)).
  by apply sym_equal, norm_opp.
  by case: (@nagroup_abelian G NAG) => /=.
Qed.

Lemma UnifFct_norm_triangle  {T} {G} {TT : TopologicalSpace T} {MM : NormedAbelianGroup G} :
  forall f g : T -> G,
  UnifFct_norm (plus f g) <= UnifFct_norm f + UnifFct_norm g.
Proof.
  move => f g.
  - rewrite {2}/UnifFct_norm /Rbar_min ; case: Rbar_le_dec ;
    rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => /= lf Hf Hlf.
    apply Rle_trans with 1.
    rewrite /UnifFct_norm /Rbar_min ; case: Rbar_le_dec => H.
    by apply Rle_refl.
    apply Rbar_not_le_lt in H.
    apply Rlt_le.
    move: H ; case: (Lub_Rbar_ne _ _) => //= _.
    by apply Rlt_0_1.
    apply Rminus_le_0 ; ring_simplify.
    rewrite /UnifFct_norm /Rbar_min ; case: Rbar_le_dec => H.
    by apply Rle_0_1.
    rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; case => [lg | | ] //= Hlg.
    apply Rbar_finite_le, Hlg.
    by left.
    by apply Rle_refl.
    by apply Rle_refl.
    apply Rbar_not_le_lt in Hlf.
    have Hlf0 : Rbar_le 0 lf.
      apply Hf ; by left.
    have : is_finite lf.
      case: (lf) Hlf Hlf0 => [r | | ] //= H H0.
      by case: H0.
    case: lf Hf Hlf Hlf0 => [lf | | ] //= Hf Hlf Hlf0 _.
    apply Rbar_finite_le in Hlf0.
  - rewrite {2}/UnifFct_norm /Rbar_min ; case: Rbar_le_dec ;
    rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => /= lg Hg Hlg.
    apply Rle_trans with 1.
    rewrite /UnifFct_norm /Rbar_min ; case: Rbar_le_dec => H.
    by apply Rle_refl.
    apply Rbar_not_le_lt in H.
    apply Rlt_le.
    move: H ; case: (Lub_Rbar_ne _ _) => //= _.
    by apply Rlt_0_1.
    apply Rminus_le_0 ; ring_simplify.
    by [].
    apply Rbar_not_le_lt in Hlg.
    have Hlg0 : Rbar_le 0 lg.
      apply Hg ; by left.
    have : is_finite lg.
      case: (lg) Hlg Hlg0 => [r | | ] //= H H0.
      by case: H0.
    case: lg Hg Hlg Hlg0 => [lg | | ] //= Hg Hlg Hlg0 _.
    apply Rbar_finite_le in Hlg0.
  - rewrite /UnifFct_norm.
    + have Hlub : Rbar_le (Lub_Rbar_ne
      (fun s : R => s = 0 \/ (exists x : T, s = norm (plus f g x)))
      (@UnifFct_norm_ne T G TT MM (@plus (T -> G) (@AbelianGroup_Fct T G (@nagroup_abelian G MM)) f g))) (lf + lg).
      rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; case => [l | | ] //= H.
      apply H => s ; case => [-> | [x -> ]] {s}.
      by apply Rbar_finite_le, Rplus_le_le_0_compat.
      replace (norm (plus f g x)) with (norm (plus (f x) (g x))).
      apply Rbar_finite_le, Rle_trans with (1 := norm_triangle _ _).
      apply Rplus_le_compat ; apply Rbar_finite_le.
      apply Hf ; right ; by exists x.
      apply Hg ; right ; by exists x.
      by case: nagroup_abelian.
      apply H => s ; case => [-> | [x -> ]] {s}.
      by apply Rbar_finite_le, Rplus_le_le_0_compat.
      replace (norm (plus f g x)) with (norm (plus (f x) (g x))).
            apply Rbar_finite_le, Rle_trans with (1 := norm_triangle _ _).
      apply Rplus_le_compat ; apply Rbar_finite_le.
      apply Hf ; right ; by exists x.
      apply Hg ; right ; by exists x.
      by case: nagroup_abelian.
      by left.
    + have Hlub' : (Lub_Rbar_ne
      (fun s : R => s = 0 \/ (exists x : T, s = @norm G MM ((plus f g) x)))
      (@UnifFct_norm_ne T G TT MM (@plus (T -> G) (@AbelianGroup_Fct T G (@nagroup_abelian G MM)) f g))) <= (lf + lg).
      move: Hlub ; case: (Lub_Rbar_ne _ _) => [x | | ] //= H.
      by apply Rbar_finite_le.
      by apply Rplus_le_le_0_compat.
      by apply Rplus_le_le_0_compat.

    apply Rle_trans with (2 := Hlub').
    rewrite /Rbar_min ; case: Rbar_le_dec.
    move: Hlub Hlub' ;
    rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; case => [l | | ] //= H H0 Hl.
    by apply Rbar_finite_le.
    by case: H0.
    move => H1 ; contradict H1.
    by apply Rbar_lt_not_le.
    move => _ ; by right.
Qed.

Global Instance NAG_UnifFct {T} {G} {TT : TopologicalSpace T} :
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

Lemma filterlim_swich_1 {T1 T2 G} {TT1 : TopologicalSpace T1} {TT2 : TopologicalSpace T2} {NAG : NormedAbelianGroup G}
  (f : T1 -> T2 -> G) F1 F2 (FF1 : Filter F1) (FF2 : Filter F2) g h (l : G) :
  (filterlim f F1 (locally g))
  -> (forall x, filterlim (f x) F2 (locally (h x)))
  -> filterlim h F1 (locally l) -> filterlim g F2 (locally l).
Proof.
intros Hfg Hfh Hhl P.
apply filterlim_locally.
move => eps.
wlog: eps / (eps < 1) => [Hw | Heps].
case: (Rlt_le_dec eps 1) => Heps.
by apply Hw.
suff : F2 (fun x : T2 => @distance G (@NormedAbelianGroup_MetricSpace G NAG) l (g x) < 1/2).
  apply filter_imp => x Hx.
  apply Rlt_trans with (1 := Hx).
  apply Rlt_le_trans with (2 := Heps).
  apply Rminus_lt_0 ; field_simplify ; rewrite {1}/Rdiv (Rmult_0_l (/1)).
  by apply (is_pos_div_2 (mkposreal _ Rlt_0_1)).
  apply (Hw (pos_div_2 (mkposreal _ Rlt_0_1))).
  simpl ; apply Rminus_lt_0 ; field_simplify ; rewrite {1}/Rdiv (Rmult_0_l (/1)).
  by apply (is_pos_div_2 (mkposreal _ Rlt_0_1)).

move: (proj1 (@filterlim_locally _ _ _ F1 FF1 h l) Hhl (pos_div_2 eps)) => {Hhl} /= Hhl.
move: (proj1 (@filterlim_locally _ _ _ F1 FF1 f g) Hfg (pos_div_2 (pos_div_2 eps))) => {Hfg} /= Hfg.
move: (fun x => proj1 (@filterlim_locally _ _ _ F2 FF2 (f x) (h x)) (Hfh x) (pos_div_2 (pos_div_2 eps))) => {Hfh} /= Hfh.
have : F1 (fun x => forall y, @distance G (@NormedAbelianGroup_MetricSpace G NAG) (g y) (f x y) < eps / 2 / 2).
  move: Hfg.
  apply filter_imp => x Hx y.
Admitted.

(* Lemma filterlim_swich {T1 T2} {TT1 : TopologicalSpace T1} {TT2 : TopologicalSpace T2}
  (f : T1 -> T2 -> R) F1 F2 F23 g h :
  (filterlim f F1 F23) -> (@filter_cv _ topo_UnifFct F23 g)
  -> (forall x, filterlim (f x) F2 (locally (h x)))
  -> exists l, filterlim h F1 (locally l) /\ filterlim g F2 (locally l) .
Proof.
  intros.
  
Admitted. *)






