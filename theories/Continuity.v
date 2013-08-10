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

Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Rbar Locally.
Require Import Compactness Limit.

(** * Limit of fonctions *)

(** ** Definition *)

Definition is_lim' (f : R -> R) (x l : Rbar) :=
  filterlim f (Rbar_locally x) (Rbar_locally' l).

Definition is_lim (f : R -> R) (x l : Rbar) :=
  match l with
    | Finite l => 
      forall eps : posreal, Rbar_locally x (fun y => Rabs (f y - l) < eps)
    | p_infty => forall M : R, Rbar_locally x (fun y => M < f y)
    | m_infty => forall M : R, Rbar_locally x (fun y => f y < M)
  end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_finite_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).

Lemma is_lim_ :
  forall f x l,
  is_lim f x l <-> is_lim' f x l.
Proof.
destruct l as [l| |] ; split.
- intros H P [eps LP].
  unfold filtermap.
  generalize (H eps).
  apply filter_imp.
  intros u.
  apply LP.
- intros H eps.
  apply (H (fun y => Rabs (y - l) < eps)).
  now exists eps.
- intros H P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros H M.
  apply (H (fun y => M < y)).
  now exists M.
- intros H P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros H M.
  apply (H (fun y => y < M)).
  now exists M.
Qed.

(** Equivalence with standard library Reals *)

Lemma is_lim_Reals_0 (f : R -> R) (x l : R) :
  is_lim f x l -> limit1_in f (fun y => y <> x) l x.
Proof.
  intros H e He ; set (eps := mkposreal e He).
  elim (H eps) ; clear H ; intros (d,Hd) H.
  exists d ; split ; [apply Hd | ].
  intros y Hy ; apply (H y).
  apply Hy.
  apply Hy.
Qed.
Lemma is_lim_Reals_1 (f : R -> R) (x l : R) :
  limit1_in f (fun y => y <> x) l x -> is_lim f x l.
Proof.
  intros H (e,He).
  elim (H e He) ; clear H ; intros d (Hd,H) ; set (delta := mkposreal d Hd).
  exists delta ; intros y Hy Hxy ; apply (H y).
  split.
  by apply Hxy.
  by apply Hy.
Qed.
Lemma is_lim_Reals f x l :
  limit1_in f (fun y => y <> x) l x <-> is_lim f x l.
Proof.
  split ; [apply is_lim_Reals_1|apply is_lim_Reals_0].
Qed.

(** Uniqueness *)

Lemma is_lim_comp_seq (f : R -> R) (x l : Rbar) :
  is_lim f x l -> forall u : nat -> R,
  eventually (fun n => Finite (u n) <> x) ->
  is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
intros Lf u Hu Lu.
apply is_lim_seq_.
apply is_lim_seq_ in Lu.
apply is_lim_ in Lf.
apply filterlim_compose with (2 := Lf).
intros P HP.
destruct x as [x| |] ; try now apply Lu.
specialize (Lu _ HP).
unfold filtermap in Lu |- *.
generalize (filter_and _ _ Hu Lu).
apply filter_imp.
intros n [H Hi].
apply Hi.
contradict H.
now apply f_equal.
Qed.

Lemma is_lim_unique (f : R -> R) (x l : Rbar) :
  is_lim f x l -> Lim f x = l.
Proof.
  intros.
  unfold Lim.
  rewrite (is_lim_seq_unique _ l) //.
  apply (is_lim_comp_seq f x l H).
  exists 1%nat => n Hn.
  case: x {H} => [x | | ] //=.
  apply Rbar_finite_neq, Rgt_not_eq, Rminus_lt_0.
  ring_simplify.
  by apply RinvN_pos.
  by apply is_lim_seq_Rbar_loc_seq.
Qed.
Lemma Lim_correct (f : R -> R) (x : Rbar) :
  ex_lim f x -> is_lim f x (Lim f x).
Proof.
  intros (l,H).
  replace (Lim f x) with l.
    apply H.
  apply sym_eq, is_lim_unique, H.
Qed.

Lemma ex_finite_lim_correct (f : R -> R) (x : Rbar) :
  ex_finite_lim f x <-> ex_lim f x /\ is_finite (Lim f x).
Proof.
  split.
  case => l Hf.
  move: (is_lim_unique f x l Hf) => Hf0.
  split.
  by exists l.
  by rewrite Hf0.
  case ; case => l Hf Hf0.
  exists (real l).
  rewrite -(is_lim_unique _ _ _ Hf).
  rewrite Hf0.
  by rewrite (is_lim_unique _ _ _ Hf).
Qed.
Lemma Lim_correct' (f : R -> R) (x : Rbar) :
  ex_finite_lim f x -> is_lim f x (real (Lim f x)).
Proof.
  intro Hf.
  apply ex_finite_lim_correct in Hf.
  rewrite (proj2 Hf).
  by apply Lim_correct, Hf.
Qed.

Ltac search_lim := let l := fresh "l" in
evar (l : Rbar) ;
match goal with
  | |- Lim _ _ = ?lu => apply is_lim_unique ; replace lu with l ; [ | unfold l]
  | |- is_lim _ _ ?lu => replace lu with l ; [ | unfold l]
end.

(** ** Operations and order *)

(** Extensionality *)

Lemma is_lim_ext_loc (f g : R -> R) (x l : Rbar) :
  Rbar_locally x (fun y => f y = g y)
  -> is_lim f x l -> is_lim g x l.
Proof.
intros Hext Hf.
apply is_lim_ in Hf.
apply is_lim_.
revert Hext Hf.
apply filterlim_ext_loc.
apply Rbar_locally_filter.
Qed.
Lemma ex_lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally x (fun y => f y = g y)
  -> ex_lim f x -> ex_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_lim_ext_loc with f.
Qed.
Lemma Lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally x (fun y => f y = g y)
  -> Lim g x = Lim f x.
Proof.
  move => H.
  apply sym_eq.
  apply Lim_seq_ext_loc.
  move: H.
  apply Rbar_loc_seq_carac.
Qed.

Lemma is_lim_ext (f g : R -> R) (x l : Rbar) :
  (forall y, f y = g y)
  -> is_lim f x l -> is_lim g x l.
Proof.
  move => H.
  apply is_lim_ext_loc.
  by apply Rbar_locally_forall.
Qed.
Lemma ex_lim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y) 
  -> ex_lim f x -> ex_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_lim_ext with f.
Qed.
Lemma Lim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> Lim g x = Lim f x.
Proof.
  move => H.
  apply Lim_ext_loc.
  by apply Rbar_locally_forall.
Qed.

(** Composition *)

Lemma is_lim_comp (f g : R -> R) (x k l : Rbar) :
  is_lim f l k -> is_lim g x l -> Rbar_locally x (fun y => Finite (g y) <> l)
    -> is_lim (fun x => f (g x)) x k.
Proof.
intros Lf Lg Hg.
apply is_lim_ in Lf.
apply is_lim_ in Lg.
apply is_lim_.
revert Lf.
apply filterlim_compose.
intros P HP.
destruct l as [l| |] ; try now apply Lg.
specialize (Lg _ HP).
unfold filtermap in Lg |- *.
generalize (filter_and _ _ Hg Lg).
apply filter_imp.
intros n [H Hi].
apply Hi.
contradict H.
now apply f_equal.
Qed.
Lemma ex_lim_comp (f g : R -> R) (x : Rbar) : 
  ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally x (fun y => Finite (g y) <> Lim g x)
    -> ex_lim (fun x => f (g x)) x.
Proof.
  intros.
  exists (Lim f (Lim g x)).
  apply is_lim_comp with (Lim g x).
  by apply Lim_correct.
  by apply Lim_correct.
  by apply H1.
Qed.
Lemma Lim_comp (f g : R -> R) (x : Rbar) : 
  ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally x (fun y => Finite (g y) <> Lim g x)
    -> Lim (fun x => f (g x)) x = Lim f (Lim g x).
Proof.
  intros.
  apply is_lim_unique.
  apply is_lim_comp with (Lim g x).
  by apply Lim_correct.
  by apply Lim_correct.
  by apply H1.
Qed.

(** Identity *)

Lemma is_lim_id (x : Rbar) :
  is_lim (fun y => y) x x.
Proof.
  case: x => [x | | ] /=.
  move => eps.
  by exists eps.
  move => M ; by exists M.
  move => M ; by exists M.
Qed.
Lemma ex_lim_id (x : Rbar) :
  ex_lim (fun y => y) x.
Proof.
  exists x.
  by apply is_lim_id.
Qed.
Lemma Lim_id (x : Rbar) :
  Lim (fun y => y) x = x.
Proof.
  apply is_lim_unique.
  by apply is_lim_id.
Qed.

(** Constant *)

Lemma is_lim_const (a : R) (x : Rbar) :
  is_lim (fun _ => a) x a.
Proof.
  case: x => [x | | ] /= eps ; exists (mkposreal _ Rlt_0_1) => /= ;
  intros ;
  rewrite Rminus_eq_0 Rabs_R0 ;
  by apply eps.
Qed.
Lemma ex_lim_const (a : R) (x : Rbar) :
  ex_lim (fun _ => a) x.
Proof.
  exists a.
  by apply is_lim_const.
Qed.
Lemma Lim_const (a : R) (x : Rbar) :
  Lim (fun _ => a) x = a.
Proof.
  apply is_lim_unique.
  by apply is_lim_const.
Qed.

(** *** Additive operators *)

(** Opposite *)

Lemma is_lim_opp (f : R -> R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun y => - f y) x (Rbar_opp l).
Proof.
  case: l => [l | | ] Hf eps ;
  [move: (Hf eps) | move: (Hf (-eps)) | move : (Hf (-eps))] => {Hf} ;
  apply Rbar_locally_imply ;
  apply Rbar_locally_forall => y Hf.
  by rewrite /Rminus -Ropp_plus_distr Rabs_Ropp.
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
Qed.
Lemma ex_lim_opp (f : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim (fun y => - f y) x.
Proof.
  case => l Hf.
  exists (Rbar_opp l).
  by apply is_lim_opp.
Qed.
Lemma Lim_opp (f : R -> R) (x : Rbar) :
  Lim (fun y => - f y) x = Rbar_opp (Lim f x).
Proof.
  rewrite -Lim_seq_opp.
  by apply Lim_seq_ext.
Qed.

(** Addition *)

Lemma is_lim_plus (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg
  -> is_Rbar_plus lf lg (Rbar_plus lf lg)
  -> is_lim (fun y => f y + g y) x (Rbar_plus lf lg).
Proof.
  wlog: lf lg f g / (Rbar_le lf lg) => [Hw | Hl].
    case: (Rbar_le_lt_dec lf lg) => Hl Hf Hg Hfg.
    by apply Hw.
    apply is_lim_ext with (fun y : R => g y + f y).
    move => y ; by apply Rplus_comm.
    rewrite Rbar_plus_comm.
    apply Hw.
    by apply Rbar_lt_le.
    by apply Hg.
    by apply Hf.
    apply is_Rbar_plus_comm.
    by rewrite Rbar_plus_comm.
  case: lf Hl => [lf | | ] //= ; case: lg => [lg | | ] => //= Hl Hf Hg _ eps ;
  try by case: Hl.
  move: (Hg (pos_div_2 eps)) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (pos_div_2 eps)) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  rewrite (double_var eps).
  replace (f y + g y - (lf + lg)) with ((f y - lf) + (g y - lg)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  by apply Rplus_lt_compat.
  move: (Hg (eps - (lf - 1))) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (mkposreal _ Rlt_0_1)) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  apply Rabs_lt_between' in Hf.
  replace (eps) with ((lf - 1) + (eps - (lf - 1))) by ring.
  apply Rplus_lt_compat.
  by apply Hf.
  by apply Hg.
  move: (Hg (eps / 2)) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (eps / 2)) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  rewrite (double_var eps).
  by apply Rplus_lt_compat.
  move: (Hg (mkposreal _ Rlt_0_1)) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (eps - (lg + 1))) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  apply Rabs_lt_between' in Hg.
  replace (eps) with ((eps - (lg + 1)) + (lg + 1)) by ring.
  apply Rplus_lt_compat.
  by apply Hf.
  by apply Hg.
  move: (Hg (eps / 2)) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (eps / 2)) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  rewrite (double_var eps).
  by apply Rplus_lt_compat.
Qed.
Lemma ex_lim_plus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x
  -> (exists l, is_Rbar_plus (Lim f x) (Lim g x) l)
  -> ex_lim (fun y => f y + g y) x.
Proof.
  move/Lim_correct => Hf ; move/Lim_correct => Hg [l Hl].
  exists l.
  rewrite -(Rbar_plus_correct _ _ _ Hl).
  apply is_lim_plus.
  by apply Hf.
  by apply Hg.
  by rewrite (Rbar_plus_correct _ _ _ Hl).
Qed.
Lemma Lim_plus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x
  -> (exists l, is_Rbar_plus (Lim f x) (Lim g x) l)
  -> Lim (fun y => f y + g y) x = Rbar_plus (Lim f x) (Lim g x).
Proof.
  move/Lim_correct => Hf ; move/Lim_correct => Hg [l Hl].
  apply is_lim_unique.
  apply is_lim_plus.
  by apply Hf.
  by apply Hg.
  by rewrite (Rbar_plus_correct _ _ _ Hl).
Qed.

(** Subtraction *)

Lemma is_lim_minus (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg
  -> is_Rbar_minus lf lg (Rbar_minus lf lg)
  -> is_lim (fun y => f y - g y) x (Rbar_minus lf lg).
Proof.
  move => Hf Hg Hl.
  apply is_lim_plus.
  by apply Hf.
  apply is_lim_opp.
  by apply Hg.
  by apply Hl.
Qed.
Lemma ex_lim_minus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x
  -> (exists l, is_Rbar_minus (Lim f x) (Lim g x) l)
  -> ex_lim (fun y => f y - g y) x.
Proof.
  move => Hf Hg Hl.
  apply ex_lim_plus.
  by apply Hf.
  apply ex_lim_opp.
  by apply Hg.
  rewrite Lim_opp.
  by apply Hl.
Qed.
Lemma Lim_minus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x
  -> (exists l, is_Rbar_minus (Lim f x) (Lim g x) l)
  -> Lim (fun y => f y - g y) x = Rbar_minus (Lim f x) (Lim g x).
Proof.
  move => Hf Hg Hl.
  rewrite Lim_plus.
  by rewrite Lim_opp.
  by apply Hf.
  apply ex_lim_opp.
  by apply Hg.
  rewrite Lim_opp.
  by apply Hl.
Qed.

(** ** Multiplicative operators *)
(** Multiplicative inverse *)

Lemma is_lim_inv (f : R -> R) (x l : Rbar) :
  is_lim f x l -> l <> 0 -> is_lim (fun y => / f y) x (Rbar_inv l).
Proof.
  move => Hf Hl.
  suff Hf' : Rbar_locally x (fun y => Rabs (f y) > Rabs (real l) / 2).
  wlog: l f Hf Hf' Hl / (Rbar_lt 0 l) => [Hw | Hl'].
    case: (Rbar_le_lt_dec l 0) => Hl'.
    case: Hl' => // Hl'.
    search_lim.
    apply is_lim_ext_loc with (fun y => -/- (f y)).
    move: Hf' ; apply Rbar_locally_imply ; apply Rbar_locally_forall => y Hy.
    field.
    suff H : Rabs (f y) <> 0.
      contradict H ; by rewrite H Rabs_R0.
    apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hy).
    apply Rdiv_le_0_compat.
    by apply Rabs_pos.
    by apply Rlt_0_2.
    apply is_lim_opp.
    apply Hw.
    apply is_lim_opp.
    by apply Hf.
    move: Hf' ; apply Rbar_locally_imply ; apply Rbar_locally_forall => y Hy.
    by rewrite Rbar_opp_real ?Rabs_Ropp.
    contradict Hl.
    by rewrite -(Rbar_opp_involutive l) Hl /= Ropp_0.
    apply Rbar_opp_lt ; by rewrite Rbar_opp_involutive /= Ropp_0.
    case: (l) Hl => [r | | ] /= Hl ; apply Rbar_finite_eq ; field ;
    by apply Rbar_finite_neq.
    by apply Hw.

  case: l Hl Hl' Hf Hf' => [l | | ] //= Hl Hl' Hf Hf' eps.
  set e := eps * Rabs ((l / 2) * l).
  suff He : 0 < e.
  move: (Hf (mkposreal _ He)) => {Hf} /= ; apply Rbar_locally_imply.
  move: Hf' ; apply Rbar_locally_imply, Rbar_locally_forall => y Hf' Hf.
  field_simplify (/ f y - / l) ; [ | split => // ; apply Rbar_finite_neq => //].
  rewrite Rabs_div.
  replace (- f y + l) with (-(f y - l)) by ring ;
  rewrite Rabs_Ropp.
  apply Rlt_div_l.
  apply Rabs_pos_lt.
  apply Rmult_integral_contrapositive_currified.
  suff H : Rabs (f y) <> 0.
    contradict H ; by rewrite H Rabs_R0.
  apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hf').
  apply Rdiv_le_0_compat.
  by apply Rabs_pos.
  by apply Rlt_0_2.
  by apply Rbar_finite_neq.
  apply Rlt_le_trans with (1 := Hf).
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  rewrite Rabs_mult Rabs_mult.
  apply Rmult_le_compat_r.
  by apply Rabs_pos.
  rewrite (Rabs_div _ _ (Rgt_not_eq _ _ Rlt_0_2)).
  rewrite (Rabs_pos_eq 2 (Rlt_le _ _ Rlt_0_2)).
  apply Rlt_le, Hf'.
  apply Rmult_integral_contrapositive_currified.
  suff H : Rabs (f y) <> 0.
    contradict H ; by rewrite H Rabs_R0.
  apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hf').
  apply Rdiv_le_0_compat.
  by apply Rabs_pos.
  by apply Rlt_0_2.
  by apply Rbar_finite_neq.
  suff H : Rabs (f y) <> 0.
    apply Rbar_finite_neq ;
    contradict H ; by rewrite H /= Rabs_R0.
  apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hf').
  apply Rdiv_le_0_compat.
  by apply Rabs_pos.
  by apply Rlt_0_2.
  apply Rmult_lt_0_compat.
  by apply eps.
  apply Rabs_pos_lt.
  apply Rbar_finite_neq in Hl.
  apply Rgt_not_eq.
  apply Rmult_lt_0_compat.
  apply (is_pos_div_2 (mkposreal _ Hl')).
  by apply Hl'.
  
  move: (Hf (/eps)) ; apply Rbar_locally_imply.
  move: (Hf 0) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf0 Hf.
  rewrite Rminus_0_r Rabs_Rinv.
  replace (pos eps) with (/ / eps).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  by apply Rinv_0_lt_compat, eps.
  apply Rabs_pos_lt, Rgt_not_eq, Hf0.
  rewrite Rabs_pos_eq.
  by apply Hf.
  by apply Rlt_le.
  field ; apply Rgt_not_eq, eps.
  by apply Rgt_not_eq.

  case: l Hf Hl => [l | | ] /= Hf Hl.
  apply Rbar_finite_neq, Rabs_pos_lt in Hl.
  move: (Hf (pos_div_2 (mkposreal _ Hl))) => /= {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf.
  apply Rabs_lt_between' in Hf.
  case: Hf ; rewrite /(Rabs l).
  case: Rcase_abs => Hl' Hf1 Hf2 ;
  field_simplify in Hf1 ; rewrite Rdiv_1 in Hf1 ;
  field_simplify in Hf2 ; rewrite Rdiv_1 in Hf2.
  rewrite Rabs_left.
  rewrite /Rdiv Ropp_mult_distr_l_reverse.
  apply Ropp_lt_contravar.
  by apply Hf2.
  apply Rlt_trans with (1 := Hf2).
  apply Rlt_div_l.
  by apply Rlt_0_2.
  by rewrite Rmult_0_l.
  rewrite Rabs_pos_eq.
  by [].
  apply Rlt_le, Rle_lt_trans with (2 := Hf1).
  apply Rdiv_le_0_compat.
  by apply Rge_le.
  by apply Rlt_0_2.
  move: (Hf 0) ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y {Hf} Hf.
  rewrite Rabs_R0 /Rdiv Rmult_0_l Rabs_pos_eq.
  by [].
  by apply Rlt_le.
  move: (Hf 0) ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y {Hf} Hf.
  rewrite Rabs_R0 /Rdiv Rmult_0_l Rabs_left.
  apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
  by [].
Qed.
Lemma ex_lim_inv (f : R -> R) (x : Rbar) :
  ex_lim f x -> Lim f x <> 0 -> ex_lim (fun y => / f y) x.
Proof.
  move/Lim_correct => Hf Hlf.
  exists (Rbar_inv (Lim f x)).
  by apply is_lim_inv.
Qed.
Lemma Lim_inv (f : R -> R) (x : Rbar) :
  ex_lim f x -> Lim f x <> 0 -> Lim (fun y => / f y) x = Rbar_inv (Lim f x).
Proof.
  move/Lim_correct => Hf Hlf.
  apply is_lim_unique.
  by apply is_lim_inv.
Qed.

(** Multiplication *)

Lemma is_lim_mult (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg
  -> is_Rbar_mult lf lg (Rbar_mult lf lg)
  -> is_lim (fun y => f y * g y) x (Rbar_mult lf lg).
Proof.
  case: (Rbar_eq_dec lf 0) => [ -> /= | Hlf].
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // {H} _ _.
  case: lg => [lg | | ] //= Hf Hg _ eps.
  move: (Hg (mkposreal _ Rlt_0_1)) => {Hg} /= ; apply Rbar_locally_imply.
  suff Hef : 0 < eps / (1 + Rabs lg).
  move: (Hf (mkposreal _ Hef)) => {Hf} /= ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  rewrite Rmult_0_l Rminus_0_r Rabs_mult.
  apply Rle_lt_trans with (1 := Rabs_triang_inv _ _) in Hg.
  apply Rlt_minus_l in Hg.
  rewrite Rminus_0_r in Hf.
  replace (pos eps) with ((eps / (1 + Rabs lg))*(1 + Rabs lg)).
  apply Rmult_le_0_lt_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  by apply Hf.
  by apply Hg.
  field ; apply Rgt_not_eq, Rplus_lt_le_0_compat.
  by apply Rlt_0_1.
  by apply Rabs_pos.
  apply Rdiv_lt_0_compat.
  by apply eps.
  apply Rplus_lt_le_0_compat.
  by apply Rlt_0_1.
  by apply Rabs_pos.
  
  case: (Rbar_eq_dec lg 0) => [ -> /= | Hlg].
  rewrite Rbar_mult_comm ; rewrite is_Rbar_mult_comm => /=.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // {H} _ _.
  case: lf Hlf => [lf | | ] //= Hlf Hf Hg _ eps.
  suff Heg : 0 < eps / (1 + Rabs lf).
  move: (Hg (mkposreal _ Heg)) => {Hg} /= ; apply Rbar_locally_imply.
  move: (Hf (mkposreal _ Rlt_0_1)) => {Hf} /= ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  rewrite Rmult_0_l Rminus_0_r Rabs_mult.
  apply Rle_lt_trans with (1 := Rabs_triang_inv _ _) in Hf.
  apply Rlt_minus_l in Hf.
  rewrite Rminus_0_r in Hg.
  replace (pos eps) with ((1 + Rabs lf) * (eps / (1 + Rabs lf))).
  apply Rmult_le_0_lt_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  by apply Hf.
  by apply Hg.
  field ; apply Rgt_not_eq, Rplus_lt_le_0_compat.
  by apply Rlt_0_1.
  by apply Rabs_pos.
  apply Rdiv_lt_0_compat.
  by apply eps.
  apply Rplus_lt_le_0_compat.
  by apply Rlt_0_1.
  by apply Rabs_pos.
  
  wlog: lf lg f g Hlf Hlg / (Rbar_lt 0 lf) => [Hw | {Hlf} Hlf].
    case: (Rbar_lt_le_dec 0 lf) => Hlf'.
    apply Hw ; intuition.
    case: Hlf' => // Hlf'.
    apply Rbar_opp_lt in Hlf' ; simpl Rbar_opp in Hlf' ; rewrite Ropp_0 in Hlf'.
    move => Hf Hg Hm.
    search_lim.
    apply is_lim_ext with (fun y => -((-f y) * g y)).
    move => y ; ring.
    apply is_lim_opp.
    apply Hw.
    instantiate (1 := Rbar_opp lf).
    case: (Rbar_opp lf) Hlf' => //= r H.
    by apply Rbar_finite_neq, Rgt_not_eq.
    by instantiate (1 := lg).
    by [].
    by apply is_lim_opp.
    by [].
    case: (lf) (lg) Hlf' Hm => [y | | ] ; case => [z | | ] //= Hlf' Hm.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlf') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlf') => //.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlf') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlf') => //.
    case: Rle_dec Hm => //= H .
    case: Rle_lt_or_eq_dec => //.
    case: (lf) (lg) Hlf' Hm => [y | | ] ; case => [z | | ] //= Hlf' Hm.
    apply Rbar_finite_eq ; ring.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlf') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlf') => //.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlf') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlf') => //.
    case: Rle_dec Hm => //= H .
    case: Rle_lt_or_eq_dec => //.
  wlog: lf lg f g Hlf Hlg / (Rbar_lt 0 lg) => [Hw | {Hlg} Hlg].
    case: (Rbar_lt_le_dec 0 lg) => Hlg'.
    apply Hw ; intuition.
    case: Hlg' => // Hlg'.
    apply Rbar_opp_lt in Hlg' ; simpl Rbar_opp in Hlg' ; rewrite Ropp_0 in Hlg'.
    move => Hf Hg Hm.
    search_lim.
    apply is_lim_ext with (fun y => -(f y * (- g y))).
    move => y ; ring.
    apply is_lim_opp.
    apply Hw.
    by instantiate (1 := lf).
    instantiate (1 := Rbar_opp lg).
    case: (Rbar_opp lg) Hlg' => //= r H.
    by apply Rbar_finite_neq, Rgt_not_eq.
    by [].
    by [].
    by apply is_lim_opp.
    case: (lg) (lf) Hlg' Hm => [y | | ] ; case => [z | | ] //= Hlg' Hm.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlg') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlg') => //.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlg') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlg') => //.
    case: Rle_dec Hm => //= H .
    case: Rle_lt_or_eq_dec => //.
    case: (lg) (lf) Hlg' Hm => [y | | ] ; case => [z | | ] //= Hlg' Hm.
    apply Rbar_finite_eq ; ring.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlg') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlg') => //.
    have : ~ 0 <= y.
      apply Rlt_not_le, Ropp_lt_cancel.
      by rewrite Ropp_0.
    case: Rle_dec Hm => //= H Hm _.
    case: Rle_dec (Rlt_le _ _ Hlg') => //= H0 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlg') => //.
    case: Rle_dec Hm => //= H .
    case: Rle_lt_or_eq_dec => //.

  wlog: lf lg f g Hlf Hlg / (Rbar_le lf lg) => [Hw | Hl].
    case: (Rbar_le_lt_dec lf lg) => Hl Hf Hg Hfg.
    by apply Hw.
    apply is_lim_ext with (fun y : R => g y * f y).
    move => y ; by apply Rmult_comm.
    rewrite Rbar_mult_comm.
    apply Hw.
    by [].
    by [].
    by apply Rbar_lt_le.
    by apply Hg.
    by apply Hf.
    apply is_Rbar_mult_comm.
    by rewrite Rbar_mult_comm.

  case: lf Hlf Hl => [lf | | ] //= Hlf ; case: lg Hlg => [lg | | ] => //= Hlg Hl Hf Hg Hm ;
  try by case: Hl.
  
  move => eps.
  set ef := eps / 2 / Rmax 1 (Rabs lg).
  set eg := eps / 2 / (ef + Rabs lf).
  suff Hef : 0 < ef.
  suff Heg : 0 < eg.
  move: (Hg (mkposreal _ Heg)) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (mkposreal _ Hef)) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  replace (f y * g y - lf * lg) with (f y * (g y - lg) + (f y - lf) * lg) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite ?Rabs_mult (double_var eps).
  rewrite Rplus_comm.
  apply Rplus_lt_compat.
  apply Rle_lt_trans with (1 := Rmult_le_compat_l _ _ _ (Rabs_pos _) (Rmax_r 1 _)).
  apply Rlt_div_r.
  apply Rlt_le_trans with (1 := Rlt_0_1).
  by apply Rmax_l.
  by apply Hf.
  apply Rle_lt_trans with (1 := Rabs_triang_inv _ _) in Hf.
  apply -> Rlt_minus_l in Hf.
  apply Rle_lt_trans with (1 := Rmult_le_compat_r _ _ _ (Rabs_pos _) (Rlt_le _ _ Hf)).
  rewrite Rmult_comm.
  apply Rlt_div_r.
  apply Rplus_lt_le_0_compat.
  by apply Hef.
  by apply Rabs_pos.
  by apply Hg.
  apply Rdiv_lt_0_compat.
  by apply is_pos_div_2.
  apply Rplus_lt_le_0_compat.
  by apply Hef.
  by apply Rabs_pos.
  apply Rdiv_lt_0_compat.
  by apply is_pos_div_2.
  apply Rlt_le_trans with (1 := Rlt_0_1).
  by apply Rmax_l.
  
  case: Rle_dec (Rlt_le _ _ Hlf) Hm => Hlf' _ Hm //=.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hlf) Hm => _ _ _ //=.
  move => M.
  move: (Hg (Rmax 0 M / (lf / 2))) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (pos_div_2 (mkposreal _ Hlf))) => /= {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  apply Rabs_lt_between' in Hf ; case: Hf => Hf _ ; field_simplify in Hf.
  rewrite Rdiv_1 in Hf.
  replace M with ((lf / 2) * (M / (lf / 2))) by (field ; apply Rgt_not_eq, Hlf).
  apply Rle_lt_trans with (lf / 2 * (Rmax 0 M / (lf / 2))).
  apply Rmult_le_compat_l.
  apply Rlt_le, (is_pos_div_2 (mkposreal _ Hlf)).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, (is_pos_div_2 (mkposreal _ Hlf)).
  by apply Rmax_r.
  apply Rmult_le_0_lt_compat.
  apply Rlt_le, (is_pos_div_2 (mkposreal _ Hlf)).
  apply Rdiv_le_0_compat.
  by apply Rmax_l.
  apply (is_pos_div_2 (mkposreal _ Hlf)).
  by apply Hf.
  by apply Hg.
  clear Hm.
  
  move => M.
  move: (Hg 1) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (Rmax 0 M)) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  apply Rle_lt_trans with (1 := Rmax_r 0 M).
  rewrite -(Rmult_1_r (Rmax 0 M)).
  apply Rmult_le_0_lt_compat.
  by apply Rmax_l.
  by apply Rle_0_1.
  by apply Hf.
  by apply Hg.
Qed.
Lemma ex_lim_mult (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x
  -> (exists l, is_Rbar_mult (Lim f x) (Lim g x) l)
  -> ex_lim (fun y => f y * g y) x.
Proof.
  move/Lim_correct => Hf ; move/Lim_correct => Hg [l Hl].
  exists l.
  rewrite -(Rbar_mult_correct _ _ _ Hl).
  apply is_lim_mult.
  by apply Hf.
  by apply Hg.
  by rewrite (Rbar_mult_correct _ _ _ Hl).
Qed.
Lemma Lim_mult (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x
  -> (exists l, is_Rbar_mult (Lim f x) (Lim g x) l)
  -> Lim (fun y => f y * g y) x = Rbar_mult (Lim f x) (Lim g x).
Proof.
  move/Lim_correct => Hf ; move/Lim_correct => Hg [l Hl].
  apply is_lim_unique.
  apply is_lim_mult.
  by apply Hf.
  by apply Hg.
  by rewrite (Rbar_mult_correct _ _ _ Hl).
Qed.

(** Scalar multiplication *)

Lemma is_lim_scal_l (f : R -> R) (a : R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun y => a * f y) x (Rbar_mult a l).
Proof.
  move => Hf.
  case: (Req_dec 0 a) => [<- {a} | Ha].
  replace (Rbar_mult 0 l) with (Finite 0).
  apply is_lim_ext with (fun _ => 0).
  move => y ; by rewrite Rmult_0_l.
  by apply is_lim_const.
  case: l {Hf} => [l | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //.
  case: Rle_dec (Rle_refl 0) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //.
  
  apply is_lim_mult.
  by apply is_lim_const.
  by apply Hf.
  case: l {Hf} => [l | | ] //= ;
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  by apply Rnot_le_lt.
  case: Rle_lt_or_eq_dec => //.
  by apply Rnot_le_lt.
Qed.
Lemma ex_lim_scal_l (f : R -> R) (a : R) (x : Rbar) :
  ex_lim f x -> ex_lim (fun y => a * f y) x.
Proof.
  case => l Hf.
  exists (Rbar_mult a l).
  by apply is_lim_scal_l.
Qed.
Lemma Lim_scal_l (f : R -> R) (a : R) (x : Rbar) :
  Lim (fun y => a * f y) x = Rbar_mult a (Lim f x).
Proof.
  apply Lim_seq_scal_l.
Qed.

Lemma is_lim_scal_r (f : R -> R) (a : R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun y => f y * a) x (Rbar_mult l a).
Proof.
  move => Hf.
  rewrite Rbar_mult_comm.
  apply is_lim_ext with (fun y => a * f y).
  move => y ; by apply Rmult_comm.
  by apply is_lim_scal_l.
Qed.
Lemma ex_lim_scal_r (f : R -> R) (a : R) (x : Rbar) :
  ex_lim f x -> ex_lim (fun y => f y * a) x.
Proof.
  case => l Hf.
  exists (Rbar_mult l a).
  by apply is_lim_scal_r.
Qed.
Lemma Lim_scal_r (f : R -> R) (a : R) (x : Rbar) :
  Lim (fun y => f y * a) x = Rbar_mult (Lim f x) a.
Proof.
  rewrite Rbar_mult_comm -Lim_seq_scal_l.
  apply Lim_seq_ext.
  move => y ; by apply Rmult_comm.
Qed.

(** Division *)

Lemma is_lim_div (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg -> lg <> 0
  -> is_Rbar_div lf lg (Rbar_div lf lg)
  -> is_lim (fun y => f y / g y) x (Rbar_div lf lg).
Proof.
  move => Hf Hg Hlg Hl.
  apply is_lim_mult.
  by apply Hf.
  apply is_lim_inv.
  by apply Hg.
  by apply Hlg.
  by apply Hl.
Qed.
Lemma ex_lim_div (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x -> Lim g x <> 0
  -> (exists l, is_Rbar_div (Lim f x) (Lim g x) l)
  -> ex_lim (fun y => f y / g y) x.
Proof.
  move => Hf Hg Hlg Hl.
  apply ex_lim_mult.
  by apply Hf.
  apply ex_lim_inv.
  by apply Hg.
  by apply Hlg.
  rewrite Lim_inv.
  by apply Hl.
  by apply Hg.
  by apply Hlg.
Qed.
Lemma Lim_div (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x -> Lim g x <> 0
  -> (exists l, is_Rbar_div (Lim f x) (Lim g x) l)
  -> Lim (fun y => f y / g y) x = Rbar_div (Lim f x) (Lim g x).
Proof.
  move => Hf Hg Hlg Hl.
  rewrite Lim_mult.
  by rewrite Lim_inv.
  by apply Hf.
  apply ex_lim_inv.
  by apply Hg.
  by apply Hlg.
  rewrite Lim_inv.
  by apply Hl.
  by apply Hg.
  by apply Hlg.
Qed.

(** Composition by linear functions *)

Lemma is_lim_comp_lin (f : R -> R) (a b : R) (x l : Rbar) :
  is_lim f (Rbar_plus (Rbar_mult a x) b) l -> a <> 0
  -> is_lim (fun y => f (a * y + b)) x l.
Proof.
  move => Hf Ha.
  apply is_lim_comp with (Rbar_plus (Rbar_mult a x) b).
  by apply Hf.
  search_lim.
  apply is_lim_plus.
  apply is_lim_scal_l.
  apply is_lim_id.
  apply is_lim_const.
  case: (Rbar_mult a x) => //.
  by [].
  case: x {Hf} => [x | | ] //=.
  exists (mkposreal _ Rlt_0_1) => y _ Hy.
  apply Rbar_finite_neq, Rminus_not_eq ; ring_simplify (a * y + b - (a * x + b)).
  rewrite -Rmult_minus_distr_l.
  apply Rmult_integral_contrapositive ; split.
  by [].
  by apply Rminus_eq_contra.
  exists 0 => x Hx.
  apply sym_not_eq in Ha.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  exists 0 => x Hx.
  apply sym_not_eq in Ha.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma ex_lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) :
  ex_lim f (Rbar_plus (Rbar_mult a x) b)
  -> ex_lim (fun y => f (a * y + b)) x.
Proof.
  case => l Hf.
  case: (Req_dec a 0) => [-> {a Hf} | Ha].
  apply ex_lim_ext with (fun _ => f b).
  move => y ; by rewrite Rmult_0_l Rplus_0_l.
  by apply ex_lim_const.
  exists l ; by apply is_lim_comp_lin.
Qed.
Lemma Lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) :
  ex_lim f (Rbar_plus (Rbar_mult a x) b) -> a <> 0 -> 
  Lim (fun y => f (a * y + b)) x = Lim f (Rbar_plus (Rbar_mult a x) b).
Proof.
  move => Hf Ha.
  apply is_lim_unique.
  apply is_lim_comp_lin.
  by apply Lim_correct.
  exact: Ha.
Qed.

(** Continuity and limit *)

Lemma is_lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> is_lim f x (f x).
Proof.
  move => Hf eps.
  case: (Hf eps (cond_pos eps)) => {Hf} /= d [Hd Hf].
  exists (mkposreal _ Hd) => /= y Hy Hxy.
  apply Hf.
  split.
  split.
  by [].
  by apply sym_not_eq.
  by apply Hy.
Qed.
Lemma ex_lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> ex_finite_lim f x.
Proof.
  move => Hf.
  exists (f x).
  by apply is_lim_continuity.
Qed.
Lemma Lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> Lim f x = f x.
Proof.
  move => Hf.
  apply is_lim_unique.
  by apply is_lim_continuity.
Qed.

(** *** Order *)

Lemma is_lim_le_loc (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg
  -> Rbar_locally x (fun y => f y <= g y)
  -> Rbar_le lf lg.
Proof.
  case: lf => [lf | | ] /= Hf ;
  case: lg => [lg | | ] /= Hg Hfg ;
  try by [left | right].
  
  apply Rbar_finite_le.
  apply Rnot_lt_le => H.
  apply Rminus_lt_0 in H.
  apply (Rbar_locally_const x).
  move: Hfg ; apply Rbar_locally_imply.
  move: (Hg (pos_div_2 (mkposreal _ H))) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (pos_div_2 (mkposreal _ H))) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  apply Rlt_not_le.
  apply Rlt_trans with ((lf + lg) / 2).
  replace ((lf + lg) / 2) with (lg + (lf - lg) / 2) by field.
  apply Rabs_lt_between'.
  apply Hg.
  replace ((lf + lg) / 2) with (lf - (lf - lg) / 2) by field.
  apply Rabs_lt_between'.
  apply Hf.

  left => /=.
  apply (Rbar_locally_const x).
  move: Hfg ; apply Rbar_locally_imply.
  move: (Hg (lf - (Rabs lf + 1))) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (mkposreal _ (Rle_lt_0_plus_1 _ (Rabs_pos lf)))) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  apply Rlt_not_le.
  apply Rlt_trans with (lf - (Rabs lf + 1)).
  apply Hg.
  apply Rabs_lt_between'.
  apply Hf.
  
  left => /=.
  apply (Rbar_locally_const x).
  move: Hfg ; apply Rbar_locally_imply.
  move: (Hg (mkposreal _ (Rle_lt_0_plus_1 _ (Rabs_pos lg)))) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (lg + (Rabs lg + 1))) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  apply Rlt_not_le.
  apply Rlt_trans with (lg + (Rabs lg + 1)).
  apply Rabs_lt_between'.
  apply Hg.
  apply Hf.
  
  left => /=.
  apply (Rbar_locally_const x).
  move: Hfg ; apply Rbar_locally_imply.
  move: (Hg 0) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf 0) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y /= Hf Hg.
  apply Rlt_not_le.
  apply Rlt_trans with 0.
  apply Hg.
  apply Hf.
Qed.

Lemma is_lim_le_p_loc (f g : R -> R) (x : Rbar) :
  is_lim f x p_infty
  -> Rbar_locally x (fun y => f y <= g y)
  -> is_lim g x p_infty.
Proof.
  move => Hf Hfg M.
  move: Hfg ; apply Rbar_locally_imply.
  move: (Hf M) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  apply Rlt_le_trans with (f y).
  by apply Hf.
  by apply Hg.
Qed.

Lemma is_lim_le_m_loc (f g : R -> R) (x : Rbar) :
  is_lim f x m_infty
  -> Rbar_locally x (fun y => g y <= f y)
  -> is_lim g x m_infty.
Proof.
  move => Hf Hfg M.
  move: Hfg ; apply Rbar_locally_imply.
  move: (Hf M) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  apply Rle_lt_trans with (f y).
  by apply Hg.
  by apply Hf.
Qed.


Lemma is_lim_le_le_loc (f g h : R -> R) (x : Rbar) (l : R) :
  is_lim f x l -> is_lim g x l
  -> Rbar_locally x (fun y => f y <= h y <= g y)
  -> is_lim h x l.
Proof.
  move => /= Hf Hg H eps.
  move: H ; apply Rbar_locally_imply.
  move: (Hg eps) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf eps) => {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg H.
  apply Rabs_lt_between' ; split.
  apply Rlt_le_trans with (2 := proj1 H).
  by apply Rabs_lt_between', Hf.
  apply Rle_lt_trans with (1 := proj2 H).
  by apply Rabs_lt_between', Hg.
Qed.

(** ** Generalized intermediate value theorem *)

Lemma IVT_gen (f : R -> R) (a b y : R) :
  continuity f 
  -> Rmin (f a) (f b) <= y <= Rmax (f a) (f b)
  -> { x : R | Rmin a b <= x <= Rmax a b /\ f x = y }.
Proof.
  case: (Req_EM_T a b) => [ <- {b} | Hab].
    rewrite /Rmin /Rmax ; case: Rle_dec (Rle_refl a) (Rle_refl (f a)) ;
    case: Rle_dec => // _ _ _ _ Cf Hy.
    exists a ; split.
    split ; by apply Rle_refl.
    apply Rle_antisym ; by apply Hy.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: (Rle_lt_or_eq_dec _ _ Hab') => {Hab'} // Hab'.
    by apply Hw.
    rewrite (Rmin_comm (f a)) (Rmin_comm a) (Rmax_comm (f a)) (Rmax_comm a) ;
    apply Hw => //.
    by apply Rlt_not_eq.
  rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  wlog: f y / (f a <= f b) => [Hw |].
    case: (Rle_lt_dec (f a) (f b)) => Hf' Hf Hy.
    by apply Hw.
    case: (Hw (fun y => - f y) (- y)).
    by apply Ropp_le_contravar, Rlt_le.
    by apply continuity_opp.
    rewrite Rmin_opp_Rmax Rmax_opp_Rmin ;
    split ; apply Ropp_le_contravar, Hy.
    move => x [Hx Hfx].
    exists x ; intuition.
    by rewrite -(Ropp_involutive y) -Hfx Ropp_involutive.
  rewrite /Rmin /Rmax ; case: Rle_dec =>  // _ _.
  wlog: y / (f a < y < f b) => [Hw Hf Hy | Hy Hf _].
    case: Hy => Hay Hyb.
    case: (Rle_lt_or_eq_dec _ _ Hay) => {Hay} [Hay | <- ].
    case: (Rle_lt_or_eq_dec _ _ Hyb) => {Hyb} [Hyb | -> ].
    apply Hw ; intuition.
    exists b ; intuition.
    exists a ; intuition.

  case (IVT (fun x => f x - y) a b).
  apply continuity_minus.
  exact Hf.
  apply continuity_const.
  intros _ _ ; reflexivity.
  exact Hab.
  apply Rlt_minus_l ; rewrite Rplus_0_l ; apply Hy.
  apply Rlt_minus_r ; rewrite Rplus_0_l ; apply Hy.
  intros x [Hx Hfx].
  apply Rminus_diag_uniq in Hfx.
  by exists x.
Qed.

Lemma IVT_Rbar_incr (f : R -> R) (a b la lb : Rbar) (y : R) :
  is_lim f a la -> is_lim f b lb
  -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x)
  -> (forall (x y : R), Rbar_lt a x -> x < y -> Rbar_lt y b -> f x < f y)
  -> Rbar_lt a b
  -> Rbar_lt la y /\ Rbar_lt y lb
  -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
  move => Hfa Hfb Cf Crf Hab Hy.
  
  suff Hex : (exists x : R, Rbar_lt a x /\ Rbar_lt x b /\ f x <= y).
  suff Hbound : bound (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y).
  case: (completeness _ Hbound Hex) => x [Hub Hlub].
  exists x.

  have Hax : Rbar_lt a x.
    case Ha : a Hab Hfa Hub => [a' | | ] // Hab Hfa Hub.
    case Hla : la Hy Hfa => [la' | | ] [Hy _] Hfa //.
    apply Rminus_lt_0 in Hy.
    case: (Hfa (mkposreal _ Hy)) => //= delta {Hfa} Hfa.
    case Hb : b Hab Hub => [b' | | ] //= Hab Hub.
    apply Rlt_le_trans with (Rmin (a' + delta / 2) ((a'+b')/2)).
    apply Rmin_case.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    pattern a' at 1 ; replace a' with ((a'+a')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Hub.
    repeat split.
    apply Rmin_case.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    pattern a' at 1 ; replace a' with ((a'+a')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rle_lt_trans with (1 := Rmin_r _ _).
    pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rlt_le, (Rplus_lt_reg_r (-la')).
    rewrite ?(Rplus_comm (-la')).
    apply Rle_lt_trans with (1 := Rle_abs _).
    apply Hfa.
    rewrite /Rminus (Rplus_min_distr_r (-a')).
    ring_simplify (a' + delta / 2 + - a').
    field_simplify ((a' + b') / 2 + - a').
    rewrite Rabs_pos_eq.
    apply Rle_lt_trans with (1 := Rmin_l _ _).
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
    apply Rmin_case.
    apply Rlt_le ; by apply is_pos_div_2.
    apply Rdiv_le_0_compat.
    rewrite Rplus_comm Rle_minus_r Rplus_0_l.
    by apply Rlt_le.
    by apply Rlt_0_2.
    apply Rgt_not_eq.
    apply Rmin_case.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    pattern a' at 2 ; replace a' with ((a'+a')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rlt_le_trans with (a' + delta / 2).
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    apply Hub.
    repeat split.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    apply Rlt_le, (Rplus_lt_reg_r (-la')).
    rewrite ?(Rplus_comm (-la')).
    apply Rle_lt_trans with (1 := Rle_abs _).
    apply Hfa.
    ring_simplify (a' + delta / 2 - a').
    rewrite Rabs_pos_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
    apply Rlt_le ; by apply is_pos_div_2.
    apply Rgt_not_eq.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    case: (Hfa y) => {Hfa} delta Hfa.
    case Hb : b Hab Hub => [b' | | ] //= Hab Hub.
    apply Rlt_le_trans with (Rmin (a' + delta / 2) ((a'+b')/2)).
    apply Rmin_case.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    pattern a' at 1 ; replace a' with ((a'+a')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Hub.
    repeat split.
    apply Rmin_case.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    pattern a' at 1 ; replace a' with ((a'+a')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rle_lt_trans with (1 := Rmin_r _ _).
    pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rlt_le, Hfa.
    rewrite /Rminus (Rplus_min_distr_r (-a')).
    ring_simplify (a' + delta / 2 + - a').
    field_simplify ((a' + b') / 2 + - a').
    rewrite Rabs_pos_eq.
    apply Rle_lt_trans with (1 := Rmin_l _ _).
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
    apply Rmin_case.
    apply Rlt_le ; by apply is_pos_div_2.
    apply Rdiv_le_0_compat.
    rewrite Rplus_comm Rle_minus_r Rplus_0_l.
    by apply Rlt_le.
    by apply Rlt_0_2.
    apply Rgt_not_eq.
    apply Rmin_case.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    pattern a' at 2 ; replace a' with ((a'+a')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rlt_le_trans with (a' + delta / 2).
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    apply Hub.
    repeat split.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    apply Rlt_le, Hfa.
    ring_simplify (a' + delta / 2 - a').
    rewrite Rabs_pos_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
    apply Rlt_le ; by apply is_pos_div_2.
    apply Rgt_not_eq.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  split => //.
  have Hxb : Rbar_lt x b.
    case Hb : b Crf Hab Hfb Hlub => [b' | | ] // Crf Hab Hfb Hlub.
    case Hlb : lb Hy Hfb => [lb' | | ] [_ Hy] Hfb //.
    apply Rminus_lt_0 in Hy.
    case: (Hfb (mkposreal _ Hy)) => //= delta {Hfb} Hfb.
    case Ha : a Crf Hab Hlub => [a' | | ] //= Crf Hab Hlub.
    apply Rle_lt_trans with (Rmax (b' - delta / 2) ((a'+b')/2)).
    apply: Hlub => z Hz.
    suff H : f z <= f (Rmax (b' - delta / 2) ((a' + b') / 2)).
      apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
      apply: Crf.
      apply Rlt_le_trans with (2 := Rmax_r _ _).
      pattern a' at 1 ; replace a' with ((a'+a') / 2) by field.
      apply Rmult_lt_compat_r ; intuition.
      by apply H.
      by apply Hz.
    apply Rlt_le.
    apply Rle_lt_trans with y.
    by apply Hz.
    apply Rplus_lt_reg_r with (-lb').
    apply Ropp_lt_cancel.
    apply Rle_lt_trans with (1 := Rle_abs _).
    rewrite Rabs_Ropp Ropp_plus_distr Ropp_involutive Rplus_comm.
    apply Hfb.
    rewrite /Rminus Rplus_max_distr_r.
    ring_simplify (b' + - (delta / 2) + - b').
    field_simplify ((a' + b') / 2 + - b').
    replace ((a' - b') / 2) with (-((b'-a')/2)) by field.
    rewrite Rmax_opp_Rmin Rabs_Ropp Rabs_pos_eq.
    apply Rle_lt_trans with (1 := Rmin_l _ _).
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    apply Rlt_le, Rmin_case.
    by apply is_pos_div_2.
    apply Rdiv_lt_0_compat.
    by apply -> Rminus_lt_0.
    by apply Rlt_0_2.
    apply Rlt_not_eq.
    apply Rmax_case.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rmax_case.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rle_lt_trans with (b' - delta / 2).
    apply: Hlub => z Hz.
    suff H : f z <= f (b' - delta / 2).
      apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
      apply: Crf.
      by [].
      by apply H.
      by apply Hz.
    apply Rlt_le.
    apply Rle_lt_trans with y.
    by apply Hz.
    apply Rplus_lt_reg_r with (-lb').
    apply Ropp_lt_cancel.
    apply Rle_lt_trans with (1 := Rle_abs _).
    rewrite Rabs_Ropp Ropp_plus_distr Ropp_involutive Rplus_comm.
    apply Hfb.
    ring_simplify (b' - (delta / 2) - b').
    rewrite Rabs_Ropp Rabs_pos_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    apply Rlt_le, is_pos_div_2.
    apply Rlt_not_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    case: (Hfb y) => //= delta {Hfb} Hfb.
    case Ha : a Crf Hab Hlub => [a' | | ] //= Crf Hab Hlub.
    apply Rle_lt_trans with (Rmax (b' - delta / 2) ((a'+b')/2)).
    apply: Hlub => z Hz.
    suff H : f z <= f (Rmax (b' - delta / 2) ((a' + b') / 2)).
      apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
      apply: Crf.
      apply Rlt_le_trans with (2 := Rmax_r _ _).
      pattern a' at 1 ; replace a' with ((a'+a') / 2) by field.
      apply Rmult_lt_compat_r ; intuition.
      by apply H.
      by apply Hz.
    apply Rlt_le.
    apply Rle_lt_trans with y.
    by apply Hz.
    apply Hfb.
    rewrite /Rminus Rplus_max_distr_r.
    ring_simplify (b' + - (delta / 2) + - b').
    field_simplify ((a' + b') / 2 + - b').
    replace ((a' - b') / 2) with (-((b'-a')/2)) by field.
    rewrite Rmax_opp_Rmin Rabs_Ropp Rabs_pos_eq.
    apply Rle_lt_trans with (1 := Rmin_l _ _).
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    apply Rlt_le, Rmin_case.
    by apply is_pos_div_2.
    apply Rdiv_lt_0_compat.
    by apply -> Rminus_lt_0.
    by apply Rlt_0_2.
    apply Rlt_not_eq.
    apply Rmax_case.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rmax_case.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
    apply Rmult_lt_compat_r ; intuition.
    apply Rle_lt_trans with (b' - delta / 2).
    apply: Hlub => z Hz.
    suff H : f z <= f (b' - delta / 2).
      apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
      apply: Crf.
      by [].
      by apply H.
      by apply Hz.
    apply Rlt_le.
    apply Rle_lt_trans with y.
    by apply Hz.
    apply Hfb.
    ring_simplify (b' - (delta / 2) - b').
    rewrite Rabs_Ropp Rabs_pos_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    apply Rlt_le, is_pos_div_2.
    apply Rlt_not_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
    by apply is_pos_div_2.
    by case Ha : a Hab.
  split => //.
  move: (Cf _ Hax Hxb) => Hfx.
  apply is_lim_continuity in Hfx.
  apply Rle_antisym.
  apply Rnot_lt_le => H.
  apply Rminus_lt_0 in H.
  case: (Hfx (mkposreal _ H)) => {Hfx} /= delta Hfx.
  apply Rminus_lt_0 in H.
  case Ha : a Hlub Crf Hax => [a' | | ] Hlub Crf //= Hax.
  absurd (Rmax (x - delta / 2) ((x+a')/2) < x).
  apply Rle_not_lt.
  apply Hlub => z Hz.
  suff H0 : f z <= f (Rmax (x - delta / 2) ((x + a') / 2)).
    apply Rnot_lt_le ; contradict H0 ; apply Rlt_not_le.
    apply: Crf.
    apply Rlt_le_trans with (2 := Rmax_r _ _).
    pattern a' at 1 ; replace a' with ((a'+a') / 2) by field.
    apply Rmult_lt_compat_r ; intuition.
    by apply H0.
    by apply Hz.
  apply Rlt_le, Rle_lt_trans with y.
  by apply Hz.
  apply Rplus_lt_reg_r with (-(f x)).
  apply Ropp_lt_cancel.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite Rabs_Ropp Ropp_plus_distr Ropp_involutive Rplus_comm.
  apply Hfx.
  rewrite /Rminus Rplus_max_distr_r.
  ring_simplify (x + - (delta / 2) + - x).
  field_simplify ((x + a') / 2 + - x).
  replace ((-x+a') / 2) with (-((x-a')/2)) by field.
  rewrite Rmax_opp_Rmin Rabs_Ropp Rabs_pos_eq.
  apply Rle_lt_trans with (1 := Rmin_l _ _).
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
  by apply is_pos_div_2.
  apply Rlt_le, Rmin_case.
  by apply is_pos_div_2.
  apply Rdiv_lt_0_compat.
  by apply -> Rminus_lt_0.
  by apply Rlt_0_2.
  apply Rlt_not_eq.
  apply Rmax_case.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
  by apply is_pos_div_2.
  pattern x at 2 ; replace x with ((x+x)/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rmax_case.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
  by apply is_pos_div_2.
  pattern x at 2 ; replace x with ((x+x)/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  absurd ((x - delta / 2) < x).
  apply Rle_not_lt.
  apply Hlub => z Hz.
  suff H0 : f z <= f (x - delta / 2).
    apply Rnot_lt_le ; contradict H0 ; apply Rlt_not_le.
    apply: Crf.
    by [].
    by apply H0.
    by apply Hz.
  apply Rlt_le, Rle_lt_trans with y.
  by apply Hz.
  apply Rplus_lt_reg_r with (-(f x)).
  apply Ropp_lt_cancel.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite Rabs_Ropp Ropp_plus_distr Ropp_involutive Rplus_comm.
  apply Hfx.
  ring_simplify (x - (delta / 2) - x).
  rewrite Rabs_Ropp Rabs_pos_eq.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
  by apply is_pos_div_2.
  apply Rlt_le, is_pos_div_2.
  apply Rlt_not_eq.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
  by apply is_pos_div_2.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ;
  by apply is_pos_div_2.

  apply Rnot_lt_le => H.
  apply Rminus_lt_0 in H.
  case: (Hfx (mkposreal _ H)) => {Hfx} /= delta Hfx.
  apply Rminus_lt_0 in H.
  case Hb : b Hub Crf Hxb => [b' | | ] Hub Crf //= Hxb.
  absurd (x < Rmin (x + delta / 2) ((x+b')/2)).
  apply Rle_not_lt.
  apply Hub ; repeat split.
  apply Rbar_lt_trans with x.
  by apply Hax.
  rewrite /Rmin ; case: Rle_dec => H0.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  pattern x at 1 ; replace x with ((x+x)/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rle_lt_trans with (1 := Rmin_r _ _).
  pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rlt_le, Rplus_lt_reg_r with (-(f x)).
  rewrite ?(Rplus_comm ((- f x))).
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply Hfx.
  rewrite /Rminus Rplus_min_distr_r.
  ring_simplify (x + delta / 2 + - x).
  field_simplify ((x + b') / 2 + - x).
  rewrite Rabs_pos_eq.
  apply Rle_lt_trans with (1 := Rmin_l _ _).
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rmin_case.
  by apply Rlt_le, is_pos_div_2.
  apply Rlt_le, Rdiv_lt_0_compat.
  by rewrite Rplus_comm -Rminus_lt_0.
  by apply Rlt_0_2.
  apply Rgt_not_eq.
  apply Rmin_case.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  pattern x at 2 ; replace x with ((x+x)/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rmin_case.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  pattern x at 1 ; replace x with ((x+x)/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  absurd (x < (x + delta / 2)).
  apply Rle_not_lt.
  apply Hub ; repeat split.
  apply Rbar_lt_trans with x.
  by apply Hax.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  apply Rlt_le, Rplus_lt_reg_r with (-(f x)).
  rewrite ?(Rplus_comm ((- f x))).
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply Hfx.
  ring_simplify (x + delta / 2 - x).
  rewrite Rabs_pos_eq.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  by apply Rlt_le, is_pos_div_2.
  apply Rgt_not_eq.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  case Hb : b Hab Hfb Crf => [b' | | ] Hab Hfb Crf // ; try by case Ha : a Hab.
  exists b' => z Hz.
  apply Rlt_le, Hz.
  case Hlb : lb Hy Hfb => [lb' | | ] [_ Hy] Hfb //.
  apply Rminus_lt_0 in Hy.
  case: (Hfb (mkposreal _ Hy)) => {Hfb} /= d Hfb.
  case Ha: a Hab Crf => [a' | | ] //= Hab Crf.
  exists (Rmax (d+1) (a'+ 1)) => z Hz.
  suff H : f z <= f (Rmax (d + 1) (a' + 1)).
    apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
    apply: Crf.
    apply Rlt_le_trans with (2 := Rmax_r _ _).
    apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
    by apply H.
    by [].
  apply Rlt_le, Rle_lt_trans with y.
  by apply Hz.
  apply Rplus_lt_reg_r with (- lb').
  apply Ropp_lt_cancel.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite Rabs_Ropp Ropp_plus_distr Ropp_involutive Rplus_comm.
  apply Hfb.
  apply Rlt_le_trans with (2 := Rmax_l _ _).
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  exists (d+1) => z Hz.
  suff H : f z <= f (d + 1).
    apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
    apply: Crf.
    by [].
    by apply H.
    by [].
  apply Rlt_le, Rle_lt_trans with y.
  by apply Hz.
  apply Rplus_lt_reg_r with (- lb').
  apply Ropp_lt_cancel.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite Rabs_Ropp Ropp_plus_distr Ropp_involutive Rplus_comm.
  apply Hfb.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  case: (Hfb y) => {Hfb} /= d Hfb.
  case Ha: a Hab Crf => [a' | | ] //= Hab Crf.
  exists (Rmax (d+1) (a'+ 1)) => z Hz.
  suff H : f z <= f (Rmax (d + 1) (a' + 1)).
    apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
    apply: Crf.
    apply Rlt_le_trans with (2 := Rmax_r _ _).
    apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
    by apply H.
    by [].
  apply Rlt_le, Rle_lt_trans with y.
  by apply Hz.
  apply Hfb.
  apply Rlt_le_trans with (2 := Rmax_l _ _).
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  exists (d+1) => z Hz.
  suff H : f z <= f (d + 1).
    apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
    apply: Crf.
    by [].
    by apply H.
    by [].
  apply Rlt_le, Rle_lt_trans with y.
  by apply Hz.
  apply Hfb.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  
  case Hla: la Hy Hfa => [la' | | ] [Hy _] Hfa //.
  apply Rminus_lt_0 in Hy ;
  move: (Hfa (mkposreal _ Hy)) => {Hfa} Hfa ; simpl in Hfa.
  have : Rbar_locally a (fun y0 : R => f y0 < y).
  move: Hfa ; apply Rbar_locally_imply, Rbar_locally_forall => z Hz.
  apply (Rplus_lt_reg_r (-la')).
  rewrite ?(Rplus_comm (-la')).
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply Hz.
  move => {Hfa} Hfa.
  case Ha : a Hab Hfa => [a' | | ] Hab [d Hfa] // ;
  case Hb : b Hab => [b' | | ] Hab //.
  exists (Rmin (a'+d/2) ((a'+b')/2)) ; repeat split.
  apply Rmin_case.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  pattern a' at 1 ; replace a' with ((a'+a')/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rle_lt_trans with (1 := Rmin_r _ _).
  pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rlt_le, Hfa.
  rewrite Rabs_pos_eq.
  apply Rle_lt_trans with (1 := Rplus_le_compat_r _ _ _ (Rmin_l _ _)).
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rmin_case ; field_simplify ; rewrite Rdiv_1.
  apply Rlt_le, is_pos_div_2.
  apply Rlt_le, Rdiv_lt_0_compat, Rlt_0_2.
  by rewrite Rplus_comm -Rminus_lt_0.
  apply Rgt_not_eq, Rminus_lt_0, Rmin_case ;
  field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  apply Rdiv_lt_0_compat, Rlt_0_2.
  by rewrite Rplus_comm -Rminus_lt_0.
  exists (a'+d/2) ; repeat split.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  apply Rlt_le, Hfa.
  rewrite Rabs_pos_eq.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  ring_simplify.
  apply Rlt_le, is_pos_div_2.
  apply Rgt_not_eq, Rminus_lt_0 ;
  field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  exists (Rmin (d-1) (b'-1)) ; repeat split.
  apply Rle_lt_trans with (1 := Rmin_r _ _).
  apply Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  apply Rlt_le, Hfa.
  apply Rle_lt_trans with (1 := Rmin_l _ _).
  apply Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  exists ((d-1)) ; repeat split.
  apply Rlt_le, Hfa.
  apply Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  move: (Hfa y) => {Hfa} Hfa.
  case Ha : a Hab Hfa => [a' | | ] Hab [d Hfa] // ;
  case Hb : b Hab => [b' | | ] Hab //.
  exists (Rmin (a'+d/2) ((a'+b')/2)) ; repeat split.
  apply Rmin_case.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  pattern a' at 1 ; replace a' with ((a'+a')/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rle_lt_trans with (1 := Rmin_r _ _).
  pattern b' at 2 ; replace b' with ((b'+b')/2) by field.
  apply Rmult_lt_compat_r ; intuition.
  apply Rlt_le, Hfa.
  rewrite Rabs_pos_eq.
  apply Rle_lt_trans with (1 := Rplus_le_compat_r _ _ _ (Rmin_l _ _)).
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rmin_case ; field_simplify ; rewrite Rdiv_1.
  apply Rlt_le, is_pos_div_2.
  apply Rlt_le, Rdiv_lt_0_compat, Rlt_0_2.
  by rewrite Rplus_comm -Rminus_lt_0.
  apply Rgt_not_eq, Rminus_lt_0, Rmin_case ;
  field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  apply Rdiv_lt_0_compat, Rlt_0_2.
  by rewrite Rplus_comm -Rminus_lt_0.
  exists (a'+d/2) ; repeat split.
  apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
  apply Rlt_le, Hfa.
  rewrite Rabs_pos_eq.
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  ring_simplify.
  apply Rlt_le, is_pos_div_2.
  apply Rgt_not_eq, Rminus_lt_0 ;
  field_simplify ; rewrite Rdiv_1.
  by apply is_pos_div_2.
  exists (Rmin (d-1) (b'-1)) ; repeat split.
  apply Rle_lt_trans with (1 := Rmin_r _ _).
  apply Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  apply Rlt_le, Hfa.
  apply Rle_lt_trans with (1 := Rmin_l _ _).
  apply Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  exists ((d-1)) ; repeat split.
  apply Rlt_le, Hfa.
  apply Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
Qed.

Lemma IVT_Rbar_decr (f : R -> R) (a b la lb : Rbar) (y : R) :
  is_lim f a la -> is_lim f b lb
  -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x)
  -> (forall (x y : R), Rbar_lt a x -> x < y -> Rbar_lt y b -> f y < f x)
  -> Rbar_lt a b
  -> Rbar_lt lb y /\ Rbar_lt y la
  -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
  move => Hla Hlb Cf Hf Hab Hy.
  case: (IVT_Rbar_incr (fun x => - f x) a b (Rbar_opp la) (Rbar_opp lb) (-y)).
  by apply is_lim_opp.
  by apply is_lim_opp.
  move => x Hax Hxb.
  by apply continuity_pt_opp, Cf.
  move => x z Hax Hxz Hzb.
  apply Ropp_lt_contravar.
  by apply Hf.
  by apply Hab.
  split ; apply Rbar_opp_lt ;
  rewrite Rbar_opp_involutive /Rbar_opp Ropp_involutive ;
  by apply Hy.
  move => x Hx ; exists x ; intuition.
  by rewrite -(Ropp_involutive y) -H4 Ropp_involutive.
Qed.

(** * 2D-continuity *)

(** ** Definitions *)

Definition continuity_2d_pt f x y :=
  forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.

Lemma uniform_continuity_2d :
  forall f a b c d,
  (forall x y, a <= x <= b -> c <= y <= d -> continuity_2d_pt f x y) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c <= y <= d ->
  a <= u <= b -> c <= v <= d ->
  Rabs (u - x) < delta -> Rabs (v - y) < delta ->
  Rabs (f u v - f x y) < eps.
Proof.
intros f a b c d Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x y Hx Hy => locally_2d_ex_dec (P x y) x y _ (Cf x y Hx Hy _))).
intros delta1.
set (delta2 x y := match Rle_dec a x, Rle_dec x b, Rle_dec c y, Rle_dec y d with
  left Ha, left Hb, left Hc, left Hd => pos_div_2 (projT1 (delta1 x y (conj Ha Hb) (conj Hc Hd))) |
  _, _, _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_2d a b c d delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux Hvy.
specialize (Hdelta x y Hx Hy).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&q&(Hap,Hpb)&(Hcq,Hqd)&Hxp&Hyq&Hd).
replace (f u v - f x y) with (f u v - f p q + (f p q - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hyq Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
case Rle_dec => Hcq' ; try easy.
case Rle_dec => Hqd' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hyq Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
replace (v - q) with (v - y + (y - q)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hyq).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hvy).
apply: Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_trans with (1 := Hyq).
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
destruct (Rlt_dec (Rabs (f u v - f x y)) (pos_div_2 eps)) ; [left|right]; assumption.
Qed.

Lemma uniform_continuity_2d_1d :
  forall f a b c,
  (forall x, a <= x <= b -> continuity_2d_pt f x c) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c - delta <= y <= c + delta ->
  a <= u <= b -> c - delta <= v <= c + delta ->
  Rabs (u - x) < delta ->
  Rabs (f u v - f x y) < eps.
Proof.
intros f a b c Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x Hx => locally_2d_ex_dec (P x c) x c _ (Cf x Hx _))).
intros delta1.
set (delta2 x := match Rle_dec a x, Rle_dec x b with
  left Ha, left Hb => pos_div_2 (projT1 (delta1 x (conj Ha Hb))) |
  _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_1d a b delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux.
specialize (Hdelta x Hx).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&(Hap,Hpb)&Hxp&Hd).
replace (f u v - f x y) with (f u v - f p c + (f p c - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
destruct (Rlt_dec (Rabs (f u v - f x c)) (pos_div_2 eps)); [left|right] ; assumption.
Qed.

Lemma uniform_continuity_2d_1d' :
  forall f a b c,
  (forall x, a <= x <= b -> continuity_2d_pt f c x) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c - delta <= y <= c + delta ->
  a <= u <= b -> c - delta <= v <= c + delta ->
  Rabs (u - x) < delta ->
  Rabs (f v u - f y x) < eps.
Proof.
intros f a b c Cf eps.
assert (T:(forall x : R, a <= x <= b -> continuity_2d_pt (fun x0 y : R => f y x0) x c) ).
intros x Hx e.
destruct (Cf x Hx e) as (d,Hd).
exists d.
intros; now apply Hd.
destruct (uniform_continuity_2d_1d (fun x y => f y x) a b c T eps) as (d,Hd).
exists d; intros.
now apply Hd.
Qed.

Lemma continuity_2d_pt_neq_0 (f : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y -> f x y <> 0
  -> locally_2d (fun u v => f u v <> 0) x y.
Proof.
  wlog: f / (f x y > 0) => [Hw Cf Hf' | Hf Cf _].
    case: (Rlt_le_dec 0 (f x y)) => Hf.
    by apply Hw.
    case: Hf => // Hf.
    apply locally_2d_impl with (fun u v => - f u v <> 0).
    apply locally_2d_forall => u v H.
    contradict H ; by rewrite H Ropp_0.
    apply Hw.
    apply Ropp_lt_cancel ; by rewrite Ropp_involutive Ropp_0.
    move => eps ; case: (Cf eps) => {Cf} delta Cf ; exists delta => u v Hu Hv.
    rewrite /Rminus -Ropp_plus_distr Rabs_Ropp.
    by apply Cf.
    contradict Hf' ; by rewrite -(Ropp_involutive (f _ _)) Hf' Ropp_0.
  case: (Cf (mkposreal _ Hf)) => {Cf} /= delta Cf.
  exists delta => u v Hu Hv.
  move: (Cf u v Hu Hv) ; move/Rabs_lt_between' => {Cf} [Cf _].
  ring_simplify in Cf ; by apply Rgt_not_eq.
Qed.

(** ** Operations *)

(** Identity *)

Lemma continuity_2d_pt_id1 :
  forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

Lemma continuity_2d_pt_id2 :
  forall x y, continuity_2d_pt (fun u v => v) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

(** Constant functions *)

Lemma continuity_2d_pt_const :
  forall x y c, continuity_2d_pt (fun u v => c) x y.
Proof.
  intros x y c eps; exists eps; rewrite Rminus_eq_0 Rabs_R0.
  intros; apply cond_pos.
Qed.

(** *** Extensionality *)

Lemma continuity_pt_ext_loc :
  forall f g x,
  (locally x (fun x => f x = g x)) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf eps Heps.
destruct (Cf eps Heps) as (d,(Hd1,Hd2)).
case: Heq => d0 Heq.
exists (Rmin d d0).
split.
apply Rmin_case.
exact Hd1.
by apply d0.
intros u Hu.
rewrite -2?Heq.
apply Hd2 ; intuition.
apply Rlt_le_trans with (1 := H0), Rmin_l.
rewrite Rminus_eq_0 Rabs_R0 ; by apply d0.
apply Rlt_le_trans with (1 := proj2 Hu), Rmin_r.
Qed.

Lemma continuity_pt_ext :
  forall f g x,
  (forall x, f x = g x) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf eps Heps.
destruct (Cf eps Heps) as (d,(Hd1,Hd2)).
exists d.
split.
exact Hd1.
intros u Hu.
rewrite -2!Heq.
now apply Hd2.
Qed.

Lemma continuity_2d_pt_ext :
  forall f g x y,
  (forall x y, f x y = g x y) ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq Cf eps.
apply: locally_2d_impl (Cf eps).
apply locally_2d_forall => u v.
now rewrite 2!Heq.
Qed.

Lemma continuity_2d_pt_ext_loc :
  forall f g x y,
  locally_2d (fun u v => f u v = g u v) x y ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y H1 H2 eps.
specialize (locally_2d_and _ _ _ _ H1 (H2 eps)).
apply locally_2d_impl.
apply locally_2d_forall.
intros u v (H3,H4).
rewrite <- H3.
apply locally_2d_singleton in H1.
rewrite <- H1.
exact H4.
Qed.

(** *** Composition *)

Lemma continuity_1d_2d_pt_comp :
 forall f g x y,
   continuity_pt f (g x y) ->
   continuity_2d_pt g x y ->
   continuity_2d_pt (fun x y => f (g x y)) x y.
intros f g x y cf cg eps.
destruct (cf eps (cond_pos eps)) as [delta [deltapos Pf]].
destruct (cg (mkposreal _ deltapos)) as [gamma Pg].
exists gamma; intros u v cu cv.
destruct (Req_EM_T (g x y) (g u v)) as [eqg | neqg].
 solve[rewrite eqg Rminus_eq_0 Rabs_R0; apply cond_pos].
apply (Pf (g u v)).
split;[solve[unfold D_x, no_cond; tauto] | ].
apply (Pg u v); assumption.
Qed.

(** *** Additive operators *)

Lemma continuity_2d_pt_opp (f : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt (fun u v => - f u v) x y.
Proof.
  move => Hf eps ;
  case: (Hf eps) => {Hf} delta Hf ;
  exists delta => u v Hu Hv.
  rewrite /Rminus -Ropp_plus_distr Rabs_Ropp.
  by apply Hf.
Qed.

Lemma continuity_2d_pt_plus (f g : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt g x y ->
    continuity_2d_pt (fun u v => f u v + g u v) x y.
Proof.
  intros cf cg eps.
  destruct (cf (pos_div_2 eps)) as [delta1 P1].
  destruct (cg (pos_div_2 eps)) as [delta2 P2].
  assert (m0 : 0 < Rmin delta1 delta2).
    destruct delta1 as [d1 d1p]; destruct delta2 as [d2 d2p].
    simpl in d1p, d2p |- *; apply Rmin_glb_lt; assumption.
  exists (mkposreal _ m0); simpl; intros u v ux vy.
  replace (f u v + g u v - (f x y + g x y)) with
    ((f u v - f x y) + (g u v - g x y)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
  apply Rplus_lt_compat;[apply P1 | apply P2].
   solve[apply Rlt_le_trans with (1 := ux); apply Rmin_l].
  solve[apply Rlt_le_trans with (1 := vy); apply Rmin_l].
 solve[apply Rlt_le_trans with (1 := ux); apply Rmin_r].
solve[apply Rlt_le_trans with (1 := vy); apply Rmin_r].
Qed.

Lemma continuity_2d_pt_minus (f g : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt g x y ->
    continuity_2d_pt (fun u v => f u v - g u v) x y.
Proof.
  move => Cf Cg.
  apply continuity_2d_pt_plus.
  exact: Cf.
  by apply continuity_2d_pt_opp.
Qed.

(** *** Multiplicative operators *)

Lemma continuity_2d_pt_inv (f : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  f x y <> 0 ->
  continuity_2d_pt (fun u v => / f u v) x y.
Proof.
  wlog: f / (f x y > 0) => [Hw Cf Hf | Hf Cf _ eps].
    case: (Rlt_le_dec 0 (f x y)) => Hf'.
    by apply Hw.
    case: Hf' => // Hf'.
    apply continuity_2d_pt_ext_loc with (fun u v => - / - f u v).
    case: (continuity_2d_pt_neq_0 _ _ _ Cf Hf) => delta H.
    exists delta => u v Hu Hv.
    field.
    by apply H.
    apply continuity_2d_pt_opp.
    apply Hw.
    apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
    apply continuity_2d_pt_opp.
    by apply Cf.
    apply Rgt_not_eq, Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
  case: (Cf (pos_div_2 (mkposreal _ Hf))) => /= d0 C0.
  move: (fun u v Hu Hv => proj1 (proj1 (Rabs_lt_between' _ _ _) (C0 u v Hu Hv)))
    => {C0}.
  replace (f x y - f x y / 2) with (f x y / 2) by field ;
  move => C0.
  case: (Cf (mkposreal (eps * (f x y / 2 * f x y)) _)) => [ | {Cf} /= Hd1 d1 Cf].
  apply Rmult_lt_0_compat.
  by apply eps.
  apply Rmult_lt_0_compat.
  apply (is_pos_div_2 (mkposreal _ Hf)).
  by apply Hf.
  have Hd : 0 < Rmin d0 d1.
    apply Rmin_case ; [by apply d0 | by apply d1].
  exists (mkposreal _ Hd) => /= u v Hu Hv.
  replace (/ f u v - / f x y) with (- (f u v - f x y) / (f u v * f x y)).
  rewrite Rabs_div.
  rewrite Rabs_Ropp Rabs_mult.
  apply Rlt_div_l.
  apply Rmult_lt_0_compat.
  apply Rlt_le_trans with (2 := Rle_abs _).
  apply Rlt_trans with (1 := is_pos_div_2 (mkposreal _ Hf)) => /=.
  apply C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
  by apply Rlt_le_trans with (2 := Rle_abs _).
  apply Rlt_le_trans with (eps * (f x y / 2 * f x y)).
  apply Cf ; by apply Rlt_le_trans with (2 := Rmin_r d0 d1).
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  apply Rmult_le_compat.
  by apply Rlt_le, (is_pos_div_2 (mkposreal _ Hf)).
  by apply Rlt_le.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rlt_le, C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
  by apply Rle_abs.
  apply Rgt_not_eq, Rmult_lt_0_compat.
  apply Rlt_trans with (1 := is_pos_div_2 (mkposreal _ Hf)) => /=.
  apply C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
  by [].
  field ; split ; apply Rgt_not_eq.
  by [].
  apply Rlt_trans with (1 := is_pos_div_2 (mkposreal _ Hf)) => /=.
  apply C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
Qed.

Lemma continuity_2d_pt_mult (f g : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt g x y ->
    continuity_2d_pt (fun u v => f u v * g u v) x y.
Proof.
intros cf cg eps.
assert (rabs1_gt0 : forall x, 0 < Rabs x + 1) by
 (intros; apply Rplus_le_lt_0_compat;[apply Rabs_pos | apply Rlt_0_1 ]).
assert (neps0 : forall x, 0 < eps/(4 * (Rabs x + 1))).
 intros; apply Rmult_lt_0_compat;[apply cond_pos | apply Rinv_0_lt_compat].
 apply Rmult_lt_0_compat;[|apply rabs1_gt0] ; apply Rmult_lt_0_compat ; apply Rlt_0_2.
assert (ndf : 0 < eps/(4 * (Rabs (g x y) + 1))) by apply neps0.
assert (ndg : 0 < (Rmin (eps/(4 * (Rabs (f x y) + 1))) ((Rabs (g x y)) + 1))).
 apply Rmin_glb_lt;[apply neps0 |].
 by apply rabs1_gt0.
destruct (cf (mkposreal _ ndf)) as [delta1 P1].
destruct (cg (mkposreal _ ndg)) as [delta2 P2].
assert (m0 : 0 < Rmin delta1 delta2).
 destruct delta1 as [d1 d1p]; destruct delta2 as [d2 d2p].
 simpl in d1p, d2p |- *; apply Rmin_glb_lt; assumption.
exists (mkposreal _ m0); simpl; intros u v ux vy.
replace (f u v * g u v - f x y * g x y) with
   ((f u v - f x y) * g u v + f x y * (g u v - g x y)) by ring.
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_lt_compat.
 rewrite Rabs_mult.
 apply Rle_lt_trans with (Rabs (f u v - f x y) * (2 * (Rabs (g x y) + 1))).
  apply Rmult_le_compat_l;[solve[apply Rabs_pos] | ].
  assert (Rabs (g u v - g x y) < Rabs (g x y) + 1).
   apply Rlt_le_trans with (2 := Rmin_r (eps/(4 * (Rabs (f x y) + 1))) _).
   apply P2; apply Rlt_le_trans with (2 := Rmin_r delta1 _); assumption.
  replace (g u v) with ((g u v - g x y) + g x y) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rle_minus_r ; ring_simplify.
  apply Rle_trans with (1 := Rlt_le _ _ H).
  apply Rplus_le_compat_l.
  apply Rle_minus_l ; ring_simplify.
  by apply Rle_0_1.
  replace (pos (pos_div_2 eps)) with
       (eps/ (4 * (Rabs (g x y) + 1)) * (2 * (Rabs (g x y) + 1)))
       by (simpl; field; 
      apply Rgt_not_eq, (Rplus_le_lt_0_compat _ _ (Rabs_pos _)), Rlt_0_1).
 apply Rmult_lt_compat_r;[apply Rmult_lt_0_compat;[apply Rlt_0_2|apply rabs1_gt0]|].
 apply P1; apply Rlt_le_trans with (2 := Rmin_l _ delta2); assumption.
rewrite Rabs_mult.
destruct (Req_EM_T (Rabs (f x y)) 0) as [fxy0 | fxyn0].
 rewrite fxy0 Rmult_0_l; case (pos_div_2 eps); intros; assumption. 
apply Rlt_trans with (Rabs (f x y) * (eps/(4*(Rabs (f x y) + 1)))).
 apply Rmult_lt_compat_l;[assert (t := Rabs_pos (f x y)) ; apply sym_not_eq in fxyn0 ; by case: t | ].
 apply Rlt_le_trans with (2 := Rmin_l _ (Rabs (g x y) + 1)).
 apply P2; apply Rlt_le_trans with (2 := Rmin_r delta1 _); assumption.
replace (pos (pos_div_2 eps)) with
   ((2 * (Rabs (f x y) + 1)) * (eps / (4 * (Rabs (f x y) + 1))));
  [ | destruct eps; simpl; field; apply Rgt_not_eq, rabs1_gt0].
apply Rmult_lt_compat_r;[apply neps0 | ].
assert (t := Rabs_pos (f x y)).
apply Rminus_lt_0 ; ring_simplify.
apply Rplus_le_lt_0_compat.
by apply Rabs_pos.
by apply Rlt_0_2.
Qed.
