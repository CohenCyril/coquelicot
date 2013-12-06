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

Require Import Reals Div2 ConstructiveEpsilon.
Require Import ssreflect ssrbool eqtype seq.
Require Import Markov Rcomplements Rbar Lub Limit Derive SF_seq.
Require Import Continuity Derive_2d Hierarchy.

(** * Definition of Riemann intagral *)

Section is_RInt.

Context {V} {VV : NormedVectorSpace V R}.

Definition is_RInt (f : R -> V) (a b : R) (If : V) :=
  filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (Riemann_fine a b) (locally If).
Definition ex_RInt (f : R -> V) (a b : R) :=
  exists If : V, is_RInt f a b If.

(** ** Usual properties *)
(** The integral between a and a is null *)

Lemma is_RInt_point :
  forall (f : R -> V) (a : R),
  is_RInt f a a zero.
Proof.
intros f a.
apply filterlim_locally.
move => eps ; exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
rewrite Riemann_sum_zero.
rewrite (scal_zero_r (VV := nvspace_vector)).
by apply ball_center.
by apply ptd_sort.
move: Hl Hh ; rewrite /Rmin /Rmax ;
by case: Rle_dec (Rle_refl a) => _ _ ->.
Qed.

Lemma ex_RInt_point :
  forall (f : R -> V) a,
  ex_RInt f a a.
Proof.
intros f a.
exists zero ; by apply is_RInt_point.
Qed.

(** Swapping bounds *)

Lemma is_RInt_swap :
  forall (f : R -> V) (a b : R) (If : V),
  is_RInt f b a If -> is_RInt f a b (opp If).
Proof.
  unfold is_RInt.
  intros f a b If HIf.
  rewrite -(scal_opp_one (VV := nvspace_vector)) /=.
  apply filterlim_ext with 
    (fun ptd => scal (opp (one : R)) (scal (sign (a - b)) (Riemann_sum f ptd))).
  intros x.
  rewrite scal_assoc.
  apply (f_equal (fun s => scal s _)).
  by rewrite -(Ropp_minus_distr' b a) sign_opp /= Ropp_mult_distr_l_reverse Rmult_1_l.
  unfold Riemann_fine.
  rewrite Rmin_comm Rmax_comm.
  apply filterlim_compose with (1 := HIf).
  apply filterlim_scal.
Qed.

Lemma ex_RInt_swap :
  forall (f : R -> V) (a b : R),
  ex_RInt f a b -> ex_RInt f b a.
Proof.
  intros f a b.
  case => If HIf.
  exists (opp If).
  now apply is_RInt_swap.
Qed.

(** Integrable implies bounded *)

Lemma ex_RInt_ub (f : R -> V) (a b : R) :
  ex_RInt f a b -> exists M : R, forall t : R,
    Rmin a b <= t <= Rmax a b -> norm (f t) <= M.
Proof.
  wlog: a b / (a < b) => [ Hw | Hab ] Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite /Rmin /Rmax ; case: Rle_dec (Req_le _ _ Hab) => // _ _ ;
    rewrite -Hab.
    exists (norm (f a)) => t Ht ; replace t with a.
    exact: Rle_refl.
    apply Rle_antisym ; by case: Ht.
    rewrite Rmin_comm Rmax_comm ;
    apply ex_RInt_swap in Hex ; by apply Hw.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.

  case: Hex => If Hex.
  generalize (proj1 (filterlim_locally_ball_norm _ If) Hex) => {Hex} /= Hex.
  case: (Hex (mkposreal _ Rlt_0_1)) => {Hex} alpha Hex.
  have Hn : 0 <= ((b-a)/alpha).
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Rlt_le, Hab.
    by apply alpha.
  set n := (nfloor _ Hn).
  set ptd := fun (g : R -> R -> R) =>
    SF_seq_f2 g (unif_part a b n) 0.

  assert (forall g, pointed_subdiv (ptd g) ->
    norm (minus (Riemann_sum f (ptd g)) If) < 1).
    move => g Hg ; replace (Riemann_sum f (ptd g))
      with (scal (sign (b - a)) (Riemann_sum f (ptd g))).
  apply Hex.
  apply Rle_lt_trans with ((b-a)/(INR n + 1)).
  clearbody n ; rewrite SF_lx_f2.
  replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
  suff : forall i, (S i < size (unif_part a b n))%nat ->
    nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b-a)/(INR n + 1).
  elim: (unif_part a b n) => [ /= _ | x0].
  apply Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  case => /= [ | x1 s] IH Hnth.
  apply Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  replace (seq_step _)
    with (Rmax (Rabs (x1 - x0)) (seq_step (x1 :: s))) by auto.
  apply Rmax_case_strong => _.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))) Rabs_right.
  exact: Rle_refl.
  apply Rle_ge, Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  apply IH => i Hi ; exact: (Hnth (S i) (lt_n_S _ _ Hi)).
  rewrite size_mkseq => i Hi.
  rewrite ?nth_mkseq ?S_INR ; try apply SSR_leq.
  field ; apply Rgt_not_eq ; by intuition.
  exact: lt_le_weak.
  exact: Hi.
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm ; apply Rlt_div_l.
  by apply alpha.
  rewrite /n /nfloor ; case: nfloor_ex => /= n' Hn'.
  by apply Hn'.
  split.
  apply Hg.
  split.
  clearbody n ; rewrite /Rmin ;
  case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ; field ; apply Rgt_not_eq ;
  by intuition.
  clearbody n ; rewrite /Rmax -nth_last SF_lx_f2.
  replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
  rewrite size_mkseq nth_mkseq ?S_INR // ;
  case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ; field ; apply Rgt_not_eq ;
  by intuition.
  rewrite /sign.
  case: Rle_dec (Rlt_le _ _ (Rgt_minus _ _ Hab)) => // Hab' _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rgt_minus _ _ Hab)) => // {Hab'} _ _.
  by rewrite scal_one.
  move: H => {Hex} Hex.

  assert (exists M, forall g : R -> R -> R,
    pointed_subdiv (ptd g) -> norm (Riemann_sum f (ptd g)) <= M).
    exists (norm If + 1) ; move => g Hg.
    replace (Riemann_sum f (ptd g))
      with (plus (minus (Riemann_sum f (ptd g)) If) If).
    apply Rle_trans with (norm (minus (Riemann_sum f (ptd g)) If) + norm If).
    by generalize (norm_triangle (minus (Riemann_sum f (ptd g)) If) If).
    rewrite Rplus_comm.
    apply Rplus_le_compat_l.
    apply Rlt_le.
    by apply Hex.
    by rewrite /minus -plus_assoc plus_opp_l plus_zero_r.
  clearbody n ; move: H => {Hex} Hex.

  assert (forall i, (S i < size (unif_part a b n))%nat ->
    exists M, forall t,
      nth 0 (unif_part a b n) i <= t <= nth 0 (unif_part a b n) (S i)
      -> norm (f t) <= M).
    move => i ; revert ptd Hex.
    have : sorted Rlt (unif_part a b n).
      apply sorted_nth => j Hj x0.
      rewrite size_mkseq /= in Hj.
      rewrite ?nth_mkseq ?S_INR /= ; try apply SSR_leq.
      apply Rminus_gt ; field_simplify.
      rewrite Rplus_comm Rdiv_1 ; apply Rdiv_lt_0_compat.
      exact: Rgt_minus.
      by intuition.
      apply Rgt_not_eq ; by intuition.
      by intuition.
      by intuition.
    elim: (unif_part a b n) i => [ /= i _ _ Hi | x0].
    by apply lt_n_O in Hi.
    case => [ /= _ i _ _ Hi | x1 s IH].
    by apply lt_S_n, lt_n_O in Hi.
    case => [ | i] Hlt /= Hex Hi.
    assert (exists M, forall t g, x0 <= t <= x1 ->
      pointed_subdiv (SF_seq_f2 g [:: x1 & s] 0) ->
      norm (plus (scal (x1 - x0) (f t)) (Riemann_sum f (SF_seq_f2 g [:: x1 & s] 0))) <= M).
    case: (Hex) => M Hex'.
    exists M ;
    move => t g Ht Hg.
    set g0 := fun x y =>
      match Req_EM_T x x0 with
        | left _ =>  t
        | right _ => g x y
      end.
    replace (plus (scal (x1 - x0) (f t)) (Riemann_sum f (SF_seq_f2 g (x1 :: s) 0)))
      with (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s] 0)).
    apply Hex'.
    case => [ | j] Hj ; rewrite SF_size_f2 /= in Hj ;
    rewrite SF_lx_f2 SF_ly_f2 /=.
    rewrite /g0.
    by case: Req_EM_T (refl_equal x0).
    rewrite (nth_pairmap 0).
    rewrite /g0.
    suff : (nth 0 (x1 :: s) j) <> x0.
    case: Req_EM_T => // _ _.
    move: (Hg j).
    rewrite SF_size_f2 ; rewrite SF_lx_f2 SF_ly_f2 /= (nth_pairmap 0).
    move => Hg' ; by apply Hg', lt_S_n.
    apply SSR_leq ; by intuition.
    apply Rgt_not_eq.
    apply lt_S_n in Hj.
    elim: j Hj => {IH} [ | j IH] Hj.
    by apply Hlt.
    apply Rlt_trans with (nth 0 (x1 :: s) j).
    apply IH ; by intuition.
    apply (sorted_nth Rlt).
    by apply Hlt.
    by intuition.
    apply SSR_leq ; by intuition.
    rewrite SF_cons_f2 /=.
    rewrite Riemann_sum_cons /=.
    apply f_equal2.
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (refl_equal x0).
    case: s Hlt {IH Hex Hex' Hi Hg} => [ | x2 s] Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x1) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (Rgt_not_eq _ _ (proj1 Hlt)).
    elim: s x2 Hlt => [ | x3 s IH] x2 Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x2) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (Rgt_not_eq _ _ (Rlt_trans _ _ _ (proj1 Hlt) (proj1 (proj2 Hlt)))).
    apply IH.
    split.
    by apply Hlt.
    split.
    apply Rlt_trans with x2 ; by apply Hlt.
    by apply Hlt.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
  move: H => {Hex} Hex.
  case: (Hex) => M Hex'.
  exists ((M + norm (Riemann_sum f (SF_seq_f2 (fun x y => x) (x1 :: s) 0))) / abs (x1 - x0)).
  move => t Ht.
  have Hg : pointed_subdiv (SF_seq_f2 (fun x y : R => x) (x1 :: s) 0).
    move => j ; rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 /= => Hj.
    rewrite (nth_pairmap 0).
    split.
    apply Rle_refl.
    apply Rlt_le, (sorted_nth Rlt (x1::s)).
    by apply Hlt.
    by [].
    apply SSR_leq ; by intuition.
  specialize (Hex' _ _ Ht Hg).
  rewrite -(scal_one (f t)).
  simpl one.
  rewrite -(Rinv_l (x1 - x0)).
  2: by apply Rgt_not_eq, Rgt_minus, Hlt.
  rewrite -scal_assoc.
  eapply Rle_trans ; try apply @norm_scal.
  rewrite Rmult_comm.
  simpl abs.
  rewrite Rabs_Rinv.
  2: by apply Rgt_not_eq, Rgt_minus, Hlt.
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat.
  apply Rabs_pos_lt, Rgt_not_eq.
  by apply Rgt_minus, Hlt.
  replace (scal (x1 - x0) (f t))
    with (minus (plus (scal (x1 - x0) (f t))
            (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s) 0)))
            (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s) 0))).
  rewrite /minus.
  apply Rle_trans with (norm (plus (scal (x1 - x0) (f t))
        (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s) 0)))
        + norm (opp (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s) 0)))).
  by generalize (norm_triangle (plus (scal (x1 - x0) (f t))
        (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s) 0)))
     (opp (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s) 0)))).
  rewrite norm_opp.
  apply Rplus_le_compat_r.
  apply Hex'.
  rewrite /minus -plus_assoc plus_opp_r.
  by apply plus_zero_r.
  apply IH.
  by apply Hlt.
  case: Hex => M Hex.
  exists ((M + norm (scal (x1 - x0) (f x0)))) => g Hg.
  set g0 := fun x y =>
      match Req_EM_T x x0 with
        | left _ => x0
        | right _ => g x y
      end.
  have Hg0 : pointed_subdiv (SF_seq_f2 g0 (x0::x1 :: s) 0).
    move => j ; rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 => Hj.
    rewrite nth_behead (nth_pairmap 0) /=.
    case: j Hj => /= [ | j ] Hj.
    rewrite /g0.
    case: Req_EM_T (refl_equal x0) => // _ _.
    split.
    exact: Rle_refl.
    by apply Rlt_le, Hlt.
    suff : (nth 0 (x1 :: s) j) <> x0.
    rewrite /g0 ; case: Req_EM_T => // _ _.
    move: (Hg j).
    rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 /= => {Hg} Hg.
    move: (Hg (lt_S_n _ _ Hj)) ; rewrite (nth_pairmap 0).
    by [].
    apply SSR_leq ; by intuition.
    apply Rgt_not_eq.
    elim: j Hj => {IH} /= [ | j IH] Hj.
    by apply Hlt.
    apply Rlt_trans with (nth 0 (x1 :: s) j).
    apply IH ; by intuition.
    apply (sorted_nth Rlt (x1::s)).
    by apply Hlt.
    by intuition.
    apply SSR_leq ; by intuition.
    replace (Riemann_sum f (SF_seq_f2 g (x1 :: s) 0))
      with (minus (Riemann_sum f (SF_seq_f2 g0 (x0::x1::s) 0)) (scal (x1 - x0) (f x0))).
    apply Rle_trans with (norm (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s] 0))
     + norm (opp (scal (x1 - x0) (f x0)))).
    by generalize (norm_triangle (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s] 0))
      (opp (scal (x1 - x0) (f x0)))).
    rewrite norm_opp.
    apply Rplus_le_compat_r, (Hex _ Hg0).
    rewrite /minus plus_comm SF_cons_f2 /=.
    rewrite Riemann_sum_cons /= plus_assoc.
    replace (Riemann_sum f (SF_seq_f2 g0 (x1 :: s) x0)) with
      (Riemann_sum f (SF_seq_f2 g (x1 :: s) 0)).
    replace (g0 x0 x1) with x0.
    by rewrite plus_opp_l plus_zero_l.
    rewrite /g0 ; case: Req_EM_T (refl_equal x0) => //.
    elim: s x1 Hlt {IH Hex Hg Hg0 Hi} => [ | x2 s IH] x1 Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x1) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    rewrite /g0 ; by case: Req_EM_T (Rgt_not_eq _ _ (proj1 Hlt)).
    apply IH.
    split.
    apply Rlt_trans with x1 ; by apply Hlt.
    by apply Hlt.
    exact: lt_O_Sn.
    exact: lt_O_Sn.
    exact: lt_O_Sn.
    exact: lt_S_n.
  move:H => {Hex} Hex.
  replace b with (last 0 (unif_part a b n)).
  pattern a at 1 ; replace a with (head 0 (unif_part a b n)).
  elim: (unif_part a b n) Hex => /= [ | x0].
  exists (norm (f 0)) => t Ht ;
  rewrite (Rle_antisym t 0) ; by intuition.
  case => /= [ | x1 s] IH Hex.
  exists (norm (f x0)) => t Ht ;
  rewrite (Rle_antisym t x0) ; by intuition.
  case: (Hex _ (lt_n_S _ _ (lt_O_Sn _))) => /= M0 H0.
  case: IH => [ | M IH].
  move => i Hi ; case: (Hex _ (lt_n_S _ _ Hi)) => {Hex} /= M Hex.
  by exists M.
  exists (Rmax M0 M) => t Ht ;
  case: (Rlt_le_dec t x1) => Ht0.
  apply Rle_trans with (2 := RmaxLess1 _ _) ;
  apply H0 ; by intuition.
  apply Rle_trans with (2 := RmaxLess2 _ _) ;
  apply IH ; by intuition.
  simpl ; field ; apply Rgt_not_eq ; by intuition.
  rewrite -nth_last size_mkseq nth_mkseq ?S_INR /=.
  field ; apply Rgt_not_eq, INRp1_pos.
  by [].
Qed.

(** Extensionality *)

Lemma is_RInt_ext :
  forall (f g : R -> V) (a b : R) (l : V),
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  is_RInt f a b l -> is_RInt g a b l.
Proof.
intros f g a b l Heq.
apply filterlim_within_ext.
intros ptd [Hptd [Hhead Hlast]].
apply f_equal.
move: (Rmin a b) (Rmax a b) Heq Hhead Hlast Hptd.
apply SF_seq.SF_cons_ind with (s := ptd)
  => /= [x0 | [x0 y0] s IH] /= a' b' Heq Hhead Hlast Hptd.
reflexivity.
rewrite !Riemann_sum_cons /= ; apply f_equal2.
rewrite Heq.
reflexivity.
rewrite -Hhead -Hlast ; split.
by apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_seq.SF_h s).
by apply (Hptd O (lt_O_Sn _)).
apply (SF_seq.sorted_last (seq.Cons _ (SF_seq.SF_h s) (seq.unzip1 (SF_seq.SF_t s))) O)
  with (x0 := 0).
apply ptd_sort, ptd_cons with (1 := Hptd).
by apply lt_O_Sn.
apply (IH (SF_seq.SF_h s) b').
move => x Hx ; apply Heq ; split.
apply Rle_trans with (SF_seq.SF_h s).
rewrite -Hhead ; by apply (ptd_sort _ Hptd).
by apply Hx.
by apply Hx.
reflexivity.
by apply Hlast.
by apply ptd_cons with (1 := Hptd).
Qed.

Lemma ex_RInt_ext :
  forall (f g : R -> V) (a b : R),
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  ex_RInt f a b -> ex_RInt g a b.
Proof.
intros f g a b Heq [If Hex].
exists If.
revert Hex.
now apply is_RInt_ext.
Qed.

(** ** Constant functions *)

Lemma is_RInt_const :
  forall (a b : R) (v : V),
  is_RInt (fun _ => v) a b (scal (b - a) v).
Proof.
intros a b v.
apply filterlim_within_ext with (fun _ => scal (b - a) v).
2: apply filterlim_const.
intros ptd [_ [Hhead Hlast]].
rewrite Riemann_sum_const.
rewrite Hlast Hhead.
rewrite scal_assoc.
apply (f_equal (fun x => scal x v)).
clear.
unfold sign.
destruct Rle_dec as [H|H].
assert (K := proj2 (Rminus_le_0 a b) H).
rewrite (Rmax_right _ _ K) (Rmin_left _ _ K).
destruct Rle_lt_or_eq_dec as [H'|H'].
apply sym_eq, Rmult_1_l.
rewrite -H'.
apply sym_eq, Rmult_0_l.
assert (K : b <= a).
apply Rnot_lt_le.
contradict H.
apply -> Rminus_le_0.
now apply Rlt_le.
rewrite (Rmax_left _ _ K) (Rmin_right _ _ K).
simpl.
ring.
Qed.

Lemma ex_RInt_const :
  forall (a b : R) (v : V),
  ex_RInt (fun _ => v) a b.
Proof.
intros a b v.
exists (scal (b - a) v).
apply is_RInt_const.
Qed.

(** ** Composition *)

Lemma is_RInt_comp_opp :
  forall (f : R -> V) (a b : R) (l : V),
  is_RInt f (-a) (-b) l ->
  is_RInt (fun y => opp (f (- y))) a b l.
Proof.
intros f a b l Hf.
apply filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) Hf eps) ; clear Hf ; intros [delta Hf].
exists delta.
intros ptd Hstep [Hptd [Hh Hl]].
rewrite Riemann_sum_opp.
rewrite (scal_opp_r (VV := nvspace_vector)) -scal_opp_l /= -sign_opp.
rewrite Ropp_plus_distr.
  set ptd' := (mkSF_seq (-SF_h ptd)
    (seq.map (fun X => (- fst X,- snd X)) (SF_t ptd))).
replace (Riemann_sum (fun x => f (-x)) ptd) with (Riemann_sum f (SF_rev ptd')).
  have H : SF_size ptd = SF_size ptd'.
    rewrite /SF_size /=.
    by rewrite size_map.
  apply Hf.
  clear H ;
  revert ptd' Hstep ;
  apply SF_cons_dec with (s := ptd) => [ x0  s' Hs'| h0 s] ;
  rewrite /seq_step.
  apply cond_pos.
  set s' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h0,-snd h0) s').
  rewrite SF_lx_rcons.
  rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
  rewrite head_rcons.
  rewrite SF_lx_cons.
  revert h0 s' ;
  move: {1 3}(0) ;
  apply SF_cons_ind with (s := s) => {s} [ x1 | h1 s IH] x0 h0 s' Hs' ;
  simpl in Hs'.
  rewrite /= -Ropp_minus_distr' /Rminus -Ropp_plus_distr Ropp_involutive.
  by apply Hs'.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h1,-snd h1) s'').
  rewrite SF_lx_rcons.
  rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
  rewrite head_rcons.
  rewrite pairmap_rcons.
  rewrite foldr_rcons.
  apply: IH => /=.
  replace (Rmax (Rabs (SF_h s - fst h1))
  (foldr Rmax (Rmax (Rabs (- fst h0 - - fst h1)) x0)
     (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s)))))
    with (Rmax (Rabs (fst h1 - fst h0))
        (Rmax (Rabs (SF_h s - fst h1))
           (foldr Rmax x0
              (pairmap (fun x y : R => Rabs (y - x)) (SF_h s)
                 (unzip1 (SF_t s)))))).
  by [].
  rewrite Rmax_assoc (Rmax_comm (Rabs _)) -Rmax_assoc.
  apply f_equal.
  rewrite -(Ropp_minus_distr' (-fst h0)) /Rminus -Ropp_plus_distr Ropp_involutive.
  elim: (pairmap (fun x y : R => Rabs (y + - x)) (SF_h s) (unzip1 (SF_t s)))
    x0 {Hs'} (Rabs (fst h1 + - fst h0)) => [ | x2 t IH] x0 x1 /=.
    by [].
    rewrite Rmax_assoc (Rmax_comm x1) -Rmax_assoc.
    apply f_equal.
    by apply IH.
  split.
  revert ptd' Hptd H ;
  apply SF_cons_ind with (s := ptd) => [ x0 | h0 s IH] s' Hs' H i Hi ;
  rewrite SF_size_rev -H in Hi.
  by apply lt_n_O in Hi.
  rewrite SF_size_cons in Hi.
  apply lt_n_Sm_le in Hi.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h0,-snd h0) s'').
  rewrite SF_size_cons (SF_size_cons (-fst h0,-snd h0) s'') in H.
  apply eq_add_S in H.
  rewrite SF_lx_rcons SF_ly_rcons.
  rewrite ?nth_rcons.
  rewrite ?SF_size_lx ?SF_size_ly ?SF_size_rev -H.
  move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ;
  case: (ssrnat.leq (S i) (S (SF_size s))) => // _.
  apply le_lt_eq_dec in Hi ; case: Hi => [Hi | -> {i}].
  apply lt_le_S in Hi.
  move: (proj2 (SSR_leq _ _) Hi) ;
  case: (ssrnat.leq (S i) (SF_size s)) => // _.
  move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ;
  case: (ssrnat.leq (S (S i)) (S (SF_size s))) => // _.
  apply IH.
  move: Hs' ; apply ptd_cons.
  apply H.
  rewrite SF_size_rev -H.
  intuition.
  have : ~ is_true (ssrnat.leq (S (SF_size s)) (SF_size s)).
    have H0 := lt_n_Sn (SF_size s).
    contradict H0.
    apply SSR_leq in H0.
    by apply le_not_lt.
  case: (ssrnat.leq (S (SF_size s)) (SF_size s)) => // _.
  move: (@eqtype.eq_refl ssrnat.nat_eqType (SF_size s)) ;
  case: (@eqtype.eq_op ssrnat.nat_eqType (SF_size s) (SF_size s)) => // _.
  have : ~ is_true (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))).
    have H0 := lt_n_Sn (SF_size s).
    contradict H0.
    apply SSR_leq in H0.
    by apply le_not_lt, le_S_n.
  case: (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))) => // _.
  move: (@eqtype.eq_refl ssrnat.nat_eqType (S (SF_size s))) ;
  case: (@eqtype.eq_op ssrnat.nat_eqType (S (SF_size s)) (S (SF_size s))) => // _.
  rewrite H SF_lx_rev nth_rev SF_size_lx //=.
  replace (ssrnat.subn (S (SF_size s'')) (S (SF_size s'')))
    with 0%nat by intuition.
  simpl.
  split ; apply Ropp_le_contravar ; apply (Hs' 0%nat) ;
  rewrite SF_size_cons ; by apply lt_O_Sn.
  split.
  rewrite Rmin_opp_Rmax -Hl.
  simpl.
  clear H.
  revert ptd' ;
  move: (0) ;
  apply SF_cons_ind with (s := ptd) => [ h0 | h0 s IH] x0 s'.
  by simpl.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
  rewrite head_rcons.
  by apply IH.
  rewrite Rmax_opp_Rmin -Hh.
  simpl.
  clear H.
  revert ptd' ;
  move: (0) ;
  apply SF_cons_dec with (s := ptd) => [ h0 | h0 s] x0 s'.
  by simpl.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
  rewrite head_rcons.
  rewrite behead_rcons ; [ | rewrite size_rev SF_size_lx ; by apply lt_O_Sn].
  rewrite unzip1_zip.
  by rewrite last_rcons.
  rewrite size_rcons size_behead ?size_rev SF_size_ly SF_size_lx //=.
  revert ptd' ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | h ptd' IH].
  easy.
  rewrite Riemann_sum_cons.
  rewrite (SF_rev_cons (-fst h, -snd h)
    (mkSF_seq (- SF_h ptd') (seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd')))).
  rewrite -IH => {IH}.
  set s := {|
        SF_h := - SF_h ptd';
        SF_t := seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd') |}.
  rewrite Riemann_sum_rcons.
  rewrite SF_lx_rev.
  have H : (forall s x0, last x0 (rev s) = head x0 s).
    move => T s0 x0.
    case: s0 => [ | x1 s0] //=.
    rewrite rev_cons.
    by rewrite last_rcons.
  rewrite H /=.
  rewrite plus_comm.
  apply (f_equal (fun x => plus (scal x _) _)).
  ring.
Qed.

Lemma ex_RInt_comp_opp :
  forall (f : R -> V) (a b : R),
  ex_RInt f (-a) (-b) ->
  ex_RInt (fun y => opp (f (- y))) a b.
Proof.
  intros f a b [l If].
  exists l.
  by apply is_RInt_comp_opp.
Qed.

Lemma is_RInt_comp_lin 
  (f : R -> V) (u v a b : R) (l : V) :
  is_RInt f (u * a + v) (u * b + v) l
    -> is_RInt (fun y => scal u (f (u * y + v))) a b l.
Proof.
  case: (Req_dec u 0) => [-> {u} If | ].
  assert (If' := is_RInt_point f v).
  rewrite ?Rmult_0_l Rplus_0_l in If.
  assert (H := filterlim_locally_unique _ _ _ If If') => {If If'}.
  apply is_RInt_ext with (fun _ => zero).
  move => x _ ; apply sym_eq ;
  by rewrite -(scal_zero_l (VV := nvspace_vector) (f (0 * x + v))) /=.
  apply filterlim_locally ; simpl => eps.
  apply filter_imp with (2 := filter_true) => x Hx.
  rewrite Riemann_sum_const scal_assoc /=.
  rewrite (@scal_zero_r V R _ nvspace_vector (sign (b - a) * (last (SF_h x) (unzip1 (SF_t x)) - SF_h x))).
  by apply H.
  
  wlog: u a b / (u > 0) => [Hw | Hu _].
    case: (Rlt_le_dec 0 u) => Hu.
    by apply Hw.
    case: Hu => // Hu _ If.
    apply is_RInt_ext with (fun y => opp (scal (- u) (f ((- u) * (- y) + v)))).
    move => x _.
    rewrite -(scal_opp_l (VV := nvspace_vector) (- u) (f (- u * - x + v))) /=.
    rewrite Ropp_involutive.
    apply f_equal.
    apply f_equal ; ring.
    apply (is_RInt_comp_opp (fun y => scal (- u) (f (- u * y + v)))).
    apply Hw.
    by apply Ropp_gt_lt_0_contravar.
    by apply Ropp_neq_0_compat, Rlt_not_eq.
    by rewrite ?Rmult_opp_opp.
  wlog: a b l / (a < b) => [Hw | Hab].
    case: (Rlt_le_dec a b) => Hab If.
    by apply Hw.
    case: Hab If => [Hab | -> {b}] If.
    rewrite -(opp_opp l).
    apply is_RInt_swap.
    apply Hw.
    by [].
    by apply is_RInt_swap.
    assert (If' := is_RInt_point f (u * a + v)).
    assert (H := filterlim_locally_unique _ _ _ If If') => {If If'}.
    apply filterlim_locally => eps.
    apply filter_imp with (2 := filter_true) => x _.
    rewrite Rminus_eq_0 sign_0 (scal_zero_l (VV := nvspace_vector)).
    by apply H.
  intros If.
  apply filterlim_locally.
  generalize (proj1 (filterlim_locally _ l) If).
  move => {If} If eps.
  case: (If eps) => {If} alpha If.
  have Ha : 0 < alpha / Rabs u.
    apply Rdiv_lt_0_compat.
    by apply alpha.
    by apply Rabs_pos_lt, Rgt_not_eq.
  exists (mkposreal _ Ha) => /= ptd Hstep [Hptd [Hfirst Hlast]].
  set ptd' := mkSF_seq (u * SF_h ptd + v) (map (fun X => (u * fst X + v,u * snd X + v)) (SF_t ptd)).
  replace (scal (sign (b - a)) (Riemann_sum (fun y : R => scal u (f (u * y + v))) ptd))
  with (scal (sign (u * b + v - (u * a + v))) (Riemann_sum f ptd')).
  apply: If.
  revert ptd' ;
  case: (ptd) Hstep => x0 s Hs /= ;
  rewrite /seq_step /= in Hs |- *.
  elim: s x0 Hs => [ | [x1 y0] s IH] /= x0 Hs.
  by apply alpha.
  apply Rmax_case.
  replace (u * x1 + v - (u * x0 + v)) with (u * (x1 - x0)) by ring.
  rewrite Rabs_mult Rmult_comm ; apply Rlt_div_r.
  by apply Rabs_pos_lt, Rgt_not_eq.
  by apply Rle_lt_trans with (2 := Hs), Rmax_l.
  apply IH.
  by apply Rle_lt_trans with (2 := Hs), Rmax_r.
  split.
  revert ptd' ;
  case: (ptd) Hptd => x0 s Hs /= i Hi ;
  rewrite /SF_size size_map /= in Hi ;
  move: (Hs i) => {Hs} Hs ;
  rewrite /SF_size /= in Hs ;
  move: (Hs Hi) => {Hs} ;
  rewrite /SF_lx /SF_ly /= => Hs.
  elim: s i x0 Hi Hs => /= [ | [x1 y0] s IH] i x0 Hi Hs.
  by apply lt_n_O in Hi.
  case: i Hi Hs => /= [ | i] Hi Hs.
  split ; apply Rplus_le_compat_r ;
  apply Rmult_le_compat_l ;
  try by apply Rlt_le.
  by apply Hs.
  by apply Hs.
  apply IH.
  by apply lt_S_n.
  by apply Hs.
  split.
  rewrite /ptd' /= Hfirst.
  rewrite -Rplus_min_distr_r.
  rewrite -Rmult_min_distr_l.
  reflexivity.
  by apply Rlt_le.
  rewrite -Rplus_max_distr_r.
  rewrite -Rmult_max_distr_l.
  rewrite -Hlast.
  rewrite /ptd' /=.
  elim: (SF_t ptd) (SF_h ptd) => [ | [x1 _] /= s IH] x0 //=.
  by apply Rlt_le.
  apply f_equal2.
  replace (u * b + v - (u * a + v)) with (u * (b - a)) by ring.
  rewrite /sign.
  case: (Rle_dec 0 (b - a)) (proj1 (Rminus_le_0 _ _) (Rlt_le _ _ Hab)) => // H _.
  case: Rle_dec (Rmult_le_pos _ _ (Rlt_le _ _ Hu) H) => // H0 _.
  case: (Rle_lt_or_eq_dec 0 (b - a)) (Rlt_not_eq _ _ (proj1 (Rminus_lt_0 _ _) Hab)) => // _ H1.
  case: Rle_lt_or_eq_dec (sym_not_eq (Rmult_integral_contrapositive_currified _ _ (Rgt_not_eq _ _ Hu) (sym_not_eq H1))) => //.

  revert ptd' ;
  apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] //=.
  set s' := {|
      SF_h := u * SF_h s + v;
      SF_t := [seq (u * fst X + v, u * snd X + v)
                 | X <- SF_t s] |}.
  rewrite Riemann_sum_cons (Riemann_sum_cons _ (u * x0 + v,u * y0 + v) s') /=.
  rewrite IH.
  apply f_equal2 => //=.
  rewrite scal_assoc /=.
  apply f_equal2 => //= ; ring.
Qed.
Lemma ex_RInt_comp_lin (f : R -> V) (u v a b : R) :
  ex_RInt f (u * a + v) (u * b + v)
    -> ex_RInt (fun y => scal u (f (u * y + v))) a b.
Proof.
  case => l Hf.
  exists l.
  by apply is_RInt_comp_lin.
Qed.

(** ** Chasles *)

Lemma is_RInt_Chasles_0 (f : R -> V) (a b c : R) (l1 l2 : V) :
  a < b < c -> is_RInt f a b l1 -> is_RInt f b c l2
  -> is_RInt f a c (plus l1 l2).
Proof.
  intros [Hab Hbc] H1 H2.
  case: (ex_RInt_ub f a b).
  by exists l1.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ M1 HM1.
  case: (ex_RInt_ub f b c).
  by exists l2.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ M2 HM2.

  apply filterlim_locally_ball_norm => eps.
  generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 (pos_div_2 eps))) => {H1} H1.
  generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 (pos_div_2 eps))) => {H2} H2.
  case: H1 => d1 H1.
  case: H2 => d2 H2.
  move: H1 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ H1.
  move: H2 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ H2.

  have Hd3 : 0 < eps / (4 * ((M1 + 1) + (M2 + 1))).
    apply Rdiv_lt_0_compat.
    by apply eps.
    repeat apply Rmult_lt_0_compat.
    by apply Rlt_0_2.
    by apply Rlt_0_2.
    apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
    specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
    apply Rle_trans with (2 := HM1), norm_ge_0.
    specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
    apply Rle_trans with (2 := HM2), norm_ge_0.
  have Hd : 0 < Rmin (Rmin d1 d2) (mkposreal _ Hd3).
    repeat apply Rmin_case.
    by apply d1.
    by apply d2.
    by apply Hd3.
  exists (mkposreal _ Hd) => /= ptd Hstep [Hptd [Hh Hl]].
  move: Hh Hl ; rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => //= _ _ Hh Hl.
  replace (sign _) with (one : R).
  rewrite scal_one.
  rewrite /ball_norm (double_var eps).
  apply Rle_lt_trans
    with (norm (minus (Riemann_sum f ptd)
      (plus (Riemann_sum f (SF_cut_down ptd b))
            (Riemann_sum f (SF_cut_up ptd b))))
      + norm (minus (plus (Riemann_sum f (SF_cut_down ptd b))
                          (Riemann_sum f (SF_cut_up ptd b)))
                    (plus l1 l2))).
  replace (minus (Riemann_sum f ptd) (plus l1 l2))
    with (plus (minus (Riemann_sum f ptd)
     (plus (Riemann_sum f (SF_cut_down ptd b))
        (Riemann_sum f (SF_cut_up ptd b)))) 
  (minus
     (plus (Riemann_sum f (SF_cut_down ptd b))
        (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))).
  by apply @norm_triangle.
  rewrite /minus -plus_assoc.
  apply f_equal.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
  apply Rplus_lt_compat.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hstep.
  generalize (fun H H0 => Riemann_sum_Chasles_0 f (M1 + 1 + (M2 + 1)) b ptd (mkposreal _ Hd3) H H0 Hptd Hstep).
  rewrite /= Hl Hh => H.
  replace (eps / 2) with (2 * (mkposreal _ Hd3) * (M1 + 1 + (M2 + 1))).
  rewrite -norm_opp opp_plus opp_opp plus_comm.
  simpl ; apply H.
  intros x Hx.
  case: (Rle_lt_dec x b) => Hxb.
  apply Rlt_trans with (M1 + 1).
  apply Rle_lt_trans with M1.
  apply HM1 ; split.
  by apply Hx.
  by apply Hxb.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  apply Rminus_lt_0 ; ring_simplify.
  apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
  specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
  apply Rle_trans with (2 := HM2), norm_ge_0.
  apply Rlt_trans with (M2 + 1).
  apply Rle_lt_trans with M2.
  apply HM2 ; split.
  by apply Rlt_le, Hxb.
  by apply Hx.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  apply Rminus_lt_0 ; ring_simplify.
  apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
  specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
  apply Rle_trans with (2 := HM1), norm_ge_0.
  split ; by apply Rlt_le.
  simpl ; field.
  apply Rgt_not_eq.
  apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
  specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
  apply Rle_trans with (2 := HM1), norm_ge_0.
  specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
  apply Rle_trans with (2 := HM2), norm_ge_0.
  apply Rlt_le_trans with (2 := Rmin_l _ _) in Hstep.
  specialize (H1 (SF_cut_down ptd b)).
  specialize (H2 (SF_cut_up ptd b)).
  apply Rle_lt_trans
    with (norm (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1)
         + norm (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
  replace (minus (plus (Riemann_sum f (SF_cut_down ptd b))
        (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))
    with (plus (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1)
           (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
  apply @norm_triangle.   
  replace (sign (b - a)) with (one : R).
  replace (sign (c - b)) with (one : R).
  rewrite 2!scal_one /minus opp_plus -2!plus_assoc.
  apply f_equal.
  rewrite plus_comm -plus_assoc.
  apply f_equal.
  by apply plus_comm.
  by apply sym_eq, sign_0_lt ; apply -> Rminus_lt_0.
  by apply sym_eq, sign_0_lt ; apply -> Rminus_lt_0.
  rewrite (double_var (eps / 2)) ; apply Rplus_lt_compat.
  apply H1.
  apply SF_cut_down_step.
  rewrite /= Hl Hh ; split ; by apply Rlt_le.
  by apply Rlt_le_trans with (1 := Hstep), Rmin_l.
  split.
  apply SF_cut_down_pointed.
  rewrite Hh ; by apply Rlt_le.
  by [].
  split.
  rewrite SF_cut_down_h.
  by apply Hh.
  rewrite Hh ; by apply Rlt_le.
  move: (SF_cut_down_l ptd b) => //=.
  apply H2.
  apply SF_cut_up_step.
  rewrite /= Hl Hh ; split ; by apply Rlt_le.
  by apply Rlt_le_trans with (1 := Hstep), Rmin_r.
  split.
  apply SF_cut_up_pointed.
  rewrite Hh ; by apply Rlt_le.
  by [].
  split.
  by rewrite SF_cut_up_h.
  move: (SF_cut_up_l ptd b) => /= ->.
  by apply Hl.
  rewrite Hl ; by apply Rlt_le.
  by apply sym_eq, sign_0_lt ; apply -> Rminus_lt_0 ; by apply Rlt_trans with b.
Qed.
Lemma ex_RInt_Chasles_0 (f : R -> V) (a b c : R) :
  a <= b <= c -> ex_RInt f a b -> ex_RInt f b c
  -> ex_RInt f a c.
Proof.
  case => Hab Hbc H1 H2.
  case: Hab => [ Hab | -> ] //.
  case: Hbc => [ Hbc | <- ] //.
  case: H1 => [l1 H1] ; case: H2 => [l2 H2].
  exists (plus l1 l2).
  apply is_RInt_Chasles_0 with b ; try assumption.
  by split.
Qed.

Lemma is_RInt_Chasles_1 (f : R -> V) (a b c : R) l1 l2 :
  a < b < c -> is_RInt f a c l1 -> is_RInt f b c l2 -> is_RInt f a b (minus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
apply filterlim_locally_ball_norm => eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => {H1} d1 /= H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => {H2} d2 /= H2.
exists d1 ; simpl ; intros y Hstep [Hptd [Hh Hl]].
assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\
  pointed_subdiv y /\
  SF_h y = Rmin b c /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax b c).
  apply filter_ex.
  exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
  repeat (split => //=).
  by apply H5.
  by apply H6.
case: H => y2 [Hstep2 H].
specialize (H2 y2 (Rlt_le_trans _ _ _ Hstep2 (Rmin_r _ _)) H).
case: H => Hptd2 [Hh2 Hl2].
set y1 := mkSF_seq (SF_h y) (SF_t y ++ SF_t y2).
  move: Hl Hh2 Hh Hl2 H1 H2 ; rewrite /Rmax /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) (Rlt_le _ _ Hbc) => // _ _ ; case: Rle_dec => // _ _.
  case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => // _ _.
  move => Hl Hh2 Hh Hl2 H1 H2.
  rewrite -Hl in Hab, Hbc, H2, Hh2 |-* => {b Hl}.
  rewrite -Hh in H1, Hab |- * => {a Hh}.
  rewrite -Hl2 in Hbc, H2, H1 => {c Hl2}.
assert (seq_step (SF_lx y1) < d1).
  unfold y1 ; move: Hstep Hh2.
  clear -Hstep2.
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hstep Hl.
  rewrite -Hl.
  by apply Rlt_le_trans with (1 := Hstep2), Rmin_l.
  rewrite /SF_lx /seq_step /= in Hstep |- * ;
  move: (Rle_lt_trans _ _ _ (Rmax_r _ _) Hstep) (Rle_lt_trans _ _ _ (Rmax_l _ _) Hstep) => {Hstep} /= H H0.
  apply Rmax_case.
  by [].
  by apply IH.
assert (pointed_subdiv y1 /\ SF_h y1 = SF_h y /\
  last (SF_h y1) (unzip1 (SF_t y1)) = last (SF_h y2) (unzip1 (SF_t y2))).
  split.
  unfold y1 ; move: Hptd Hh2.
  clear -Hptd2.
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hptd Hl.
  rewrite -Hl ; by apply Hptd2.
  case => [ | i] /= Hi.
  by apply (Hptd O (lt_O_Sn _)).
  apply (IH (ptd_cons _ _ Hptd) Hl i (lt_S_n _ _ Hi)).
  unfold y1 ; simpl ; split.
  by [].
  move: Hh2 ; clear ;
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
  by rewrite Hl.
  by apply IH.
specialize (H1 y1 H H0).
move: Hab Hbc Hh2 H1 H2 ; clear ;
set c := last (SF_h y2) (unzip1 (SF_t y2)) ;
set b := last (SF_h y) (unzip1 (SF_t y)) ;
set a := SF_h y => Hab Hbc Hl.
replace (sign (c - a)) with (one : R).
replace (sign (c - b)) with (one : R).
replace (sign (b - a)) with (one : R).
rewrite ?scal_one.
replace (Riemann_sum f y) with (minus (Riemann_sum f y1) (Riemann_sum f y2)).
move => H1 H2.
unfold ball_norm.
replace (minus (minus (Riemann_sum f y1) (Riemann_sum f y2)) (minus l1 l2))
  with (minus (minus (Riemann_sum f y1) l1) (minus (Riemann_sum f y2) l2)).
  rewrite (double_var eps).
  apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
  rewrite -(norm_opp (minus (Riemann_sum f y2) l2)).
  by apply @norm_triangle.
  rewrite /minus 2!opp_plus opp_opp 2!plus_assoc.
  apply (f_equal (fun x => plus x _)).
  rewrite -!plus_assoc.
  apply f_equal.
  by apply plus_comm.
  move: Hl ; unfold y1, b.
  clear.
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
  by rewrite -Hl /minus plus_opp_r.
  rewrite (Riemann_sum_cons _ (x0,y0) {| SF_h := SF_h y; SF_t := SF_t y ++ SF_t y2 |}) /=.
  rewrite Riemann_sum_cons /=.
  rewrite /minus -plus_assoc.
  apply f_equal.
  by apply IH.
  apply sym_eq, sign_0_lt ; by apply -> Rminus_lt_0.
  apply sym_eq, sign_0_lt ; by apply -> Rminus_lt_0.
  apply sym_eq, sign_0_lt ; apply -> Rminus_lt_0.
  by apply Rlt_trans with b.
Qed.
Lemma ex_RInt_Chasles_1 (f : R -> V) (a b c : R) :
  a <= b <= c -> ex_RInt f a c -> ex_RInt f b c -> ex_RInt f a b.
Proof.
  intros [Hab Hbc].
  case: Hab => [ Hab | -> ].
  case: Hbc => [ Hbc | -> //=].
  intros [l1 H1] [l2 H2].
  exists (minus l1 l2).
  by apply is_RInt_Chasles_1 with c.
  intros ; by apply ex_RInt_point.
Qed.

Lemma is_RInt_Chasles_2 (f : R -> V) (a b c : R) l1 l2 :
  a < b < c -> is_RInt f a c l1 -> is_RInt f a b l2 -> is_RInt f b c (minus l1 l2).
Proof.
  intros [Hab Hbc] H1 H2.
  rewrite -(Ropp_involutive a) -(Ropp_involutive b) -(Ropp_involutive c) in H1 H2.
  apply is_RInt_comp_opp, is_RInt_swap in H1.
  apply is_RInt_comp_opp, is_RInt_swap in H2.
  apply Ropp_lt_contravar in Hab.
  apply Ropp_lt_contravar in Hbc.
  generalize (is_RInt_Chasles_1 _ _ _ _ _ _ (conj Hbc Hab) H1 H2).
  clear => H.
  apply is_RInt_comp_opp, is_RInt_swap in H.
  replace (minus l1 l2) with (opp (minus (opp l1) (opp l2))).
  move: H ; apply is_RInt_ext.
  now move => x _ ; rewrite opp_opp Ropp_involutive.
  by rewrite /minus opp_plus 2!opp_opp.
Qed.
Lemma ex_RInt_Chasles_2 (f : R -> V) (a b c : R) :
  a <= b <= c -> ex_RInt f a c -> ex_RInt f a b -> ex_RInt f b c.
Proof.
  intros [Hab Hbc].
  case: Hab => [ Hab | -> //=].
  case: Hbc => [ Hbc | -> ].
  intros [l1 H1] [l2 H2].
  exists (minus l1 l2).
  by apply is_RInt_Chasles_2 with a.
  intros ; by apply ex_RInt_point.
Qed.

Lemma is_RInt_Chasles (f : R -> V) (a b c : R) (l1 l2 : V) :
  is_RInt f a b l1 -> is_RInt f b c l2
  -> is_RInt f a c (plus l1 l2).
Proof.
  wlog: a c l1 l2 / (a <= c) => [Hw | Hac].
    move => H1 H2.
    case: (Rle_lt_dec a c) => Hac.
    by apply Hw.
    rewrite -(opp_opp (plus _ _)) opp_plus plus_comm.
    apply is_RInt_swap.
    apply Hw.
    by apply Rlt_le.
    by apply is_RInt_swap.
    by apply is_RInt_swap.
  case: (Req_dec a b) => [ <- {b} | Hab'] H1.
  - move => H2.
    apply filterlim_locally_ball_norm => /= eps.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
    assert (pointed_subdiv (SF_nil a) /\
      SF_h (SF_nil (T := V) a) = Rmin a a /\
      last (SF_h (SF_nil (T := V) a)) (unzip1 (SF_t (SF_nil (T := V) a))) = Rmax a a).
      split.
      move => i Hi ; by apply lt_n_O in Hi.
      rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl a).
    specialize (H1 (SF_nil a) (cond_pos d1) H) => {H d1}.
    rewrite Rminus_eq_0 sign_0 in H1.
    assert ( H := scal_zero_l (K := R) (Riemann_sum f (SF_nil a))).
    rewrite /ball_norm H /minus plus_zero_l in H1 => {H}.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
    exists d2 => ptd Hstep Hptd.
    apply Rle_lt_trans with (norm (minus (scal (sign (c - a)) (Riemann_sum f ptd)) l2) + norm (opp l1)).
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le, f_equal.
    rewrite /minus opp_plus -plus_assoc.
    by apply f_equal, @plus_comm.
    rewrite (double_var eps) ; apply Rplus_lt_compat.
    by apply H2.
    by apply H1.
  case: (Req_dec b c) => [ <- | Hbc'] H2.
  - apply filterlim_locally_ball_norm => /= eps.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
    assert (pointed_subdiv (SF_nil b) /\
      SF_h (SF_nil (T := V) b) = Rmin b b /\
      last (SF_h (SF_nil (T := V) b)) (unzip1 (SF_t (SF_nil (T := V) b))) = Rmax b b).
      split.
      move => i Hi ; by apply lt_n_O in Hi.
      rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl b).
    specialize (H2 (SF_nil b) (cond_pos d2) H) => {H d2}.
    rewrite Rminus_eq_0 sign_0 in H2.
    assert ( H := scal_zero_l (K := R) (Riemann_sum f (SF_nil a))).
    rewrite /ball_norm H /minus plus_zero_l in H2 => {H}.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
    exists d1 => ptd Hstep Hptd.
    apply Rle_lt_trans with (norm (minus (scal (sign (b - a)) (Riemann_sum f ptd)) l1) + norm (opp l2)).
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le, f_equal.
    by rewrite /minus opp_plus -plus_assoc.
    rewrite (double_var eps) ; apply Rplus_lt_compat.
    by apply H1.
    by apply H2.
  case: (Req_dec a c) => Hac'.
  - rewrite -Hac' in H1 Hbc' H2 Hac |- * => {c Hac'}.
    apply is_RInt_swap in H2.
    apply filterlim_locally_ball_norm => /= eps.
    exists (mkposreal _ Rlt_0_1) => y Hstep Hy.
    rewrite Rminus_eq_0 sign_0.
    assert ( H := scal_zero_l (K := R) (Riemann_sum f y)).
    rewrite /ball_norm H /minus plus_zero_l opp_plus => {H y Hstep Hy}.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
    assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\
      pointed_subdiv y /\
      SF_h y = Rmin a b /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax a b).
      apply filter_ex.
      exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
      repeat (split => //=).
      by apply H5.
      by apply H6.
    case: H => y [Hstep Hy].
    specialize (H1 _ (Rlt_le_trans _ _ _ Hstep (Rmin_l _ _)) Hy).
    specialize (H2 _ (Rlt_le_trans _ _ _ Hstep (Rmin_r _ _)) Hy).
    rewrite (double_var eps).
    rewrite /ball_norm -norm_opp /minus opp_plus opp_opp in H2.
    apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le, f_equal.
    rewrite plus_assoc /minus.
    apply (f_equal (fun x => plus x _)).
    by rewrite plus_comm plus_assoc plus_opp_l plus_zero_l.
  case: (Rle_lt_dec a b) => Hab ; try (case: Hab => //= Hab) ; clear Hab' ;
  case: (Rle_lt_dec b c) => Hbc ; try (case: Hbc => //= Hbc) ; clear Hbc' ;
  try (case: Hac => //= Hac) ; clear Hac'.
  by apply is_RInt_Chasles_0 with b.
  apply is_RInt_swap in H2.
  rewrite -(opp_opp l2).
  by apply is_RInt_Chasles_1 with b.
  apply is_RInt_swap in H1.
  rewrite -(opp_opp l1) plus_comm.
  by apply is_RInt_Chasles_2 with b.
  now contradict Hab ; apply Rle_not_lt, Rlt_le, Rlt_trans with c.
Qed.
Lemma ex_RInt_Chasles (f : R -> V) (a b c : R) :
  ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
  intros [l1 H1] [l2 H2].
  exists (plus l1 l2).
  by apply is_RInt_Chasles with b.
Qed.

(** ** Continuity *)

Lemma continuity_RInt_0 :
  forall (f : R -> V) (a : R) If,
    locally a (fun x => is_RInt f a x (If x))
    -> filterlim If (locally a) (locally (If a)).
Proof.
  move => f a If [d1 /= CIf].
  assert (forall eps : posreal, norm (If a) < eps).
    move => eps.
    generalize (fun Hy => proj1 (filterlim_locally_ball_norm _ _) (CIf a Hy) eps)
      => /= {CIf} CIf.
      assert (Rabs (a + - a) < d1).
        rewrite -/(Rminus _ _) Rminus_eq_0 Rabs_R0.
        by apply d1.
      destruct (CIf H) as [d CIf'].
      assert (exists y : SF_seq,
        seq_step (SF_lx y) < d /\
        pointed_subdiv y /\
        SF_h y = Rmin a a /\ seq.last (SF_h y) (SF_lx y) = Rmax a a).
        apply filter_ex.
        exists d => y Hy Hy'.
        now split.
      case: H0 => {CIf H} ptd [Hstep Hptd].
      specialize (CIf' ptd Hstep Hptd).
      rewrite Rminus_eq_0 sign_0 in CIf'.
      rewrite -norm_opp.
      replace (opp (If a)) with (minus (scal 0 (Riemann_sum f ptd)) (If a)).
      by apply CIf'.
      replace (scal 0 (Riemann_sum f ptd) : V) with (zero : V).
      by rewrite /minus plus_zero_l.
      apply sym_eq ; apply: (scal_zero_l (VV := nvspace_vector)).
  apply filterlim_locally_ball_norm.
  cut (forall eps : posreal, locally a (fun x : R => norm (If x) < eps)).
    move => H0 eps.
    specialize (H (pos_div_2 eps)).
    specialize (H0 (pos_div_2 eps)).
    destruct H0 as [d Hd].
    exists d => /= y Hy.
    apply Rle_lt_trans with (norm (If y) + norm (If a))%R.
    rewrite -(norm_opp (If a)).
    apply @norm_triangle.
    rewrite (double_var eps).
    apply Rplus_lt_compat.
    now apply Hd.
    by apply H.
  clear H.
  move => eps.
  destruct (ex_RInt_ub f (a - d1 / 2) (a + d1 / 2)) as [Mf HMf].
    apply ex_RInt_Chasles with a.
    apply ex_RInt_swap ; eexists ; apply CIf.
    field_simplify (a - d1 / 2 + - a)%R.
    rewrite Rabs_left.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
    apply Ropp_lt_cancel ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
    eexists ; apply CIf.
    field_simplify (a + d1 / 2 + - a)%R.
    rewrite Rabs_pos_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
    apply Rlt_le ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
  assert ((a - d1 / 2) <= (a + d1 / 2)).
    apply Rminus_le_0.
    replace (a + d1 / 2 - (a - d1 / 2))%R with (d1 : R) by field.
    by apply Rlt_le, d1.
  move: HMf ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ HMf.
  assert (0 <= Mf).
    eapply Rle_trans.
    2: apply (HMf (a - d1 / 2)%R) ; split => // ; by apply Rle_refl.
    by apply norm_ge_0.
  generalize (fun y Hy => proj1 (filterlim_locally_ball_norm _ _) (CIf y Hy) (pos_div_2 eps))
    => /= {CIf} CIf.
  assert (0 < Rmin (d1 / 2) (eps / (2 * (Mf + 1)))).
    apply Rmin_case.
    by apply is_pos_div_2.
    apply Rdiv_lt_0_compat.
    by apply eps.
    apply Rmult_lt_0_compat.
    by apply Rlt_0_2.
    apply Rplus_le_lt_0_compat.
    by [].
    by apply Rlt_0_1.
  set (d2 := mkposreal _ H1).
  exists d2 => x /= Hx.
  specialize (CIf x).
  destruct CIf as [d' CIf].
  apply Rlt_trans with (1 := Hx).
  apply Rle_lt_trans with (1 := Rmin_l _ _).
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  assert (exists y0, seq_step (SF_lx y0) < d' /\
      pointed_subdiv y0 /\
      SF_h y0 = Rmin a x /\ seq.last (SF_h y0) (SF_lx y0) = Rmax a x).
    apply filter_ex.
    exists d' => y Hy Hy'.
    now split.
    case: H2 => ptd [Hstep Hptd].
    specialize (CIf ptd Hstep Hptd).
  rewrite -norm_opp.
  replace (opp (If x)) with 
    (minus (minus (scal (sign (x - a)) (Riemann_sum f ptd)) (If x)) (scal (sign (x - a)) (Riemann_sum f ptd))).
  2: rewrite /minus plus_comm plus_assoc plus_opp_l.
  2: by apply plus_zero_l.
  apply Rle_lt_trans with (norm (minus (scal (sign (x - a)) (Riemann_sum f ptd)) (If x))
    + norm (opp (scal (sign (x - a)) (Riemann_sum f ptd))))%R.
  rewrite /minus ; by apply @norm_triangle.
  rewrite norm_opp (double_var eps).
  apply Rplus_lt_le_compat.
  by [].
  apply Rle_trans with (norm (Riemann_sum f ptd)).
  rewrite /sign ; case: Rle_dec => H2.
  case: Rle_lt_or_eq_dec => H3.
  rewrite scal_one ; by right.
  rewrite (scal_zero_l (VV := nvspace_vector)) norm_zero.
  by apply norm_ge_0.
  rewrite (scal_opp_l (VV := nvspace_vector)) scal_one norm_opp ; by right.
  apply Rle_trans with (Riemann_sum (fun _ => Mf) ptd).
  apply Riemann_sum_norm.
  apply Hptd.
  move => t.
  rewrite (proj2 (proj2 Hptd)) (proj1 (proj2 Hptd)) => Ht.
  apply HMf ; split ; eapply Rle_trans ; try apply Ht.
  apply Rmin_case.
  apply Rlt_le, Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rlt_le, Rabs_lt_between'.
  apply Rlt_le_trans with (1 := Hx).
  by apply Rmin_l.
  apply Rmax_case.
  apply Rlt_le, Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rlt_le, Rabs_lt_between'.
  apply Rlt_le_trans with (1 := Hx).
  by apply Rmin_l.
  rewrite Riemann_sum_const.
  rewrite (proj2 (proj2 Hptd)) (proj1 (proj2 Hptd)) /=.
  apply Rle_trans with (Rabs (x + - a) * Mf)%R.
  apply Rmult_le_compat_r.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec => _.
  apply Rle_abs.
  rewrite -Ropp_minus_distr.
  apply Rabs_maj2.
  apply Rle_trans with (Rabs (x + - a) * (Mf + 1))%R.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply Rminus_le_0 ; ring_simplify ; by apply Rle_0_1.
  apply Rle_div_r.
  apply Rlt_le_trans with (1 := Rlt_0_1).
  apply Rminus_le_0 ; by ring_simplify.
  apply Rlt_le, Rlt_le_trans with (1 := Hx).
  apply Rle_trans with (1 := Rmin_r _ _).
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1).
  apply Rminus_le_0 ; by ring_simplify.
Qed.
Lemma continuity_RInt :
  forall (f : R -> V) (a b : R) If,
  ex_RInt f a b ->
    locally b (fun x => is_RInt f a x (If x))
    -> filterlim If (locally b) (locally (If b)).
Proof.
  move => f a b If [Ifa Hab] CIf.
  set (If' := fun x => plus (opp Ifa) (If x)).
  assert (filterlim If' (locally b) (locally (If' b))).
    apply (continuity_RInt_0 f).
    case: CIf => d CIf.
    exists d => y Hy.
    apply is_RInt_Chasles with a.
    by apply is_RInt_swap.
    by apply CIf.
  apply filterlim_locally_ball_norm => eps.
  unfold ball_norm.
  destruct (proj1 (filterlim_locally_ball_norm _ _) H eps) as [d Hd].
  simpl in Hd.
  exists d => y /= Hy.
  replace (minus (If y) (If b)) with (minus (If' y) (If' b)).
  by apply Hd.
  rewrite /If' /minus opp_plus opp_opp.
  rewrite (plus_comm (opp Ifa)) -plus_assoc.
  apply f_equal.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
Qed.

(** ** Operations *)

Lemma is_RInt_scal :
  forall (f : R -> V) (a b : R) (k : R) (If : V),
  is_RInt f a b If ->
  is_RInt (fun y => scal k (f y)) a b (scal k If).
Proof.
intros f a b k If Hf.
apply filterlim_ext with (fun ptd => scal k (scal (sign (b - a)) (Riemann_sum f ptd))).
intros ptd.
rewrite Riemann_sum_scal.
rewrite 2!scal_assoc.
apply (f_equal (fun x => scal x _)).
apply Rmult_comm.
apply filterlim_compose with (1 := Hf).
apply filterlim_scal.
Qed.

Lemma ex_RInt_scal :
  forall (f : R -> V) (a b : R) (k : R),
  ex_RInt f a b ->
  ex_RInt (fun y => scal k (f y)) a b.
Proof.
intros f a b k [If Hf].
exists (scal k If).
now apply is_RInt_scal.
Qed.

Lemma is_RInt_opp :
  forall (f : R -> V) (a b : R) (If : V),
  is_RInt f a b If ->
  is_RInt (fun y => opp (f y)) a b (opp If).
Proof.
intros f a b If Hf.
apply filterlim_ext with (fun ptd => (scal (opp 1) (scal (sign (b - a)) (Riemann_sum f ptd)))).
intros ptd.
rewrite Riemann_sum_opp.
rewrite (scal_opp_one (VV := nvspace_vector)).
apply sym_eq, (scal_opp_r (VV := nvspace_vector)).
apply filterlim_compose with (1 := Hf).
rewrite -(scal_opp_one (VV := nvspace_vector)).
apply filterlim_scal.
Qed.

Lemma ex_RInt_opp :
  forall (f : R -> V) (a b : R),
  ex_RInt f a b ->
  ex_RInt (fun x => opp (f x)) a b.
Proof.
intros f a b [If Hf].
exists (opp If).
now apply is_RInt_opp.
Qed.

Lemma is_RInt_plus :
  forall (f g : R -> V) (a b : R) (If Ig : V),
  is_RInt f a b If ->
  is_RInt g a b Ig ->
  is_RInt (fun y => plus (f y) (g y)) a b (plus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (sign (b - a)) (Riemann_sum g ptd)))).
intros ptd.
rewrite Riemann_sum_plus.
apply sym_eq, @scal_distr_l.
apply filterlim_compose_2 with (1 := Hf) (2 := Hg).
apply filterlim_plus.
Qed.

Lemma ex_RInt_plus :
  forall (f g : R -> V) (a b : R),
  ex_RInt f a b ->
  ex_RInt g a b ->
  ex_RInt (fun y => plus (f y) (g y)) a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
exists (plus If Ig).
now apply is_RInt_plus.
Qed.

Lemma is_RInt_minus :
  forall (f g : R -> V) (a b : R) (If Ig : V),
  is_RInt f a b If ->
  is_RInt g a b Ig ->
  is_RInt (fun y => minus (f y) (g y)) a b (minus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (opp 1) (scal (sign (b - a)) (Riemann_sum g ptd))))).
intros ptd.
rewrite Riemann_sum_minus.
unfold minus.
rewrite (scal_opp_one (VV := nvspace_vector)).
rewrite -scal_opp_r.
apply sym_eq, @scal_distr_l.
eapply filterlim_compose_2 with (1 := Hf).
apply filterlim_compose with (1 := Hg).
apply filterlim_scal.
rewrite (scal_opp_one (VV := nvspace_vector)).
apply filterlim_plus.
Qed.

Lemma ex_RInt_minus :
  forall (f g : R -> V) (a b : R),
  ex_RInt f a b ->
  ex_RInt g a b ->
  ex_RInt (fun y => minus (f y) (g y)) a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
exists (minus If Ig).
now apply is_RInt_minus.
Qed.

End is_RInt.

(** ** Norm *)

Lemma RInt_ge_0 (f : R -> R) (a b : R) (l : R) :
  a <= b -> (forall x, a <= x <= b -> 0 <= f x)
    -> is_RInt f a b l
    -> 0 <= l.
Proof.
  intros Hab Hf HIf.
  apply Ropp_le_cancel ; rewrite Ropp_0.
  apply Rnot_lt_le => He.
  generalize (proj1 (filterlim_locally _ _) HIf (mkposreal _ He)) ;
  case => {HIf} /= [d HIf].
  assert (exists y, seq_step (SF_lx y) < d /\
    pointed_subdiv y /\
    SF_h y = Rmin a b /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax a b).
    apply filter_ex.
    exists d => y Hy Hy'.
    now split.
  case: H => y [Hy Hy'].
  specialize (HIf y Hy Hy') => {Hy}.
  apply Rabs_lt_between in HIf.
  case: HIf => _.
  apply Rle_not_lt.
  apply Rminus_le_0 ; ring_simplify.
  apply Rminus_le_0 in Hab.
  rewrite /sign ; case: Rle_dec => // {Hab} Hab.
  case: Rle_lt_or_eq_dec => /= Ha'.
  rewrite Rmult_1_l.
  eapply Rle_trans.
  2: apply Riemann_sum_norm.
  apply norm_ge_0.
  by apply Hy'.
  move => t /= Ht.
  rewrite Rabs_pos_eq.
  by apply Rle_refl.
  apply Hf.
  move: Ht.
  rewrite (proj2 (proj2 Hy')) (proj1 (proj2 Hy')).
  apply Rminus_le_0 in Hab.
  rewrite /Rmin /Rmax ; by case: Rle_dec.
  rewrite Rmult_0_l.
  by apply Rle_refl.
Qed.

Lemma RInt_norm {V} {VV : NormedVectorSpace V R}
  (f : R -> V) (g : R -> R) (a b : R) (lf : V) (lg : R) :
  a <= b -> (forall x, a <= x <= b -> norm (f x) <= g x)
  -> is_RInt f a b lf -> is_RInt g a b lg
    -> norm lf <= lg.
Proof.
  intros Hab H Hf Hg.
  apply Rbar_finite_le, filterlim_le 
    with (fun ptd : SF_seq => norm (scal (sign (b - a)) (Riemann_sum f ptd)))
      (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum g ptd)).
  3: apply Hg.
  exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
  apply Rminus_le_0 in Hab.
  rewrite /sign ; case: Rle_dec => // {Hab} Hab.
  case: Rle_lt_or_eq_dec => // _.
  rewrite !scal_one.
  apply Riemann_sum_norm.
  by [].
  move => t.
  apply Rminus_le_0 in Hab.
  rewrite Hl Hh /Rmin /Rmax ; case: Rle_dec => // _.
  apply H.
  rewrite /= Rmult_0_l.
  rewrite (scal_zero_l (VV := nvspace_vector)).
  rewrite norm_zero ; by right.
  apply filterlim_compose with (locally lf).
  by apply Hf.
  by apply filterlim_norm.
Qed.

(** * Particular Vector Spaces *)

(** Pairs *)

Lemma is_RInt_fct_extend_fst {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
  (f : R -> U * V) (a b : R) (l : U * V) :
  is_RInt f a b l -> is_RInt (fun t => fst (f t)) a b (fst l).
Proof.
  intros Hf P [eP HP].
  destruct (Hf (fun u : U * V => P (fst u))) as [ef Hf'].
    exists eP => y Hy.
    apply HP.
    apply Hy.
  exists ef => y H1 H2.
  replace (Riemann_sum (fun t : R => fst (f t)) y)
    with (fst (Riemann_sum f y)).
  by apply Hf'.
  clear.
  apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
  by rewrite /Riemann_sum /=.
  by rewrite ?Riemann_sum_cons /= IH.
Qed.  
Lemma is_RInt_fct_extend_snd {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
  (f : R -> U * V) (a b : R) (l : U * V) :
  is_RInt f a b l -> is_RInt (fun t => snd (f t)) a b (snd l).
Proof.
  intros Hf P [eP HP].
  destruct (Hf (fun u : U * V => P (snd u))) as [ef Hf'].
    exists eP => y Hy.
    apply HP.
    apply Hy.
  exists ef => y H1 H2.
  replace (Riemann_sum (fun t : R => snd (f t)) y)
    with (snd (Riemann_sum f y)).
  by apply Hf'.
  clear.
  apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
  by rewrite /Riemann_sum /=.
  by rewrite ?Riemann_sum_cons /= IH.
Qed.

Lemma is_RInt_fct_extend_pair {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
  (f : R -> U * V) (a b : R) lu lv :
  is_RInt (fun t => fst (f t)) a b lu -> 
  is_RInt (fun t => snd (f t)) a b lv 
    -> is_RInt f a b (lu,lv).
Proof.
  move => H1 H2.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) H1 eps) => {H1} ; intros [d1 H1].
  generalize (proj1 (filterlim_locally _ _) H2 eps) => {H2} ; intros [d2 H2].
  simpl in H1, H2.
  exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= ptd Hstep Hptd.
  rewrite (Riemann_sum_pair (VU := nvspace_vector) (VV := nvspace_vector) f ptd) ; simpl.
  split.
  apply H1 => //.
  by apply Rlt_le_trans with (2 := Rmin_l d1 d2).
  apply H2 => //.
  by apply Rlt_le_trans with (2 := Rmin_r d1 d2).
Qed.

Lemma ex_RInt_fct_extend_fst {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
  (f : R -> U * V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun t => fst (f t)) a b.
Proof.
  intros [l Hl].
  exists (fst l).
  by apply is_RInt_fct_extend_fst.
Qed.  
Lemma ex_RInt_fct_extend_snd {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
  (f : R -> U * V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun t => snd (f t)) a b.
Proof.
  intros [l Hl].
  exists (snd l).
  by apply is_RInt_fct_extend_snd.
Qed.

Lemma ex_RInt_fct_extend_pair {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
  (f : R -> U * V) (a b : R) :
  ex_RInt (fun t => fst (f t)) a b -> 
  ex_RInt (fun t => snd (f t)) a b 
    -> ex_RInt f a b.
Proof.
  move => [l1 H1] [l2 H2].
  exists (l1,l2).
  by apply is_RInt_fct_extend_pair.
Qed.

Lemma RInt_fct_extend_pair {U V} {MU : NormedVectorSpace U R} {MV : NormedVectorSpace V R}
   (U_RInt : (R -> U) -> R -> R -> U) (V_RInt : (R -> V) -> R -> R -> V) :
  (forall f a b l, is_RInt f a b l -> U_RInt f a b = l)
  -> (forall f a b l, is_RInt f a b l -> V_RInt f a b = l)
  -> forall f a b l, is_RInt f a b l
    -> (U_RInt (fun t => fst (f t)) a b, V_RInt (fun t => snd (f t)) a b) = l.
Proof.
  intros HU HV f a b l Hf.
  apply injective_projections ; simpl.
  apply HU ; by apply is_RInt_fct_extend_fst.
  apply HV ; by apply is_RInt_fct_extend_snd.
Qed.

(** * The total function [RInt] *)

Definition RInt (f : R -> R) (a b : R) :=
  match Rle_dec a b with
    | left _ => real (Lim_seq (RInt_val f a b))
    | right _ => - real (Lim_seq (RInt_val f b a))
  end.

Lemma RInt_point :
  forall f a, RInt f a a = 0.
Proof.
intros f a.
replace 0 with (Rbar.real (Rbar.Finite 0)) by auto.
rewrite -(Lim_seq_const 0).
rewrite /RInt ; case: Rle_dec (Rle_refl a) => // _ _ ;
apply f_equal, Lim_seq_ext.
intros n.
unfold RInt_val.
rewrite Riemann_sum_zero //.
unfold SF_sorted.
rewrite SF_lx_f2.
by apply unif_part_sort, Rle_refl.
rewrite SF_lx_f2 /=.
elim: (iota 2 n) {2}(1) ; simpl ; intros.
unfold Rdiv ; ring.
by apply H.
Qed.

Lemma RInt_swap :
  forall f a b,
  - RInt f a b = RInt f b a.
Proof.
intros f a b.
destruct (Req_dec a b) as [Hab|Hab].
rewrite Hab.
rewrite RInt_point.
apply Ropp_0.
unfold RInt.
destruct (Rle_dec a b) as [H|H].
destruct (Rle_dec b a) as [H'|H'].
elim Hab.
now apply Rle_antisym.
apply refl_equal.
apply Rnot_le_lt in H.
destruct (Rle_dec b a) as [H'|H'].
apply Ropp_involutive.
elim H'.
now apply Rlt_le.
Qed.

Lemma is_RInt_lim_seq (f : R -> R) (a b : R) :
  forall If : R, is_RInt f a b If -> is_lim_seq (RInt_val f a b) If.
Proof.
  wlog: a b /(a < b) => [Hw | Hab] If Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.

    Focus 2.
    cut (is_lim_seq (RInt_val f b a) (-If)).
      intros H.
      apply is_lim_seq_spec in H.
      apply is_lim_seq_spec.
      move => eps ; case: (H eps) => {H} N H ; exists N => n Hn.
      rewrite RInt_val_swap.
      replace (- RInt_val f b a n - If) with (- (RInt_val f b a n - - If)) by ring.
      rewrite Rabs_Ropp ; by apply H.
    apply Hw.
    exact: Hab.

    now apply @is_RInt_swap.

    assert (forall n, RInt_val f a a n = 0).
      move => n ; by rewrite RInt_val_point.
    rewrite -Hab in Hex |- * => {Hab b}.
    replace If with 0.
    apply is_lim_seq_spec.
    move => eps ; exists O => n _.
    rewrite H.
    rewrite Rminus_0_r Rabs_R0 ; apply eps.
    suff H0 : forall eps : posreal, Rabs If < eps.
    apply Rle_antisym ; apply le_epsilon => e He ;
    set eps := mkposreal e He ; apply Rlt_le.
    rewrite -(Rminus_eq_0 If) ;
    apply Rplus_lt_compat_l, Rle_lt_trans with (Rabs If).
    exact: Rabs_maj2.
    by apply (H0 eps).
    rewrite Rplus_0_l ;
    apply Rle_lt_trans with (Rabs If).
    exact: Rle_abs.
    by apply (H0 eps).
    generalize (proj1 (filterlim_locally _ If) Hex).
    clear Hex.
    intros Hex.
    move => eps ; move: (Hex eps) => {Hex}.
    rewrite Rminus_eq_0 /sign.
    move: (Rle_refl 0) (Rle_not_lt _ _ (Rle_refl 0)).
    case: Rle_dec => // H0 _ ; case: Rle_lt_or_eq_dec => // _ _ {H0}.
    case => alpha Halpha.
    set ptd := @SF_nil R a.
    replace If with (If - 0 * Riemann_sum f ptd) by ring.
    rewrite Rabs_minus_sym.
    apply Halpha.
    by apply alpha.
    split.
    move => i /= Hi.
    by apply lt_n_O in Hi.
    split.
    rewrite /Rmin ; by case: Rle_dec (Rle_refl a).
    rewrite /Rmax ; by case: Rle_dec (Rle_refl a).
(* * Preuve dans la cas a < b *)
  apply is_lim_seq_spec.
  move => eps.
  generalize (proj1 (filterlim_locally _ If) Hex).
  clear Hex.
  intros Hex.
  case: (Hex eps) => {Hex} alpha Hex.
(* ** Trouver N *)
  have HN : 0 <= (b-a)/alpha.
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Rlt_le, Hab.
    by apply alpha.
  set N := (nfloor _ HN).
  exists N => n Hn.
  rewrite -Rabs_Ropp.
  set ptd := SF_seq_f2 (fun x y => (x+y)/2) (unif_part a b n) 0.
(* ** Appliquer Hex *)
  replace (- (RInt_val f a b n - If))
    with (If - sign (b - a) * Riemann_sum f ptd).
  rewrite Rabs_minus_sym.
  apply: Hex.
  apply Rle_lt_trans with ((b-a)/(INR n + 1)).
  suff : forall i, (S i < size (SF_lx ptd))%nat ->
    nth 0 (SF_lx ptd) (S i) - nth 0 (SF_lx ptd) i = (b-a)/(INR n + 1).
  elim: (SF_lx ptd) => /= [ | x0].
  move => _ ; apply Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  case => /=[ | x1 s] IH Hs.
  apply Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  replace (seq_step _) with (Rmax (Rabs (x1 - x0)) (seq_step (x1::s))) by auto.
  rewrite (Hs _ (lt_n_S _ _ (lt_O_Sn _))) Rabs_right.
  apply Rmax_lub.
  by apply Rle_refl.
  apply IH => i Hi.
  by apply (Hs _ (lt_n_S _ _ Hi)).
  apply Rle_ge, Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  rewrite SF_lx_f2.
  replace (head 0%R (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
  rewrite size_mkseq => i Hi ; rewrite !nth_mkseq ?S_INR.
  field ; apply Rgt_not_eq, INRp1_pos.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
  apply Rle_lt_trans with ((b-a)/(INR N + 1)).
  apply Rmult_le_compat_l.
  by apply Rlt_le, Rgt_minus.
  apply Rinv_le_contravar.
  by apply INRp1_pos.
  by apply Rplus_le_compat_r, le_INR.
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm ; apply Rlt_div_l.
  by apply alpha.
  rewrite /N /nfloor ; case: nfloor_ex => N' HN' /=.
  by apply HN'.
  split.
  move => i.
  rewrite SF_size_f2 size_mkseq => Hi ; simpl in Hi.
  rewrite SF_lx_f2 SF_ly_f2.
  replace (head 0 (unif_part a b n) :: behead (unif_part a b n)) with
    (unif_part a b n) by auto.
  rewrite nth_behead (nth_pairmap 0).
  replace (nth 0 (0 :: unif_part a b n) (S i)) with
    (nth 0 (unif_part a b n) i) by auto.
  have : nth 0 (unif_part a b n) i <= nth 0 (unif_part a b n) (S i).
    apply (sorted_nth Rle).
    by apply unif_part_sort, Rlt_le.
    by rewrite size_mkseq.
  move : (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i)) => x y Hxy.
  pattern y at 3 ; replace y with ((y+y)/2) by field.
  pattern x at 1 ; replace x with ((x+x)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  apply SSR_leq ; rewrite size_mkseq ; by intuition.
  split.
  rewrite /Rmin /= ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  field ; apply Rgt_not_eq, INRp1_pos.
  rewrite SF_lx_f2 -nth_last.
  replace (head 0 _ :: behead _) with (unif_part a b n) by auto.
  rewrite size_mkseq nth_mkseq ?S_INR /=.
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  field ; apply Rgt_not_eq, INRp1_pos.
  by [].
  rewrite Ropp_minus_distr'.
  apply f_equal.
  rewrite /sign.
  case: Rle_dec (Rlt_le _ _ (Rgt_minus _ _ Hab)) => // Hab' _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rgt_minus _ _ Hab)) => // _ _.
  rewrite Rmult_1_l.
  by [].
Qed.

(** Correction of RInt *)

Lemma is_RInt_unique (f : R -> R) (a b l : R) :
  is_RInt f a b l -> RInt f a b = l.
Proof.
  wlog : a b l /(a < b) => [Hw | Hab].
    case: (Rlt_le_dec a b) => Hab.
    by apply Hw.
    case: Hab => [Hab | -> {b}] Hf.
    rewrite -RInt_swap.
    rewrite -(Ropp_involutive l).
    apply Ropp_eq_compat.
    apply Hw.
    by apply Hab.
    now apply @is_RInt_swap.
    rewrite RInt_point.
    generalize (proj1 (filterlim_locally _ l) Hf).
    clear Hf.
    intros Hf.
    apply Req_lt_aux => eps.
    rewrite Rminus_0_l Rabs_Ropp.
    case: (Hf eps) => {Hf} alpha Hf.
    set ptd := SF_seq_f2 (fun x y => (x + y) / 2) (unif_part a a O) 0.
    replace l with (l - sign (a - a) * Riemann_sum f ptd).
    rewrite Rabs_minus_sym.
    apply Hf.
    rewrite /seq_step SF_lx_f2 /=.
    replace (a + 1 * (a - a) / (0 + 1) - (a + 0 * (a - a) / (0 + 1))) with 0 by field.
    rewrite Rabs_R0.
    rewrite /Rmax ; case: Rle_dec (Rle_refl 0) => // _ _.
    by apply alpha.
    split.
    rewrite /ptd => i ;
    rewrite SF_size_f2 SF_lx_f2 ;
    move => /= Hi.
    case: i Hi => [ | i] //= Hi.
    split ; apply Req_le ; field.
    by apply lt_S_n, lt_n_0 in Hi.
    split.
    rewrite /ptd /=.
    rewrite /Rmin ; case: Rle_dec (Rle_refl a) => // _ _.
    field.
    rewrite SF_lx_f2 /=.
    rewrite /Rmax ; case: Rle_dec (Rle_refl a) => // _ _.
    field.
    now rewrite Rminus_eq_0 sign_0 Rmult_0_l Rminus_0_r.
  move => Hf.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (is_lim_seq_unique _ l) => //.
  by apply is_RInt_lim_seq.
Qed.

Lemma RInt_correct (f : R -> R) (a b : R) :
  ex_RInt f a b -> is_RInt f a b (RInt f a b).
Proof.
  case => If Hf.
  replace (RInt f a b) with If.
  by [].
  apply sym_eq ; by apply is_RInt_unique.
Qed.

Ltac search_RInt := let l := fresh "l" in
evar (l : R) ;
match goal with
  | |- RInt _ _ _ = ?lu => apply is_RInt_unique ; replace lu with l ; [ | unfold l]
  | |- is_RInt _ _ _ ?lu => replace lu with l ; [ | unfold l]
end.

(** ** Usual rewritings *)

Lemma RInt_ext :
  forall f g a b,
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  RInt f a b = RInt g a b.
Proof.
intros f g a b.
wlog H: a b / a <= b.
intros H Heq.
destruct (Rle_dec a b) as [Hab|Hab].
now apply H.
rewrite -RInt_swap -(RInt_swap g).
rewrite H //.
apply Rlt_le.
now apply Rnot_le_lt.
now rewrite Rmin_comm Rmax_comm.
rewrite Rmin_left // Rmax_right //.
intros Heq.
unfold RInt.
destruct (Rle_dec a b) as [Hab|Hab].
clear H.
2: easy.
apply f_equal, Lim_seq_ext => n.
apply sym_eq, RInt_val_ext.
rewrite /Rmin /Rmax ; by case: Rle_dec.
Qed.

Lemma RInt_const (a b c : R) :
  RInt (fun _ => c) a b = (b - a) * c.
Proof.
apply is_RInt_unique.
apply @is_RInt_const.
Qed.

Lemma RInt_comp_opp (f : R -> R) (a b : R) :
  RInt (fun y => - f (- y)) a b = RInt f (-a) (-b).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
  by rewrite ?RInt_point.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -(RInt_swap _ b) -(RInt_swap _ (-b)).
    rewrite Hw => //.
    by apply Rlt_not_eq.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  case: Rle_dec (Rlt_not_le _ _ (Ropp_lt_contravar _ _ Hab)) => // _ _.
  rewrite -Rbar_opp_real.
  apply f_equal.
  rewrite -Lim_seq_opp.
  apply Lim_seq_ext => n.
  rewrite RInt_val_swap /RInt_val Riemann_sum_opp.
  simpl opp ; apply f_equal.
  rewrite Riemann_sum_map SF_map_f2.
  replace (unif_part (- b) (- a) n) with (map Ropp (unif_part b a n)).
Focus 2.
apply eq_from_nth with 0.
by rewrite size_map !size_mkseq.
rewrite size_map !size_mkseq => i Hi.
rewrite (nth_map 0 0).
rewrite ?(nth_mkseq 0) => //.
field ; rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
by rewrite size_mkseq.
elim: (unif_part b a n) => /= [ | x0 s IH].
rewrite /Riemann_sum /= ; ring.
destruct s as [ | x1 s].
rewrite /Riemann_sum /= ; ring.
rewrite (SF_cons_f2 _ (- x0)).
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /=.
rewrite (SF_cons_f2 _ (x0)).
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /=.
rewrite -IH Ropp_plus_distr.
apply f_equal2.
replace (- ((x0 + x1) / 2)) with ((- x0 + - x1) / 2) by field.
ring.
apply f_equal.
clear.
case: s x0 x1 => [ | x2 s] x0 x1.
by [].
rewrite !(SF_cons_f2 _ (x1)).
2: by apply lt_O_Sn.
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /=.
by [].
Qed.

Lemma RInt_comp_lin (f : R -> R) (u v a b : R) :
  RInt (fun y => u * f (u * y + v)) a b = RInt f (u * a + v) (u * b + v).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
  by rewrite ?RInt_point.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -(RInt_swap _ b) -(RInt_swap _ (u * b + v)).
    rewrite Hw => //.
    by apply Rlt_not_eq.
  case: (Req_dec 0 u) => [<- {u} | Hu].
    ring_simplify (0 * a + v) (0 * b + v).
    rewrite RInt_point.
    rewrite -(RInt_ext (fun _ => 0)).
    rewrite RInt_const ; ring.
    move => x _ ; ring.
  wlog: u v Hu f / (0 < u) => [Hw | {Hu} Hu].
    case: (Rle_lt_dec 0 u) => Hu'.
    case: Hu' => // Hu'.
    by apply Hw.
    replace (u * a + v) with (-((-u) * a + (-v))) by ring.
    replace (u * b + v) with (-((-u) * b + (-v))) by ring.
    rewrite -RInt_comp_opp.
    rewrite -Hw.
    apply RInt_ext => x _.
    ring_simplify (- (- u * x + - v)) ; ring.
    apply Rlt_not_eq, Ropp_lt_cancel ;
    by rewrite Ropp_0 Ropp_involutive.
    apply Ropp_lt_cancel ;
    by rewrite Ropp_0 Ropp_involutive.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  have : (u * a + v) <= (u * b + v).
    by apply Rlt_le, Rplus_lt_compat_r, Rmult_lt_compat_l.
  case: Rle_dec => // _ _.
  apply f_equal.
  apply Lim_seq_ext => n.
  rewrite /RInt_val.
  change scal with Rmult.
  change plus with Rplus.
  change zero with 0.
  replace ((u * b + v - (u * a + v)) / (INR n + 1) * foldr Rplus 0 (SF_val_ly f (u * a + v) (u * b + v) n))
  with ((b - a) / (INR n + 1) * (u * foldr Rplus 0 (SF_val_ly f (u * a + v) (u * b + v) n)))
  by (rewrite /Rdiv ; ring).
  replace (unif_part (u * a + v) (u * b + v) n) with (map (fun x => u * x + v) (unif_part a b n)).
  elim: (unif_part a b n) {1}0 {2}0 => /= [ | x2 s IH] x0 x1.
  by [].
  destruct s as [ | x3 s].
  by [].
  rewrite (SF_cons_f2 _ (u * x2 + v)).
  rewrite SF_cons_f2.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  replace (u * ((x2 + x3) / 2) + v) with ((u * x2 + v + (u * x3 + v)) / 2) by field.
  ring.
  by apply IH.
  by apply lt_O_Sn.
  by apply lt_O_Sn.
apply eq_from_nth with 0.
by rewrite size_map !size_mkseq.
rewrite size_map !size_mkseq => i Hi.
rewrite (nth_map 0 0).
rewrite ?(nth_mkseq 0) => //.
field ; rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
by rewrite size_mkseq.
Qed.

Lemma RInt_Chasles :
  forall f a b c,
  ex_RInt f a b -> ex_RInt f b c ->
  RInt f a b + RInt f b c = RInt f a c.
Proof.
intros f a b c H1 H2.
apply sym_eq, is_RInt_unique.
replace (RInt f a b + RInt f b c)
  with (plus (RInt f a b) (RInt f b c)) by auto.
assert (H := is_RInt_Chasles f a b c (RInt f a b) (RInt f b c)) ;
apply H ; by apply RInt_correct.
Qed.

Lemma RInt_scal :
  forall f l a b,
  RInt (fun x => l * f x) a b = l * RInt f a b.
Proof.
intros f l.
(* *)
assert (forall a b, Lim_seq (RInt_val (fun x : R => l * f x) a b) = Rbar.Rbar_mult (Rbar.Finite l) (Lim_seq (RInt_val f a b))).
intros a b.
rewrite -Lim_seq_scal_l.
apply Lim_seq_ext => n.
unfold RInt_val.
by rewrite (Riemann_sum_scal l).
(* *)
intros a b.
unfold RInt.
have H0 : (forall x, l * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite l) x)).
  case: (Req_dec l 0) => [-> | Hk].
  case => [x | | ] //= ; rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case => [x | | ] //= ; rewrite Rmult_0_r.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.

case Rle_dec => _.
by rewrite H0 H.
rewrite -?Rbar.Rbar_opp_real H0 H.
apply f_equal.
case: (Lim_seq (RInt_val f b a)) => [x | | ] /=.
apply f_equal ; ring.
case: Rle_dec => // H1.
case: Rle_lt_or_eq_dec => H2 //=.
by rewrite Ropp_0.
case: Rle_dec => // H1.
case: Rle_lt_or_eq_dec => H2 //=.
by rewrite Ropp_0.
Qed.

Lemma RInt_opp :
  forall f a b,
  RInt (fun x => - f x) a b = - RInt f a b.
Proof.
intros f a b.
replace (-RInt f a b) with ((-1) * RInt f a b) by ring.
rewrite -RInt_scal.
apply RInt_ext => x _.
ring.
Qed.

Lemma RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
apply is_RInt_unique.
rewrite -> is_RInt_unique with (1 := Hf).
rewrite -> is_RInt_unique with (1 := Hg).
now apply @is_RInt_plus.
Qed.

Lemma RInt_minus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
apply is_RInt_unique.
rewrite -> is_RInt_unique with (1 := Hf).
rewrite -> is_RInt_unique with (1 := Hg).
now apply @is_RInt_minus.
Qed.

(** * Equivalence with standard library *)

Lemma ex_RInt_Reals_aux_1 (f : R -> R) (a b : R) :
  forall pr : Riemann_integrable f a b,
    is_RInt f a b (RiemannInt pr).
Proof.
  wlog: a b / (a < b) => [Hw | Hab].
    case: (total_order_T a b) => [[Hab | <-] | Hab] pr.
    by apply Hw.
    rewrite RiemannInt_P9.
    apply @is_RInt_point.
    move: (RiemannInt_P1 pr) => pr'.
    rewrite (RiemannInt_P8 pr pr').
    apply @is_RInt_swap.
    apply Hw => //.
  rewrite /is_RInt.
  intros pr.
  apply filterlim_locally.
  unfold Riemann_fine.
  rewrite Rmin_left.
  2: now apply Rlt_le.
  rewrite Rmax_right.
  2: now apply Rlt_le.
  rewrite (proj1 (sign_0_lt (b - a))).
  2: now apply Rlt_Rminus.

  cut (forall (phi : StepFun a b) (eps : posreal),
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (unzip1 (SF_t ptd)) = b ->
    Rabs (RiemannInt_SF phi - 1 * Riemann_sum phi ptd) <= eps).

  intros H.
  rewrite /RiemannInt /= -/(Rminus _ _) => eps ; case: RiemannInt_exists => If HIf.
  set eps2 := pos_div_2 eps.
  set eps4 := pos_div_2 eps2.
(* RInt (f-phi) < eps/4 *)
  case: (HIf _ (cond_pos eps4)) => {HIf} N HIf.
  case: (nfloor_ex (/eps4) (Rlt_le _ _ (Rinv_0_lt_compat _ (cond_pos eps4)))) => n Hn.
  move: (HIf (N+n)%nat (le_plus_l _ _)) => {HIf}.
  rewrite /phi_sequence /R_dist ; case: pr => phi [psi pr] ;
  simpl RiemannInt_SF => HIf.
(* RInt psi < eps/4*)
  have H0 : Rabs (RiemannInt_SF psi) < eps4.
    apply Rlt_le_trans with (1 := proj2 pr).
    rewrite -(Rinv_involutive eps4 (Rgt_not_eq _ _ (cond_pos eps4))) /=.
    apply Rle_Rinv.
    apply Rinv_0_lt_compat, eps4.
    intuition.
    apply Rlt_le, Rlt_le_trans with (1 := proj2 Hn).
    apply Rplus_le_compat_r.
    apply le_INR, le_plus_r.
(* Rsum phi < eps/4 and Rsum psi < eps/4 *)
  case: (H phi eps4) => alpha0 Hphi.
  case: (H psi eps4) => {H} alpha1 Hpsi.
  have Halpha : (0 < Rmin alpha0 alpha1).
    apply Rmin_case_strong => _ ; [apply alpha0 | apply alpha1].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd Hstep [Hsort [Ha Hb]].
  rewrite (double_var eps) 1?(double_var (eps/2)) ?Rplus_assoc.
  rewrite Rabs_minus_sym.
  replace (_-_) with (-(RiemannInt_SF phi - If)
    + (RiemannInt_SF phi - Riemann_sum f ptd)) ;
    [ | by ring_simplify].
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_le_compat.
  rewrite Rabs_Ropp ; apply HIf.
  clear HIf ;
  replace (_-_) with ((RiemannInt_SF phi - 1* Riemann_sum phi ptd)
    + (Riemann_sum phi ptd - Riemann_sum f ptd)) ;
    [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Hphi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_l.
  rewrite -Ropp_minus_distr' Rabs_Ropp.
  replace (Riemann_sum f ptd - Riemann_sum phi ptd)
    with (@minus R (@vspace_group R R _ _) (Riemann_sum f ptd) (Riemann_sum phi ptd))
    by (unfold minus ; simpl ; reflexivity).
  rewrite -Riemann_sum_minus.
  have H1 : (forall t : R,
    SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t - phi t) <= psi t).
    move => t Ht.
    apply pr ; move: (Rlt_le _ _ Hab) ; rewrite /Rmin /Rmax ;
    case: Rle_dec => // _ _ ; rewrite -Ha -Hb //.
  apply Rle_trans with (1 := Riemann_sum_norm _ _ _ Hsort H1).
  apply Rle_trans with (1 := Rle_abs _).
  replace (Riemann_sum psi ptd) with
    (-(RiemannInt_SF psi - 1* Riemann_sum psi ptd)
    + RiemannInt_SF psi) ; [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  rewrite Rabs_Ropp ; apply Hpsi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_r.
  apply Rlt_le, H0.

(* forall StepFun *)

  case => phi [lx [ly Hphi]] eps /= ;
  rewrite /RiemannInt_SF /subdivision /subdivision_val ;
  move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  clear pr.
  move: (Rlt_le _ _ Hab) Hphi => {Hab} ;
  elim: lx ly eps a b => [ | lx0 lx IH] ly eps a b Hab.
(* lx = [::] *)
  case ; intuition ; by [].
  case: lx IH ly => [ | lx1 lx] IH ;
  case => [ {IH} | ly0 ly] Had ; try by (case: Had ; intuition ; by []).
(* lx = [:: lx0] *)
  exists eps => ptd Hptd Hstep (*Hsort*) Ha Hb /=.
  rewrite Riemann_sum_zero.
  rewrite Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
  by apply ptd_sort.
  rewrite /SF_lx /= Hb Ha ; case: Had => {Ha Hb} _ [Ha [Hb _]] ; move: Ha Hb ;
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ <- <- //.
(* lx = [:: lx0, lx1 & lx] *)
  set eps2 := pos_div_2 eps ; set eps4 := pos_div_2 eps2.
(* * alpha1 from IH *)
  case: (IH ly eps4 lx1 b) => {IH}.

  replace b with (last 0 (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx)))).
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1%nat)
  with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; apply lt_n_S, lt_O_Sn.
  case: Had => /= _ [_ [Hb _]] ; move: Hb ; rewrite /Rmax ;
  case : Rle_dec => //= _ ;
  elim: (lx) lx1  => //= h s IH _ ; apply IH.
  apply (StepFun_P7 Hab Had).

  move => /= alpha1 IH.
(* * alpha2 from H *)
  cut (forall eps : posreal,
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (SF_lx ptd) = lx1 ->
    Rabs (ly0 * (lx1 - lx0) - Riemann_sum phi ptd) <= eps).

  intros H.
  case: (H eps4) => {H} alpha2 H.
(* * alpha3 from (fmax - fmin) *)
  set fmin1 := foldr Rmin 0 (ly0::Rlist2seq ly).
  set fmin2 := foldr Rmin 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmin := Rmin fmin1 fmin2.
  set fmax1 := foldr Rmax 0 (ly0::Rlist2seq ly).
  set fmax2 := foldr Rmax 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmax := Rmax fmax1 fmax2.

  have Ha3 : (0 < eps4 / (Rmax (fmax - fmin) 1)).
    apply Rdiv_lt_0_compat ; [ apply eps4 | ].
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha3 := mkposreal _ Ha3.
(* * alpha = Rmin (Rmin alpha1 alpha2) alpha3 *)
  have Halpha : (0 < Rmin (Rmin alpha1 alpha2) alpha3).
    apply Rmin_case_strong => _ ; [ | apply alpha3].
    apply Rmin_case_strong => _ ; [ apply alpha1 | apply alpha2].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd Hptd Hstep Ha Hb.

  suff Hff : forall x, a <= x <= b -> fmin <= phi x <= fmax.
  suff Hab1 : forall i, (i <= SF_size ptd)%nat -> a <= nth 0 (SF_lx ptd) i <= b.
  suff Hab0 : a <= lx1 <= b.

  rewrite (SF_Chasles _ _ lx1 (SF_h ptd)) /=.
  replace (_-_) with
    ((ly0 * (lx1 - lx0) - 1* Riemann_sum phi (SF_cut_down' ptd lx1 (SF_h ptd)))
    + (Int_SF ly (RList.cons lx1 lx) - 1* Riemann_sum phi (SF_cut_up' ptd lx1 (SF_h ptd))))
    ; [ | by ring_simplify].

  rewrite (double_var eps) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* partie [lx0;lx1] *)

  set ptd_r_last := (SF_last a (SF_cut_down' ptd lx1 a)).
  set ptd_r_belast := (SF_belast (SF_cut_down' ptd lx1 a)).
  set ptd_r := SF_rcons ptd_r_belast (lx1, (fst (SF_last a ptd_r_belast) + lx1)/2).

  move: (H ptd_r) => {H} H.

  replace (_-_) with ((ly0 * (lx1 - lx0) - Riemann_sum phi ptd_r) +
    (phi ((fst (SF_last 0 ptd_r_belast) + lx1)/2) - phi (snd ptd_r_last))
      * (lx1 - fst (SF_last 0 ptd_r_belast))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* * appliquer H *)
  apply: H => {IH}.

  Focus 3.
    rewrite -Ha /ptd_r /ptd_r_belast.
    move: (proj1 Hab0) ; rewrite -Ha.
    apply SF_cons_dec with (s := ptd) => [x0 | [x0 y0] s] //= Hx0 ;
    by case: Rle_dec.
  Focus 3.
    revert ptd_r_belast ptd_r ; move: (proj1 Hab0) ;
    rewrite -Ha ;
    apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH]
    //= Hx0 ; case: Rle_dec => //= _.
    by rewrite unzip1_rcons /= last_rcons.

(* ** ptd_r est une subdivision pointée *)

  revert ptd_r_belast ptd_r Hptd ;
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH ] Hptd.
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.

  case => /= [ _ | i Hi] .
  case: Rle_dec => //= Hx0.
  pattern lx1 at 3 ; replace lx1 with ((lx1 + lx1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  split ; apply Req_le ; by field.
  contradict Hi ; apply le_not_lt.
  case: Rle_dec => //= Hx0 ; rewrite /SF_size /= ;
  apply le_n_S, le_O_n.

  move: (IH (ptd_cons _ _ Hptd)) => {IH} IH.
  case => [ _ | i Hi].
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: Rle_dec => //= Hx0.
  case: Rle_dec => //= Hx1.
  move: Hptd Hx1 ; apply SF_cons_dec with (s := s)
    => {s IH} /= [x1 | [x1 y1] s] //= Hptd Hx1.
  by apply (Hptd O (lt_O_Sn _)).
  case: Rle_dec => //= Hx2.
  by apply (Hptd O (lt_O_Sn _)).
  by apply (Hptd O (lt_O_Sn _)).
  pattern lx1 at 3 ; replace lx1 with ((lx1 + lx1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  split ; apply Req_le ; by field.
  move: Hi (IH i) => {IH}.
  rewrite ?SF_size_rcons -?SF_size_lx ?SF_lx_rcons ?SF_ly_rcons.
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -?unzip1_fst.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: (Rle_dec x0 lx1) => //= Hx0.
  case: (Rle_dec (SF_h s) lx1) => //= Hx1.
  rewrite size_belast size_belast'.
  move: Hx1 ;
  apply SF_cons_dec with (s := s) => {s Hptd} /= [ x1 | [x1 y1] s] //= Hx1.
  move => Hi IH ; apply IH ; by apply lt_S_n.
  case: Rle_dec => //= Hx2.

  move => Hi IH ; apply IH ; by apply lt_S_n.

  move => Hi IH ; apply IH ; by apply lt_S_n.

  move => Hi ; by apply lt_S_n, lt_n_O in Hi.
  move => Hi ; by apply lt_S_n, lt_n_O in Hi.

  apply Rlt_le_trans with (2 := Rmin_r alpha1 alpha2) ;
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep) => {Hstep}.
  move: Hab0 ; rewrite -Ha -Hb ;
  revert ptd_r_belast ptd_r => {Hab1} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //= Hab0.
  rewrite /SF_lx /SF_rcons /SF_belast /SF_last /SF_cut_down' /=.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) /seq_step /=.
  rewrite Rminus_eq_0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  move: Hab0 (fun Hx1 => IH (conj Hx1 (proj2 Hab0))) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hab0 IH.
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: Rle_dec => //= Hx1.
  rewrite /seq_step /=.
  apply Rle_max_compat_l.
  rewrite (Rle_antisym _ _ Hx1 (proj2 Hab0)) Rminus_eq_0 Rabs_R0.
  apply Rmax_case_strong ; by intuition.
  rewrite /seq_step /=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  apply Rplus_le_compat_r.
  by apply Rlt_le, Rnot_le_lt.
  apply Rle_ge ; rewrite -Rminus_le_0 ; by apply Hab0.
  move: IH ; rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: (Rle_dec x1 lx1) => //= Hx1 IH.
  move: (IH Hx1) => {IH}.
  case: (Rle_dec (SF_h s) lx1) => //= Hx2.
  rewrite /seq_step -?(last_map (@fst R R)) /= => IH ;
  apply Rle_max_compat_l, IH.
  rewrite /seq_step /= ; apply Rle_max_compat_l.
  rewrite /seq_step /= ; apply Rmax_le_compat.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
  apply Rle_ge ; rewrite -Rminus_le_0 ; apply Hab0.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  apply SF_cons_ind with (s := s) => {s IH Hab0} /= [x2 | [x2 y2] s IH] //=.
  exact: Rle_refl.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  exact: IH.
(* ** transition 1 *)
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (fst (SF_last 0 ptd_r_belast) + lx1) / 2 <= b.
  suff H1 : a <= snd ptd_r_last <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_r_last Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  replace a with ((a+a)/2) by field.
  replace b with ((b+b)/2) by field.
  split ; apply Rmult_le_compat_r, Rplus_le_compat ; try by intuition.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.

  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite Rabs_right.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_r_belast ptd_r Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /SF_cut_down' /SF_belast /SF_last /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) ; apply Req_le ; by ring.
  move => Hptd Hab0 ;
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  rewrite /SF_cut_down' /SF_belast /SF_last /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx3.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.

  apply Rle_ge ; rewrite -Rminus_le_0.
  revert ptd_r_belast ptd_r ; rewrite -Ha in Hab0 ; move: (proj1 Hab0) ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down' /SF_belast /SF_last /=.
  by case: Rle_dec.
  move: IH ; rewrite /SF_cut_down' /SF_belast /SF_last /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= Hx1 IH.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //=.
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] //= Hx2.
  case: (Rle_dec (SF_h s) _) => //=.

  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.

  clear H IH.
  rewrite Rplus_assoc Rmult_1_l.
  apply (f_equal (Rplus (ly0 * (lx1 - lx0)))).
  rewrite -(Ropp_involutive (-_+_)).
  apply Ropp_eq_compat.
  rewrite Ropp_plus_distr Ropp_involutive.
  revert ptd_r_last ptd_r_belast ptd_r ; move: (proj1 Hab0) ;
  rewrite -Ha => {Hab0} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down' /=.
  case: (Rle_dec x0 lx1) => //= _.
  rewrite /Riemann_sum  /=.
  by ring.
  
  case: (Rle_dec (SF_h s) lx1) => //= Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} [x1 | [x1 y1] s] /= Hx1.
  rewrite /SF_cut_down' /= ;
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _.
  rewrite /Riemann_sum /= => _.
  ring.
  rewrite /SF_cut_down' /= ;
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _ ;
  case: (Rle_dec (SF_h s) _) => //= Hx2.
  rewrite /SF_belast /SF_last /SF_rcons /=.
  rewrite (Riemann_sum_cons phi (x0,y0) ({| SF_h := x1; SF_t := (SF_h s, y1) :: seq_cut_down' (SF_t s) lx1 y1 |})).
  rewrite (Riemann_sum_cons phi (x0,y0) ({|
  SF_h := x1;
  SF_t := rcons (seq.belast (SF_h s, y1) (seq_cut_down' (SF_t s) lx1 y1))
               (lx1,
               (fst
                  (last (x1, y0)
                     (seq.belast (SF_h s, y1) (seq_cut_down' (SF_t s) lx1 y1))) +
                lx1) / 2) |})).
  move => <- /=.
  rewrite Rplus_assoc ;
  apply f_equal.
  rewrite -!(last_map (@fst R R)) -!unzip1_fst /=.
  ring.
  rewrite /Riemann_sum /= => _ ; ring.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= _ ; case: Rle_dec => //= _.
  rewrite /Riemann_sum /= ; ring.

(* partie [lx1 ; b] *)

  set ptd_l_head := (SF_head a (SF_cut_up' ptd lx1 a)).
  set ptd_l_behead := (SF_behead (SF_cut_up' ptd lx1 a)).
  set ptd_l := SF_cons (lx1, (lx1 + fst (SF_head a ptd_l_behead))/2) ptd_l_behead.

  move: (IH ptd_l) => {IH} IH.

  replace (_-_) with ((Int_SF ly (RList.cons lx1 lx) - 1 * Riemann_sum phi ptd_l) -
    (phi ((lx1 + fst (SF_head 0 ptd_l_behead))/2) - phi (snd ptd_l_head))
      * (lx1 - fst (SF_head 0 ptd_l_behead))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
(* * hypothèse d'induction *)
  apply: IH.
(* ** ptd_l est une subdivision pointée *)
  case.
  move => _ ; move: (proj1 Hab0) ; rewrite -Ha => /= Hx0 ;
  case: Rle_dec => //= _.
  rewrite seq_cut_up_head'.
  move: Hx0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  split ; apply Req_le ; field.
  case: Rle_dec => //= Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: Rle_dec => //= Hx2.
  pattern (SF_h s) at 3 ; replace (SF_h s) with ((SF_h s+SF_h s)/2) by field.
  pattern lx1 at 1 ; replace lx1 with ((lx1+lx1)/2) by field.
  apply Rnot_le_lt, Rlt_le in Hx1 ; split ;
  apply Rmult_le_compat_r ; by intuition.
  rewrite /ptd_l SF_lx_cons SF_ly_cons SF_size_cons => i Hi ;
  move: i {Hi} (lt_S_n _ _ Hi).
  revert ptd_l_behead ptd_l Hptd ;
  apply SF_cons_ind with (s := ptd)
    => /= [x0 | [x0 y0] s IH] /= Hptd.
  rewrite /SF_cut_up' /=.
  case: Rle_dec => //=.
  rewrite /SF_size /SF_behead /= => _ i Hi ; by apply lt_n_O in Hi.
  move: (IH (ptd_cons _ _ Hptd)) => {IH}.
  rewrite /SF_cut_up' /=.
  case: (Rle_dec x0 _) => //= Hx0.
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  rewrite !seq_cut_up_head'.
  move: Hx1 ; apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //= Hx2.
  
(* * seq_step (SF_lx ptd_l) < alpha1 *)
  apply Rlt_le_trans with (2 := Rmin_l alpha1 alpha2).
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep).
  revert ptd_l_behead ptd_l ; move :(proj1 Hab0) ;
  rewrite -Ha ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] /= s IH] Hx0.
  rewrite /SF_cut_up' /= ; case: (Rle_dec x0 _) => //= _.
  rewrite /seq_step /= Rminus_eq_0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  rewrite /SF_cut_up' /= ; case: (Rle_dec x0 _) => //= _.
  move: IH ; rewrite /SF_cut_up' /= ; case: (Rle_dec (SF_h s) _) => //= Hx1 ;
  rewrite ?seq_cut_up_head' => IH.
  move: Hx1 (IH Hx1) => {IH} ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx1 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ;
  exact: RmaxLess2.
  move: IH ; case: (Rle_dec (SF_h s) _) => //= Hx2 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ;
  exact: RmaxLess2.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ;
  exact: RmaxLess2.
  clear IH ; rewrite /seq_step /=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_l, Ropp_le_contravar.
  by apply Rle_ge, (Rminus_le_0 lx1 _), Rlt_le, Rnot_le_lt.
  by rewrite /ptd_l /=.
  rewrite -Hb.
  move: (proj1 Hab0) ; rewrite -Ha /=;
  case: (Rle_dec (SF_h ptd) lx1) => //= _ _.
  rewrite seq_cut_up_head'.
  move: Hab0 ; rewrite -Ha -Hb ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= [Hx0 Hlx1].
  by apply Rle_antisym.
  move: (fun Hx1 => IH (conj Hx1 Hlx1)) => {IH} ;
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  move => IH ; rewrite -(IH Hx1) => {IH}.
  move: Hx1 Hlx1 ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s ] Hx1 Hlx1.
  by [].
  case: (Rle_dec (SF_h s) _) => /= Hx2 ;
  by [].
(* ** transition 2 *)
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_Ropp Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (lx1 + fst (SF_head 0 ptd_l_behead)) / 2 <= b.
  suff H1 : a <= snd ptd_l_head <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_l_head Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_up' /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up' /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_up' /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  replace a with ((a+a)/2) by field.
  replace b with ((b+b)/2) by field.
  split ; apply Rmult_le_compat_r, Rplus_le_compat ; try by intuition.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up' /SF_head /= -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite ?seq_cut_up_head'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite !seq_cut_up_head'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.

  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite -Rabs_Ropp Rabs_right ?Ropp_minus_distr'.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_l_behead ptd_l Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  apply Req_le ; by ring.
  move => Hptd Hab0 ;
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  rewrite !seq_cut_up_head' in IH |-*.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar, Hab0.

  apply Rle_ge, (Rminus_le_0 lx1).
  revert ptd_l_behead ptd_l ; rewrite -Ha -Hb in Hab0 ; move: Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  case: Rle_dec => /= _.
  exact: Rle_refl.
  exact: (proj2 Hx0).
  move: (proj1 Hx0) ; case: Rle_dec => //= _ _.
  move: (fun Hx1 => IH (conj Hx1 (proj2 Hx0))) => {IH}.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  rewrite !seq_cut_up_head' in IH |-* ; move: (IH Hx1) => {IH}.
  move: Hx0 Hx1 ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx0 Hx1 IH.
  exact: Rle_refl.
  move: IH ; case: (Rle_dec (SF_h s)) => /= Hx2.
  by [].
  by [].
  by apply Rlt_le, Rnot_le_lt, Hx1.

  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.

  clear H IH.
  rewrite !Rmult_1_l {1 2}/Rminus Rplus_assoc -Ropp_plus_distr.
  apply (f_equal (Rminus _)) => /=.
  rewrite /ptd_l /ptd_l_behead /ptd_l_head /= /SF_cut_up' /= ;
  move: Hab0 ; rewrite -Ha -Hb /= ;
  case => [Hx0 Hlx1].
  case: (Rle_dec (SF_h ptd)) => //= _.
  rewrite ?seq_cut_up_head' /SF_ly /= Riemann_sum_cons /=.
  move: Hx0 Hlx1 ; apply SF_cons_ind with (s := ptd)
    => [x0 | [x0 y0] s /= IH] /= Hx0 Hlx1.
  rewrite /Riemann_sum /= ; ring.
  case: (Rle_dec (SF_h s)) => //= Hx1.
  move: (IH Hx1 Hlx1) => /= {IH}.
  move: Hx1 Hlx1 ; apply SF_cons_dec with (s := s)
    => {s} [x1 | [x1 y1] s /=] /= Hx1 Hlx1 IH.
  rewrite /Riemann_sum /= ; ring.
  move: IH ; case: (Rle_dec (SF_h s)) => //= Hx2.
  move => <- ; apply Rminus_diag_uniq ; ring_simplify.
  move: Hx2 Hlx1 y1 ; apply SF_cons_ind with (s := s)
    => {s} [x2 | [x2 y2] s /= IH] /= Hx2 Hlx1 y1.
  ring.
  case: (Rle_dec (SF_h s)) => //= Hx3.
  by apply IH.
  ring.
  ring_simplify.
  unfold Riemann_sum ; simpl.
  ring_simplify ; repeat apply f_equal.
  by elim: (SF_t s) (0) (y0).
  
  replace (fst (last (SF_h ptd, SF_h ptd) (SF_t ptd)))
    with (last (SF_h ptd) (unzip1 (SF_t ptd))).
Focus 2.
pattern (SF_h ptd) at 1.
replace (SF_h ptd) with (fst (SF_h ptd, SF_h ptd)) by auto.
elim: (SF_t ptd) (SF_h ptd, SF_h ptd) => //=.
  by rewrite Hb Ha.

  replace lx1 with (pos_Rl (RList.cons lx0 (RList.cons lx1 lx)) 1) by reflexivity.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ;
  case: Rle_dec => // _ <- <-.
  rewrite -(seq2Rlist_bij (RList.cons lx0 _)) !nth_compat size_compat.
  split.
  rewrite nth0.
  apply (sorted_head (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.
  simpl ; rewrite -last_nth.
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1) with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.

  rewrite -Ha -Hb /SF_lx /= => i Hi.
  apply le_lt_n_Sm in Hi ; rewrite -SF_size_lx /SF_lx in Hi.
  split.
  exact: (sorted_head (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).
  exact: (sorted_last (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).

  clear H IH.
  move => x Hx ; case: (sorted_dec ([:: lx0, lx1 & Rlist2seq lx]) 0 x).
  apply sorted_compat ; rewrite /= seq2Rlist_bij ; apply Had.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ;
  case: Rle_dec => // _.
  rewrite -nth0 -nth_last /= => -> Hb'.
  split.
  by apply Hx.
  elim: (lx) (lx1) Hb' => /= [ | h1 s IH] h0 Hb'.
  rewrite Hb' ; by apply Hx.
  by apply IH.
  case => i ; case ; case ; case => {Hx} Hx Hx' Hi.
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (S i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ;
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  have : (((size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat) <
    size [:: lx0, lx1 & Rlist2seq lx])%nat.
    by [].
  replace (size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat with
    (S (size [:: lx0, lx1 & Rlist2seq lx] - 2)) by (simpl ; intuition).
  move: (size [:: lx0, lx1 & Rlist2seq lx] - 2)%nat => i Hi.
  case ; case => {Hx} Hx ; [ case => Hx' | move => _ ].
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ;
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite Hx'.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] (S i)) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: s IH Hi => /= [ | h1 s] IH Hi.
  by apply lt_S_n, lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ;
  [ apply Rle_trans with (1 := Rmin_r _ _) ; exact: Rmin_l
  | apply Rle_trans with (2 := RmaxLess2 _ _) ; exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.

(* preuve de H *)
  clear eps eps2 IH eps4 alpha1.
  move: (proj1 (proj2 Had)) => /= ; rewrite /Rmin ;
    case: Rle_dec => //= _ <-.
  move: (proj1 Had O (lt_O_Sn _)) => /= Hl0l1.
  move: (proj2 (proj2 (proj2 (proj2 Had))) O (lt_O_Sn _)) => /= Hval.
  clear a b Hab Had lx ly.
  rename lx0 into a ; rename lx1 into b ;
  rename ly0 into c ; rename Hl0l1 into Hab.

  set fmin := Rmin (Rmin (phi a) (phi b)) c.
  set fmax := Rmax (Rmax (phi a) (phi b)) c.

  move => eps ; set eps2 := pos_div_2 eps.
  have Halpha : 0 < eps2 / (Rmax (fmax - fmin) 1).
    apply Rdiv_lt_0_compat.
    apply eps2.
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd.
  apply SF_cons_ind with (s := ptd)
    => {ptd} [x0 | [x0 y0] ptd IH] Hptd Hstep Ha Hb ; simpl in Ha, Hb.
  rewrite -Ha -Hb /Riemann_sum  /= ;
  rewrite Rminus_eq_0 Rmult_0_r Rminus_0_r Rabs_R0.
  by apply Rlt_le, eps.
  move: (fun Ha => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep) Ha Hb)
    => {IH} IH.
  move: (proj1 (ptd_sort _ Hptd)) ;
  rewrite Ha in Hptd, Hstep |- * => {x0 Ha} ;
  case => /= Ha.
  rewrite Riemann_sum_cons /= => {IH}.
  replace (_-_) with ((c-phi y0) * (SF_h ptd - a)
    + (c * (b - SF_h ptd) - Riemann_sum phi ptd))
    by ring.
  rewrite (double_var eps) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq_0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ;
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  rewrite -Hb ;
  apply (sorted_last (SF_lx ptd) 0 (proj2 (ptd_sort _ Hptd)) (lt_O_Sn _))
    with (x0 := 0).
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ;
  rewrite /seq_step /= ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.

  move: (ptd_cons _ _ Hptd)
  (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep : seq_step (SF_lx ptd) < alpha)
  Ha Hb => {Hptd Hstep y0} Hptd Hstep Ha Hb.
  suff : SF_h ptd <= b.
  case => Hx0.
  move: Hptd Hstep Ha Hb Hx0.
  apply SF_cons_ind with (s := ptd) => {ptd}
    [x0 | [x0 y0] ptd IH] Hptd Hstep /= Ha Hb Hx0.
  contradict Hb ; apply Rlt_not_eq, Hx0.
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep)
    (Rlt_le_trans _ _ _ Ha (proj1 (ptd_sort _ Hptd))) Hb Hx1) => {IH} IH.
  rewrite Riemann_sum_cons /=.
  have : SF_h ptd <= b.
    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
    apply lt_O_Sn.
  case => Hx1.
  rewrite Hval.
  replace (_-_) with (c * (b - SF_h ptd) - Riemann_sum phi ptd)
  by (ring).
  by apply IH.
  split.
  apply Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_lt_trans with (2 := Hx1), (Hptd O (lt_O_Sn _)).
  rewrite Hx1 Riemann_sum_zero.
  change zero with R0.
  replace (c * (b - x0) - ((b - x0) * phi y0 + 0))
    with ((c - phi y0) * (b - x0)) by ring.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq_0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ;
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply Rlt_le, Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  by apply Req_le.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ;
  rewrite /seq_step /= -Hx1 ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.
  apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
  by rewrite /SF_lx /= Hb.
  rewrite Hx0 Riemann_sum_zero.
  change zero with 0.
  replace (c * (b - b) - 0) with 0 by ring.
  rewrite Rabs_R0 ; apply Rlt_le, eps2.
  apply ptd_sort, Hptd.
  by rewrite /SF_lx /= Hb.

    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, Hptd.
    apply lt_O_Sn.
  rewrite Riemann_sum_cons /= -Ha.
  rewrite Rminus_eq_0 Rmult_0_l Rplus_0_l.
  by apply IH.
Qed.

Lemma ex_RInt_Reals_1 (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> ex_RInt f a b.
Proof.
  move => pr ; exists (RiemannInt pr).
  exact: ex_RInt_Reals_aux_1.
Qed.


Lemma ex_RInt_Reals_2 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
  wlog: a b /(a < b) => [Hw | Hab ] Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: (Rle_lt_or_eq_dec _ _ Hab) => {Hab} Hab.
    by apply Hw.
    rewrite -Hab.
    by apply RiemannInt_P7.
    apply ex_RInt_swap in Hex ;
    apply RiemannInt_P1 ;
    by apply Hw.
  assert ({If : R | is_RInt f a b If}).
    exists (real (Lim_seq (RInt_val f a b))).
    case: Hex => If Hex.
    replace (real (Lim_seq (RInt_val f a b))) with If.
    exact: Hex.
    replace If with (real (Finite If)) by auto.
    apply f_equal, sym_equal, is_lim_seq_unique.
    by apply is_RInt_lim_seq.
  case: H => If HIf.
  generalize (proj1 (filterlim_locally _ If) HIf).
  clear HIf.
  intros HIf.
  set (E := fun eps : posreal =>
    (fun alpha => 0 < alpha <= b-a + 1 /\
      forall ptd : SF_seq,
        pointed_subdiv ptd ->
        seq_step (SF_lx ptd) < alpha ->
        SF_h ptd = Rmin a b ->
        last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
        Rabs (If - sign (b - a) * Riemann_sum f ptd) < eps)).
  have E_bnd : forall eps : posreal, bound (E eps).
    move => eps ; exists (b-a+1) => x [Hx _] ; by apply Hx.
  have E_ex : forall eps : posreal, exists x, (E eps x).
    move => eps ; case: (HIf eps) => {HIf} alpha HIf.
    exists (Rmin alpha (b-a + 1)) ; split.
    apply Rmin_case_strong => H.
    split.
    by apply alpha.
    exact: H.
    split.
    apply Rplus_le_lt_0_compat.
    by apply (Rminus_le_0 a b), Rlt_le.
    exact: Rlt_0_1.
    exact: Rle_refl.
    intros.
    rewrite Rabs_minus_sym.
    apply: HIf.
    move: H0 ; apply Rmin_case_strong.
    by [].
    move => Halp Hstep ; by apply Rlt_le_trans with (b-a+1).
    split.
    exact: H.
    split.
    exact: H1.
    exact: H2.
  set alpha := fun eps : posreal => projT1 (completeness (E eps) (E_bnd eps) (E_ex eps)).
  have Ealpha : forall eps : posreal, (E eps (alpha eps)).
    revert alpha ; move => /= eps.
    case: (E_ex eps) => alp H.
    case: completeness => alpha [ub lub] /= ; split.
    split.
    apply Rlt_le_trans with alp.
    by apply H.
    by apply ub.
    apply: lub => x [Hx _] ; by apply Hx.
    intros.
    apply Rnot_le_lt ; contradict H1.
    apply Rle_not_lt.
    apply: lub => x [Hx1 Hx2].
    apply Rnot_lt_le ; contradict H1.
    by apply Rlt_not_le, Hx2.
  have Hn : forall eps : posreal, {n : nat | (b-a)/(INR n + 1) < alpha eps}.
    move => eps.
    have Hn : 0 <= (b-a)/(alpha eps).
      apply Rdiv_le_0_compat.
      by apply Rlt_le, Rgt_minus.
      by apply Ealpha.
    set n := (nfloor _ Hn).
    exists n.
    apply Rlt_div_l.
    by apply INRp1_pos.
    rewrite Rmult_comm ; apply Rlt_div_l.
    by apply Ealpha.
    rewrite /n /nfloor ; case: nfloor_ex => /= n' Hn'.
    by apply Hn'.

  rewrite /Riemann_integrable.
  suff H : forall eps : posreal,
    {phi : StepFun a b &
    {psi : StepFun a b |
    (forall t : R, Rmin a b <= t <= Rmax a b -> Rabs (f t - phi t) <= psi t) /\
    Rabs (RiemannInt_SF psi) <= eps}}.
  move => eps ; set eps2 := pos_div_2 eps.
  case: (H eps2) => {H} phi [psi [H H0]].
  exists phi ; exists psi ; split.
  exact: H.
  apply Rle_lt_trans with (1 := H0).
  apply Rminus_gt ; simpl ; field_simplify ; rewrite Rdiv_1 ; by apply eps2.

  move => eps ; set eps2 := pos_div_2 eps.
  case: (Hn eps2) => {Hn} n Hn.
  case: (Ealpha eps2) => {HIf} Halpha HIf.

(* Construire phi *)
  set phi := sf_SF_val_fun f a b n.
  exists phi.
(* Construire psi *)
  set psi1 := SF_sup_r (fun t => Rabs (f t - phi t)) a b n.
  have Haux : forall x,
    {i : nat | x = nth 0 (unif_part a b n) i /\ (i < size (unif_part a b n))%nat}
    + {(forall i, (i < size (unif_part a b n))%nat -> x <> nth 0 (unif_part a b n) i)}.
    move => x.
    have : {n0 : nat | x = nth 0 (unif_part a b n) n0
      /\ (n0 < size (unif_part a b n))%nat} +
      {(forall n0 : nat,
      ~ (x = nth 0 (unif_part a b n) n0
      /\ (n0 < size (unif_part a b n))%nat))}.
    apply (Markov (fun i => x = nth 0 (unif_part a b n) i
      /\ (i < size (unif_part a b n))%nat)).
    move => i.
    case: (Req_EM_T x (nth 0 (unif_part a b n) i)) => Hx.
    case: (lt_dec i (size (unif_part a b n))) => Hi.
    left ; split ; by [].
    right ; contradict Hi ; by apply Hi.
    right ; contradict Hx ; by apply Hx.
    case => [[i Hi] | Hx].
    left ; by exists i.
    right => i Hi ;
    move: (Hx i) => {Hx} Hx ;
    contradict Hx ; by split.
  set psi2_aux := fun x => match Haux x with
    | inleft Hi => Rabs (f x - phi x) - psi1 x
    | inright _ => 0
  end.
  set psi2_ly := seq2Rlist (SF_ly (SF_seq_f1 (fun _ => 0) (unif_part a b n) 0)).
  have psi2_ad : adapted_couple psi2_aux a b (seq2Rlist (unif_part a b n)) psi2_ly.
    split.
    by apply sorted_compat, unif_part_sort, Rlt_le.
    split.
    rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
    field ; apply Rgt_not_eq ; by intuition.
    split.
    rewrite size_compat size_mkseq nth_compat nth_mkseq ?S_INR /=.
    rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ ;
    field ; apply Rgt_not_eq ; by intuition.
    by [].
    split.
    by rewrite !size_compat SF_ly_f1 size_belast' size_map.
    rewrite size_compat => i Hi ;
    rewrite !nth_compat SF_ly_f1 => x Hx.
    rewrite /psi2_aux => {psi2_aux} ;
    case: Haux => [ [j [Hx' Hj]] | Hx' ].
    rewrite Hx' in Hx |- * ; case: Hx => Hxi Hxj.
    case: (lt_dec i j) => Hij.
    contradict Hxj ; apply Rle_not_lt.
    apply sorted_incr.
    by apply unif_part_sort, Rlt_le.
    by [].
    by [].
    contradict Hxi ; apply Rle_not_lt.
    apply sorted_incr.
    by apply unif_part_sort, Rlt_le.
    by apply not_lt.
    by intuition.
    move: i Hi {Hx} ;
    elim: (unif_part a b n) => /= [ i Hi | x0].
    by apply lt_n_O in Hi.
    case => /= [ | x1 s] IH i Hi.
    by apply lt_n_O in Hi.
    case: i Hi => /= [ | i] Hi.
    by [].
    by apply IH, lt_S_n.
  have psi2_is : IsStepFun psi2_aux a b.
    exists (seq2Rlist (unif_part a b n)).
    exists psi2_ly.
    by [].
  set psi2 := mkStepFun psi2_is.
  set psi := mkStepFun (StepFun_P28 1 psi1 psi2).

  exists psi.

have Hfin : forall i, (S i < size (unif_part a b n))%nat ->
  is_finite (Sup_fct (fun t0 : R => Rabs (f t0 - phi t0))
    (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
  case: (ex_RInt_ub f a b Hex) => M HM.
  case: (StepFun_bound phi) => M' HM'.
  have : exists m, forall x : R, Rmin a b <= x <= Rmax a b -> m <= phi x.
    case: (StepFun_bound (mkStepFun (StepFun_P28 (-1) (mkStepFun (StepFun_P4 a b 0)) phi)))
    => /= m' Hm'.
    exists (-m') => x Hx.
    replace (phi x) with (- (fct_cte 0 x + -1 * phi x))
      by (rewrite /fct_cte /= ; ring).
    by apply Ropp_le_contravar, Hm'.
  case => m' Hm' i ;
  rewrite size_mkseq => Hi ;
  rewrite !nth_mkseq.
  rewrite /Sup_fct.
  have H : (a + INR i * (b - a) / (INR n + 1)) <
    (a + (INR (S i)) * (b - a) / (INR n + 1)).
    rewrite S_INR ; apply Rminus_gt ; field_simplify.
    rewrite Rdiv_1 Rplus_comm ; apply Rdiv_lt_0_compat.
    by apply Rgt_minus.
    by apply INRp1_pos.
    by apply Rgt_not_eq, INRp1_pos.
  move: (Rlt_not_eq _ _ H) ; case: Req_EM_T => // H0 _.
  move: (ex_Im_fct _ _ _ _) ;
  rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ H) => // _ _ H1.
  rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; case => [l | | ] [ub lub] /=.
  by [].
  case: (lub (Finite (Rmax (M - m') (-(-M - M'))))) => //.
  move => _ [x [-> Hx]].
  apply Rbar_finite_le, Rabs_le_between_Rmax.
  suff H2 : Rmin a b <= x <= Rmax a b.
  split ; apply Rplus_le_compat, Ropp_le_contravar.
  apply Ropp_le_cancel, Rle_trans with (Rabs (f x)).
  by apply Rabs_maj2.
  rewrite Ropp_involutive ; by apply HM.
  by apply HM'.
  apply Rle_trans with  (Rabs (f x)).
  by apply Rle_abs.
  by apply HM.
  by apply Hm'.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ ; split ;
  apply Rlt_le.
  replace a with (a + INR O * (b - a) / (INR n + 1))
    by (simpl ; field ; apply Rgt_not_eq, INRp1_pos).
  apply Rle_lt_trans with (2 := proj1 Hx).
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat ; by intuition.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rgt_minus.
  apply le_INR ; by intuition.
  replace b with (a + INR (S n) * (b - a) / (INR n + 1))
    by (rewrite S_INR ; field ; apply Rgt_not_eq, INRp1_pos).
  apply Rlt_le_trans with (1 := proj2 Hx).
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat ; by intuition.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rgt_minus.
  apply le_INR ; by intuition.
  case : H1 => y Hy.
  by case: (ub y Hy).
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.

have Hfin' : forall t, is_finite (SF_sup_fun (fun t : R => Rabs (f t - phi t)) a b n t).
  rewrite /SF_sup_fun ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite /SF_fun /SF_sup_seq.
  case: (unif_part a b n) Hfin => [ | x0 sx] /=.
  move => _ t ; by case: Rle_dec.
  case: sx => [ | x1 sx] /=.
  move => _ t ; by case: Rle_dec.
  move => H t.
  case: Rlt_dec => Hx0.
  by [].
  elim: sx x0 x1 H Hx0 => [ | x2 sx IH] x0 x1 /= H Hx0.
  case: Rle_dec => Hx1.
  apply (H O) ; by intuition.
  by [].
  case: Rlt_dec => Hx1.
  apply (H O) ; by intuition.
  apply IH.
  move => i Hi ; apply (H (S i) (lt_n_S _ _ Hi)).
  exact: Hx1.

  split.
(* Partie 1 *)
  move => t Ht_ab.
  move: Ht_ab ; rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Ht_ab.
  rewrite /= /psi2_aux /= ; case: (Haux t) => [ [i Hi] | Hi ] ;
  ring_simplify.
  exact: Rle_refl.
  apply Rbar_finite_le ; rewrite Hfin'.
  rewrite /SF_sup_fun ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite /SF_fun /SF_sup_seq.
  move: (unif_part_sort a b n (Rlt_le _ _ Hab)).
  move: Ht_ab.
  pattern b at 1 ; replace b with (last 0 (unif_part a b n)).
  pattern a at 1 ; replace a with (head 0 (unif_part a b n)).
  have : (0 < size (unif_part a b n))%nat.
    rewrite size_mkseq ; exact: lt_O_Sn.
  case: (unif_part a b n) Hi => [ | x0 sx] Hi Hsx Ht_ab Hsort /=.
  by apply lt_irrefl in Hsx.
  clear Hsx.
  case: sx Hsort Hi Ht_ab => [ | x1 sx] Hsort /= Hi [Ht_a Ht_b].
  move: (Rle_antisym _ _ Ht_b Ht_a) => Ht.
  contradict Ht ; apply (Hi O (lt_n_Sn _)).
  apply Rle_not_lt in Ht_a.
  case: Rlt_dec => // _.
  elim: sx x0 x1 Hsort Ht_a Ht_b Hi => [ | x2 sx IH] x0 x1 Hsort /= Ht_a Ht_b Hi.
  case: Rle_dec => // _.
  rewrite /Sup_fct /Lub_Rbar_ne.
  have H : x0 < x1.
    apply Rlt_trans with t.
    apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
    by [].
    contradict Ht_a ; apply sym_not_eq, (Hi O).
    by apply lt_O_Sn.
    case: Ht_b => Ht_b.
    by [].
    contradict Ht_b ; apply (Hi 1%nat).
    by apply lt_n_Sn.
  move: (Rlt_not_eq _ _ H) ;
  case: Req_EM_T => // H0 _.
  case: ex_lub_Rbar_ne => l lub /=.
  apply lub ; exists t ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _ ;
  split.
  apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
  by [].
  contradict Ht_a ; apply sym_not_eq, (Hi O).
  by apply lt_O_Sn.
  case: Ht_b => Ht_b.
  by [].
  contradict Ht_b ; apply (Hi 1%nat).
  by apply lt_n_Sn.
  case: Rlt_dec => Hx1.
   rewrite /Sup_fct /Lub_Rbar_ne.
  have H : x0 < x1.
    apply Rlt_trans with t.
    apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
    by [].
    contradict Ht_a ; apply sym_not_eq, (Hi O).
    by apply lt_O_Sn.
    by apply Hx1.
  move: (Rlt_not_eq _ _ H) ;
  case: Req_EM_T => // H0 _.
  case: ex_lub_Rbar_ne => l lub /=.
  apply lub ; exists t ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _ ;
  split.
  apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
  by [].
  contradict Ht_a ; apply sym_not_eq, (Hi O).
  by apply lt_O_Sn.
  by [].
  apply IH.
  exact: (proj2 Hsort).
  exact: Hx1.
  exact: Ht_b.
  move => j Hj ; apply (Hi (S j) (lt_n_S _ _ Hj)).
  simpl ; field ; apply Rgt_not_eq ; by intuition.
  rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ;
  field ; apply Rgt_not_eq, INRp1_pos.

(* Partie 2 *)
(* * SF_lx ptd = unif_part a b n *)
  assert (forall g : R -> R -> R,
    let ptd := SF_seq_f2 g (unif_part a b n) 0 in
    pointed_subdiv ptd ->
    Rabs (If - sign (b-a) * Riemann_sum f ptd) < eps2).
  move => g ptd Hptd.
  apply HIf.
  exact: Hptd.
  rewrite SF_lx_f2.
  suff : forall i, (S i < size (unif_part a b n))%nat ->
    nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b-a)/(INR n + 1).
  elim: (unif_part a b n) => /= [ | h0 t IH].
  move => _ ; by apply Ealpha.
  case: t IH => /= [ | h1 t] IH Hnth.
  by apply Ealpha.
  replace (seq_step _) with (Rmax (Rabs (h1 - h0)) (seq_step (h1::t))) by auto.
  apply (Rmax_case_strong (Rabs (h1 - h0))) => /= _.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))).
  rewrite Rabs_right.
  exact: Hn.
  apply Rle_ge, Rdiv_le_0_compat.
  by apply Rlt_le, Rgt_minus.
  by intuition.
  apply IH => i Hi.
  by apply (Hnth (S i)), lt_n_S.
  move => i ; rewrite size_mkseq => Hi ; rewrite !nth_mkseq.
  rewrite S_INR ; field ; apply Rgt_not_eq ; by intuition.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
  simpl ; rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
  field ; apply Rgt_not_eq ; by intuition.
  rewrite -nth_last SF_lx_f2.
  replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
  rewrite size_mkseq nth_mkseq.
  simpl ssrnat.predn ; rewrite S_INR /Rmax ;
  case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
  field ; apply Rgt_not_eq ; by intuition.
  simpl ; apply SSR_leq, le_refl.
  move: H => {HIf} HIf.
  assert (forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (unif_part a b n) 0 in
    let ptd2 := SF_seq_f2 g2 (unif_part a b n) 0 in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
    Rabs (Riemann_sum f ptd1 - Riemann_sum f ptd2) < eps).
  move => g1 g2 ptd1 ptd2 H1 H2.
  replace (Riemann_sum f ptd1 - Riemann_sum f ptd2) with
    ((If - sign (b - a) * Riemann_sum f ptd2) -
      (If - sign (b - a) * Riemann_sum f ptd1)).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps) ; apply Rplus_lt_compat ;
  by apply HIf.
  rewrite /sign /=.
  move: (proj1 (Rminus_le_0 _ _) (Rlt_le _ _ Hab)) ; case: Rle_dec => //= H0 _.
  case: Rle_lt_or_eq_dec => //= {H0} H0.
  ring.
  contradict H0.
  by apply Rlt_not_eq, Rgt_minus.
  move: H => {HIf} HIf.
  rewrite /Riemann_sum in HIf.
(* * oublier If *)
  assert (forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (unif_part a b n) 0 in
    let ptd2 := SF_seq_f2 g2 (unif_part a b n) 0 in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
      Rabs
        (Riemann_sum (fun x => x) (SF_seq_f2 (fun x y => f (g1 x y) - f (g2 x y))
          (unif_part a b n) 0)) < eps).
  move => g1 g2 ptd1 pdt2 H1 H2.
  replace (Riemann_sum _ _ : R) with
    (Riemann_sum f (SF_seq_f2 g1 (unif_part a b n) 0) -
    Riemann_sum f (SF_seq_f2 g2 (unif_part a b n) 0)).
  apply HIf.
  exact: H1.
  exact: H2.
  elim: (unif_part a b n) (0) => /= [ x0 | h0].
  rewrite /Riemann_sum /= ; ring.
  case => /= [ | h1 t] IH x0.
  rewrite /Riemann_sum /= ; ring.
  rewrite !(SF_cons_f2 _ h0) /= ; try by intuition.
  rewrite !Riemann_sum_cons /= -IH ; ring.
  move:H => {HIf} HIf.
(* * faire rentrer Rabs dans l'intégrale *)
  assert (forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (unif_part a b n) 0 in
    let ptd2 := SF_seq_f2 g2 (unif_part a b n) 0 in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
      Riemann_sum id
      (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
      (unif_part a b n) 0) < eps).
  move => g1 g2 ptd1 ptd2 H1 H2.
  set h1 := fun x y => match Rle_dec (f (g1 x y)) (f (g2 x y)) with
    | left _ => g2 x y | right _ => g1 x y end.
  set h2 := fun x y => match Rle_dec (f (g1 x y)) (f (g2 x y)) with
    | left _ => g1 x y | right _ => g2 x y end.
  replace (Riemann_sum id
    (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
    (unif_part a b n) 0)) with
    (Riemann_sum id (SF_seq_f2 (fun x y : R => (f (h1 x y) - f (h2 x y)))
    (unif_part a b n) 0)).
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply HIf.
    revert ptd1 ptd2 H1 H2.
    elim: (unif_part a b n) (0) => [z /= _ _ | x0].
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    case => [ | x1 t] /= IH z H1 H2.
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    move: H1 H2 ; rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    move => H1 H2 ; case => [ | i] /= Hi.
    rewrite /h1 ; case: Rle_dec => //= _.
    apply (H2 O (lt_O_Sn _)).
    apply (H1 O (lt_O_Sn _)).
    apply (IH x0 (ptd_cons _ _ H1) (ptd_cons _ _ H2)).
    apply lt_S_n, Hi.
    revert ptd1 ptd2 H1 H2.
    elim: (unif_part a b n) (0) => [z /= _ _ | x0].
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    case => [ | x1 t] /= IH z H1 H2.
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    move: H1 H2 ; rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    move => H1 H2 ; case => [ | i] /= Hi.
    rewrite /h2 ; case: Rle_dec => //= _.
    apply (H1 O (lt_O_Sn _)).
    apply (H2 O (lt_O_Sn _)).
    apply (IH x0 (ptd_cons _ _ H1) (ptd_cons _ _ H2)).
    apply lt_S_n, Hi.
  elim: (unif_part a b n) (0) => [x0 | x0].
  by rewrite /Riemann_sum /= .
  case => [ | x1 t] IH z.
  by rewrite /Riemann_sum /= .
  rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /h1 /h2 /id ; case: Rle_dec => H0.
  rewrite Rabs_left1.
  ring.
  by apply Rle_minus.
  rewrite Rabs_right.
  ring.
  by apply Rgt_ge, Rgt_minus, Rnot_le_lt.
  by apply IH.
  move: H => {HIf} HIf.
(* * phi (g x y) = f (h x y) *)
  assert (forall g : R -> R -> R,
    (forall i j, (S i < size (unif_part a b n))%nat ->
      (j < size (unif_part a b n))%nat ->
      g (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))
      <> nth 0 (unif_part a b n) j) ->
    let ptd := SF_seq_f2 g (unif_part a b n) 0 in
    pointed_subdiv ptd ->
    Riemann_sum id
    (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y)))
    (unif_part a b n) 0) < eps).
  move => g1 Hg1 ptd1 H1.
  rewrite /phi /sf_SF_val_fun ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _.
  move: (unif_part_nat a b n) => Hp.
  set h := fun t => match Rle_dec a t with
    | right _ => t
    | left Ha => match Rle_dec t b with
      | right _ => t
      | left Hb => match Hp t (conj Ha Hb) with
        | inleft H => (a + (INR (projT1 H) + /2) * (b - a) / (INR n + 1))
        | inright _ => (a + (INR n + /2) * (b - a) / (INR n + 1))
      end
    end
  end.
  set g2 := fun x y => h (g1 x y).
  set ptd2 := SF_seq_f2 g2 (unif_part a b n) 0.
  have H2 : pointed_subdiv ptd2.
    move => i ; move: (H1 i) => {H1}.
    rewrite !SF_lx_f2 !SF_ly_f2 !SF_size_f2 size_mkseq.
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
      with (unif_part a b n) by auto.
    move => H1 Hi ; move: (H1 Hi) => {H1}.
    simpl in Hi.
    rewrite !nth_behead !(nth_pairmap 0).
    replace (nth 0 (0 :: unif_part a b n) (S i)) with
      (nth 0 (unif_part a b n) i) by auto.
    rewrite /g2 /h => {h g2 ptd2 ptd1} H1.
    case: Rle_dec => Ha.
    case: Rle_dec => Hb.
    case: Hp => [ [j [Ht Hj]] | Ht] ; simpl projT1.
    suff Hij : j = i.
    rewrite Hij in Ht, Hj |- * => {j Hij}.
    rewrite !nth_mkseq.
    rewrite S_INR.
    split ; simpl ; apply Rminus_le_0 ; field_simplify.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by field.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by field.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; rewrite size_mkseq in Hi, Hj ; by intuition.
    apply SSR_leq ; rewrite size_mkseq in Hi, Hj ; by intuition.
    apply le_antisym ; apply not_lt.
    have Hij : nth 0 (unif_part a b n) j < nth 0 (unif_part a b n) (S i).
      apply Rle_lt_trans with
        (g1 (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
      by apply Ht.
      case: (proj2 H1) => {H1} H1.
      exact: H1.
      contradict H1 ; apply (Hg1 i (S i)).
      rewrite size_mkseq ; by apply lt_n_S.
      rewrite size_mkseq ; by apply lt_n_S.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le, Hab.
    by [].
    by intuition.
    move: (Rle_lt_trans _ _ _ (proj1 H1) (proj2 Ht)) => Hij.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le, Hab.
    by [].
    rewrite size_mkseq ; by intuition.
    suff : i = n.
    move => ->.
    rewrite !nth_mkseq ?S_INR.
    split ; simpl ; apply Rminus_le_0 ; field_simplify.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by ring.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by ring.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; by intuition.
    apply SSR_leq ; by intuition.
    apply le_antisym ; apply not_lt.
    have Hij : nth 0 (unif_part a b n) i < nth 0 (unif_part a b n) (S n).
      apply Rle_lt_trans with
        (g1 (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
      by apply H1.
      case: (proj2 Ht) => {Ht} Ht.
      exact: Ht.
      contradict Ht ; apply Hg1.
      rewrite size_mkseq ; by apply lt_n_S.
      rewrite size_mkseq ; by apply lt_n_Sn.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le , Hab.
    by intuition.
    rewrite size_mkseq ; by intuition.
    have Hij : nth 0 (unif_part a b n) (n) < nth 0 (unif_part a b n) (S i).
      apply Rle_lt_trans with
        (g1 (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
      by apply Ht.
      case: (proj2 H1) => {H1} H1.
      exact: H1.
      contradict H1 ; apply Hg1.
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq ; by intuition.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le, Hab.
    by [].
    rewrite size_mkseq ; by intuition.
    exact: H1.
    exact: H1.
    apply SSR_leq ; rewrite size_mkseq ; by intuition.
    apply SSR_leq ; rewrite size_mkseq ; by intuition.
    move: (HIf g1 g2 H1 H2).
    replace (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - SF_val_fun f a b n (g1 x y)))
     (unif_part a b n) 0) with
     (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
     (unif_part a b n) 0).
    by [].
    have H0 : forall t, a <= t <= b -> SF_val_fun (z:=0) f a b n t = f (h t).
      move => t Ht.
      rewrite /h SF_val_fun_rw.
      case: Ht => Ha Hb.
      case: Rle_dec => // Ha'.
      case: Rle_dec => // Hb'.
      case: unif_part_nat => [ [i [Ht Hi]] | Ht] ;
      case: Hp {h g2 ptd2 H2} => [ [j [Ht' Hj]] | Ht'] ; simpl projT1.
      apply (f_equal (fun i => f (a + (INR i + /2) * (b - a) / (INR n + 1)))).
      apply le_antisym ; apply not_lt.
      move: (Rle_lt_trans _ _ _ (proj1 Ht) (proj2 Ht')) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      apply unif_part_sort, Rlt_le, Hab.
      by [].
      by intuition.
      move: (Rle_lt_trans _ _ _ (proj1 Ht') (proj2 Ht)) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply unif_part_sort, Rlt_le.
      by [].
      by intuition.
      absurd (i < n)%nat.
      move: (Rle_lt_trans _ _ _ (proj1 Ht') (proj2 Ht)) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply unif_part_sort, Rlt_le.
      by [].
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq in Hi ; by intuition.
      absurd (j < n)%nat.
      move: (Rle_lt_trans _ _ _ (proj1 Ht) (proj2 Ht')) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply unif_part_sort, Rlt_le.
      by [].
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq in Hj ; by intuition.
      by [].
    rewrite /g2.
  have : forall i, (i < size (unif_part a b n))%nat ->
    a <= nth 0 (unif_part a b n) i <= b.
    move => i ; rewrite size_mkseq => Hi ; rewrite nth_mkseq.
    pattern b at 3 ; replace b with (a + (INR n + 1) * (b - a) / (INR n + 1)) by
      (field ; apply Rgt_not_eq ; intuition).
    pattern a at 1 ; replace a with (a + 0 * (b - a) / (INR n + 1)) by
      (field ; apply Rgt_not_eq ; intuition).
    apply Rgt_minus in Hab.
    split ; apply Rplus_le_compat_l ; repeat apply Rmult_le_compat_r ;
    try by intuition.
    rewrite -S_INR ; apply le_INR ; by intuition.
    by apply SSR_leq.
    revert ptd1 H1 ;
    elim: (unif_part a b n) {4 6}(0) => [ z ptd1 H1 Hnth | x0 ].
    by [].
    case => [ | x1 s] IH z ptd1 H1 Hnth.
    by [].
    revert ptd1 H1 ;
    rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    intro ;
    apply (f_equal2 (fun x y => SF_cons (x0, Rabs (f (g1 x0 x1) - x)) y)).
    apply sym_equal, H0.
    move: (H1 O (lt_O_Sn _))
      (Hnth O (lt_O_Sn _)) (Hnth 1%nat (lt_n_S _ _ (lt_O_Sn _))) => /= ; intuition.
    by apply Rle_trans with x0.
    by apply Rle_trans with x1.
    apply (IH x0 (ptd_cons _ _ H1)).
    move => i Hi ; apply (Hnth (S i)) ; simpl in Hi |- * ; by apply lt_n_S.

  move: H => {HIf} HIf.
  rewrite Rabs_right.

(* * dernière étape :-) *)
  replace (RiemannInt_SF psi) with
    (Riemann_sum id (SF_seq_f2 (fun x y : R => real (Sup_fct (fun t => Rabs (f t - phi t)) x y))
    (unif_part a b n) 0)).
  set (F := fun z s val => exists g : R -> R -> R,
    (forall (i j : nat),
    (S i < size s)%nat -> (j < size s)%nat
      -> g (nth 0 s i) (nth 0 s (S i)) <> nth 0 s j) /\
    (let ptd := SF_seq_f2 g s z in pointed_subdiv ptd) /\
    Riemann_sum id (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y)))
      s z) = val).
  cut (is_lub (F 0 (unif_part a b n)) (Riemann_sum id (SF_seq_f2
    (fun x y : R => real (Sup_fct (fun t : R => Rabs (f t - phi t)) x y))
    (unif_part a b n) 0))) => [ Hlub | ].

  apply Hlub => val [g [Hnth [H0 Hval]]].
  apply Rlt_le ; rewrite -Hval.
  apply HIf.
  exact: Hnth.
  exact: H0.

  Focus 2.
  rewrite StepFun_P30.
  replace (RiemannInt_SF psi2) with 0.
  rewrite Rmult_0_r Rplus_0_r /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  elim: (unif_part a b n) (unif_part_sort a b n (Rlt_le _ _ Hab)) {1}(0)
  => [ Hsort z | x0 ].
  by [].
  case => [ | x1 s] IH Hsort z.
  by [].
  rewrite SF_cons_f2 /=.
  rewrite Riemann_sum_cons /=.
  rewrite Rmult_comm.
  by apply f_equal, IH, Hsort.
  exact: lt_O_Sn.
  rewrite /RiemannInt_SF ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (StepFun_P17 (StepFun_P1 psi2) psi2_ad).
  clear psi2_ad.
  revert psi2_ly ; elim: (unif_part a b n) => /= [ | x0].
  by [].
  case => /= [ | x1 s] IH.
  by [].
  rewrite -IH ; ring.

  Focus 2.
  rewrite StepFun_P30.
  replace (RiemannInt_SF psi2) with 0.
  rewrite Rmult_0_r Rplus_0_r ;
  rewrite /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  elim: (unif_part a b n) (unif_part_sort a b n (Rlt_le _ _ Hab))
    => [ Hsort /= | x0].
  by apply Rge_refl.
  case => [ | x1 s] IH Hsort /=.
  by apply Rge_refl.
  apply Rle_ge, Rplus_le_le_0_compat.
  apply Rmult_le_pos.
  rewrite /Sup_fct /Lub_Rbar_ne.
  case: Req_EM_T => Hx0.
  by apply Rle_refl.
  case: ex_lub_Rbar_ne ;
  case => [l | | ] [ub lub] /=.
  apply Rle_trans with (Rabs (f ((x0+x1)/2) - phi ((x0+x1)/2))).
  apply Rabs_pos.
  apply Rbar_finite_le, ub.
  exists ((x0+x1)/2) ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _.
  pattern x1 at 3 ; replace x1 with ((x1 + x1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_lt_compat_r.
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
  apply Rplus_lt_compat_l ; by case: (proj1 Hsort).
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
  apply Rplus_lt_compat_r ; by case: (proj1 Hsort).
  apply Rle_refl.
  apply Rle_refl.
  apply -> Rminus_le_0 ; apply Hsort.
  apply Rge_le, IH, Hsort.
  rewrite /RiemannInt_SF ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (StepFun_P17 (StepFun_P1 psi2) psi2_ad).
  clear psi2_ad.
  revert psi2_ly ; elim: (unif_part a b n) => /= [ | x0].
  by [].
  case => /= [ | x1 s] IH.
  by [].
  rewrite -IH ; ring.

(* ** c'est la bonne borne sup *)

  move: Hfin.
  have : sorted Rlt (unif_part a b n).
    apply sorted_nth => i.
    rewrite size_mkseq => Hi x0 ; rewrite !nth_mkseq.
    apply Rminus_gt ; rewrite S_INR ; field_simplify.
    rewrite Rdiv_1.
    apply Rdiv_lt_0_compat.
    rewrite Rplus_comm ; by apply Rgt_minus.
    by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; by intuition.
    apply SSR_leq ; by intuition.
  elim: (unif_part a b n) {3 4}(0) (unif_part_sort a b n (Rlt_le _ _ Hab))
    => [ x0 Hle Hlt Hfin | x1].
  split ; rewrite /Riemann_sum /=.
  move => val [g [Hnth [Hptd Hval]]].
  rewrite -Hval ; by apply Rle_refl.
  move => ub Hub ; apply: Hub.
  exists (fun _ _ => 0).
  split.
  move => i j Hi Hj ; by apply lt_n_O in Hi.
  split.
  move => ptd i Hi ; by apply lt_n_O in Hi.
  split.
  case => [ | x2 s] IH x0 Hle Hlt Hfin.
  split ; rewrite /Riemann_sum /=.
  move => val [g [Hnth [Hptd Hval]]].
  rewrite -Hval ; by apply Rle_refl.
  move => ub Hub ; apply: Hub.
  exists (fun _ _ => 0).
  split.
  move => i j Hi Hj.
  simpl in Hi ; by apply lt_S_n, lt_n_O in Hi.
  split.
  move => ptd i Hi ; by apply lt_n_O in Hi.
  split.
  rewrite SF_cons_f2 /= ; last by apply lt_O_Sn.
  rewrite Riemann_sum_cons /=.
  set F0 := fun x =>
    exists t, x1 < t < x2 /\ x = Rabs (f t - phi t) * (x2 - x1).
  set set_plus := fun (F : R -> Prop) (G : R -> Prop) (x : R) =>
    exists y, exists z, x = y + z /\ F y /\ G z.
  suff H0 : forall (x : R), F x0 [:: x1, x2 & s] x
    <-> (set_plus (F0) (F x1 (x2::s))) x.
  cut (is_lub (set_plus (F0) (F x1 (x2::s)))
    (real (Sup_fct (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1) +
    Riemann_sum id
    (SF_seq_f2
    (fun x y : R => real (Sup_fct (fun t : R => Rabs (f t - phi t)) x y))
    (x2 :: s) x1))) => [H1 | ].
  split.
  move => x Hx.
  rewrite Rmult_comm.
  by apply H1, H0.
  move => ub Hub.
  rewrite Rmult_comm.
  apply H1 => x Hx ; by apply Hub, H0.
  suff H_F0 : is_lub (F0) (real (Sup_fct
    (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1)).
  have Hfin0 : (forall i : nat,
    (S i < size (x2 :: s))%nat ->
    is_finite
    (Sup_fct (fun t0 : R => Rabs (f t0 - phi t0)) (nth 0 (x2 :: s) i)
       (nth 0 (x2 :: s) (S i)))).
    move => i /= Hi ; move: (Hfin (S i) (lt_n_S _ _ Hi)) => /= {Hfin}.
    by [].

  move: H_F0 (IH x1 (proj2 Hle) (proj2 Hlt) Hfin0).

  move: (F0 (pos_div_2 eps)) (F x1 (x2::s) (pos_div_2 eps))
    (real (Sup_fct (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1))
    (Riemann_sum id (SF_seq_f2 (fun x4 y : R =>
      real (Sup_fct (fun t : R => Rabs (f t - phi t)) x4 y)) (x2 :: s) x1)).
  move => F1 F2 l1 l2 Hl1 Hl2.
    split.
    move => _ [y [z [-> Hx]]].
    apply Rplus_le_compat.
    by apply Hl1, Hx.
    by apply Hl2, Hx.
    move => ub Hub.
    replace ub with ((ub-l2) + l2) by ring.
    apply Rplus_le_compat_r.
    apply Hl1 => y Hy.
    replace y with (l2 + (y - l2)) by ring.
    replace (ub-l2) with ((ub - y) + (y - l2)) by ring.
    apply Rplus_le_compat_r.
    apply Hl2 => z Hz.
    replace z with ((y+z) - y) by ring.
    apply Rplus_le_compat_r.
    apply Hub.
    exists y ; exists z ; by intuition.
  move: (Hfin O (lt_n_S _ _ (lt_O_Sn _))).
  rewrite /Sup_fct /=.
  move: (Rlt_not_eq _ _ (proj1 Hlt)).
  case: Req_EM_T => // Hx1 _.
  rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ;
    case => [l | | ] [ub lub] ; simpl.
    split.
    move => _ [t [Ht ->]].
    apply Rmult_le_compat_r.
    apply -> Rminus_le_0 ; apply Hle.
    apply Rbar_finite_le, ub ; exists t ; split.
    by [].
    rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hle) => // _ _ ;
    by intuition.
    move => b0 Hb0.
    move: (Rgt_minus _ _ (proj1 Hlt)) => H1.
    replace b0 with ((b0 / (x2 - x1)) * (x2 - x1)) by
      (field ; by apply Rgt_not_eq).
    apply Rmult_le_compat_r.
    by apply Rlt_le.
    apply Rbar_finite_le, lub => _ [t [-> Ht]].
    apply Rbar_finite_le.
    replace (Rabs (f t - phi t)) with ((Rabs (f t - phi t) * (x2 - x1)) / (x2 - x1))
      by (field ; by apply Rgt_not_eq).
    apply Rmult_le_compat_r.
    by apply Rlt_le, Rinv_0_lt_compat.
    apply Hb0 ; exists t.
    split.
    move: Ht ; rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hle) => //.
    by [].


  by [].
  by [].

    move => val ; split => Hval.
    case: Hval => g [Hnth [Hptd <-]] {val}.
    rewrite SF_cons_f2 /=.
    rewrite Riemann_sum_cons /=.
    exists (Rabs (f (g x1 x2) - phi (g x1 x2)) * (x2 - x1)).
    exists (Riemann_sum id
      (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y))) (x2 :: s) x1)).
    split.
    rewrite Rmult_comm.
    by [].
    split.
    exists (g x1 x2) ; split.
    case: (Hptd O) => /=.
    rewrite SF_size_f2 /= ; exact: lt_O_Sn.
    case => Hx1.
    case => Hx2.
    by split.
    contradict Hx2 ; apply (Hnth O 1%nat).
    simpl ; by intuition.
    simpl ; by intuition.
    contradict Hx1 ; apply sym_not_eq, (Hnth O O).
    simpl ; by intuition.
    simpl ; by intuition.

    by [].
    exists g.
    split.
    move => i j Hi Hj.
    apply (Hnth (S i) (S j)).
    simpl ; apply lt_n_S, Hi.
    simpl ; apply lt_n_S, Hj.
    split.
    move: Hptd => /=.
    rewrite SF_cons_f2 /=.
    apply ptd_cons.
    apply lt_O_Sn.
    split.
    exact: lt_O_Sn.

    case: Hval => /= y Hy.
    case: Hy => /= z [-> [F0y Fz]].
    case: F0y => t [Ht ->].
    case: Fz => g [Hnth [Hpdt <-]].
    set g0 := fun x y => match Req_EM_T x x1 with
      | left _ => match Req_EM_T y x2 with
        | left _ => t
        | right _ => g x y
      end
      | right _ => g x y
    end.
    exists g0.
    split.
    move => {val y z} i j Hi Hj.
    rewrite /g0.
    case: Req_EM_T => Hx1'.
    case: Req_EM_T => Hx2'.
    case: j Hj => /= [ | j] Hj.
    by apply Rgt_not_eq, Ht.
    apply lt_S_n in Hj ; case: j Hj => /= [ | j] Hj.
    by apply Rlt_not_eq, Ht.
    move: (proj2 Hle : sorted Rle (x2 :: s)).
    apply lt_S_n in Hj ; move: (proj2 Ht) ;
    elim: j x2 s Hj {IH Hle Hlt Hfin Hnth Hpdt F0 Ht g0 Hx2' x0 Hx1' i Hi}
      => [ | i IH] x0 ; case => {x1} [ | x1 s] Hi Ht Hle ; simpl.
    by apply lt_irrefl in Hi.
    apply Rlt_not_eq, Rlt_le_trans with (1 := Ht).
    by apply Hle.
    by apply lt_n_O in Hi.
    apply (IH x1).
    by apply lt_S_n, Hi.
    apply Rlt_le_trans with (1 := Ht).
    by apply Hle.
    by apply Hle.
    case: i j Hi Hj Hx1' Hx2' => /= [ | i] j Hi Hj Hx1' Hx2'.
    by [].
    case: j Hj => /= [ | j] Hj.
    apply Rgt_not_eq, Rlt_le_trans with x2.
    apply Rlt_trans with t ; by intuition.
    apply Rle_trans with (nth 0 (x2 :: s) i).
    apply (sorted_incr (x2 :: s) O i).
    move: (ptd_sort _ Hpdt).
    by rewrite /SF_sorted SF_lx_f2.
    by intuition.
    simpl ; by intuition.
    move: (Hpdt i).
    rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 (nth_pairmap 0) /=.
    move => H ; apply H.
    by intuition.
    apply SSR_leq ; by intuition.
    apply Hnth.
    by intuition.
    by intuition.
    simpl in Hi ; apply lt_S_n in Hi ;
    case: i Hi Hx1' => /= [ | i] Hi Hx1'.
    by [].
    case: j Hj => /= [ | j] Hj.
    apply Rgt_not_eq, Rlt_le_trans with x2.
    apply Rlt_trans with t ; by intuition.
    apply Rle_trans with (nth 0 (x2 :: s) i).
    apply (sorted_incr (x2 :: s) O i).
    move: (ptd_sort _ Hpdt).
    by rewrite /SF_sorted SF_lx_f2.
    by intuition.
    simpl ; by intuition.
    move: (Hpdt i).
    rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 (nth_pairmap 0) /=.
    move => H ; apply H.
    by intuition.
    apply SSR_leq ; by intuition.
    apply Hnth.
    by intuition.
    by intuition.
  split.
  move => ptd i Hi.
  rewrite SF_size_f2 /= in Hi.
  rewrite SF_lx_f2 SF_ly_f2 nth_behead (nth_pairmap 0) /=.
  case: i Hi => /= [ | i] Hi ; rewrite /g0.
  move: (refl_equal x1) ; case: Req_EM_T => // _ _.
  move: (refl_equal x2) ; case: Req_EM_T => // _ _.
  split ; apply Rlt_le ; by intuition.
  suff : (nth 0 (x2 :: s) i) <> x1.
  case: Req_EM_T => // _ _.
  move: (Hpdt i).
  rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 nth_behead (nth_pairmap 0) /=.
  move => H ; apply H ; by intuition.
  apply SSR_leq ; by intuition.
  apply Rgt_not_eq, Rlt_le_trans with x2.
  apply Rlt_trans with t ; by intuition.
  apply (sorted_incr (x2 :: s) O i).
  move: (ptd_sort _ Hpdt).
  by rewrite /SF_sorted SF_lx_f2.
  by intuition.
  simpl ; by intuition.
  apply SSR_leq ; by intuition.
  rewrite SF_cons_f2 /=.
  rewrite Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (refl_equal x1) ; case: Req_EM_T => // _ _.
  move: (refl_equal x2) ; case: Req_EM_T => // _ _.
  apply Rmult_comm.
  case: s Hlt {Hpdt IH Hle Hfin F0 Ht Hnth}
    => [ | x3 s] Hlt /=.
  apply refl_equal.
  rewrite !(SF_cons_f2 _ _ (x3 :: _)) /=.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /g0 /id ; move: (Rgt_not_eq _ _ (proj1 Hlt)) ;
  by case: Req_EM_T.
  elim: s (x2) x3 Hlt => [ | x4 s IH] x2' x3 Hlt.
  exact: refl_equal.
  rewrite !(SF_cons_f2 _ _ (x4 :: _)) /=.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (Rgt_not_eq _ _ (Rlt_trans _ _ _ (proj1 Hlt) (proj1 (proj2 Hlt)))) ;
  by case: Req_EM_T.
  apply IH.
  split.
  apply Rlt_trans with x2' ; apply Hlt.
  apply Hlt.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
Qed.

Lemma RInt_Reals (f : R -> R) (a b : R) :
  forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
  wlog: a b /(a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    move => pr ; set pr' := (RiemannInt_P1 pr).
    rewrite (RiemannInt_P8 _ pr').
    move: (Hw _ _ (Rlt_le _ _ Hab) pr').
    rewrite /RInt ; case: Rle_dec ;
    case: Rle_dec (Rlt_le _ _ Hab) (Rlt_not_le _ _ Hab) => // _ _ _ _.
    by move => ->.
  move => pr ; rewrite /RInt ; case: Rle_dec => // _.
  replace (RiemannInt pr) with (real (Finite (RiemannInt pr))) by auto.
  apply f_equal, is_lim_seq_unique.
  apply is_RInt_lim_seq.
  exact: ex_RInt_Reals_aux_1.
Qed.

(** ** Theorems proved using standard library *)

Lemma ex_RInt_included1: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_Reals_1.
apply RiemannInt_P22 with b;[now apply ex_RInt_Reals_2|exact H2].
Qed.

Lemma ex_RInt_included2: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f c b.
intros f a b c H1 H2.
apply ex_RInt_Reals_1.
apply RiemannInt_P23 with a;[now apply ex_RInt_Reals_2|exact H2].
Qed.

Lemma ex_RInt_inside :
  forall f a b x e,
  ex_RInt f (x-e) (x+e) -> Rabs (a-x) <= e -> Rabs (b-x) <= e ->
  ex_RInt f a b.
Proof.
intros f a b x e Hf Ha Hb.
wlog: a b Ha Hb / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
now left.
apply ex_RInt_included1 with (x+e).
apply ex_RInt_included2 with (x-e).
exact Hf.
now apply Rabs_le_between'.
split.
exact Hab.
assert (x-e <= b <= x+e) by now apply Rabs_le_between'.
apply H.
Qed.

Lemma ex_RInt_cont: forall f a b, (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f x)
  -> ex_RInt f a b.
Proof.
intros f a b H.
wlog: a b H / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H'.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
intros x; rewrite Rmin_comm Rmax_comm.
apply H.
now left.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt.
exact Hab.
intros; apply H.
rewrite Rmin_left; try exact Hab.
now rewrite Rmax_right.
Qed.

Lemma RInt_le: forall f g a b,
    a <= b ->
   ex_RInt f a b ->  ex_RInt g a b -> 
   (forall x,  a <= x <= b -> f x <= g x) ->
   RInt f a b <= RInt g a b.
Proof.
intros f g a b H1 If Ig H2.
assert (Riemann_integrable f a b).
now apply ex_RInt_Reals_2.
assert (Riemann_integrable g a b).
now apply ex_RInt_Reals_2.
rewrite (RInt_Reals _ _ _ X)(RInt_Reals _ _ _ X0).
apply RiemannInt_P19.
exact H1.
intros; apply H2.
split; left; apply H.
Qed.

Lemma is_RInt_le: forall f g a b If Ig,
  a <= b ->
   is_RInt f a b If ->  is_RInt g a b Ig ->
   (forall x,  a <= x <= b -> f x <= g x) ->
   If <= Ig.
Proof.
intros f g a b If Ig Hab Hf Hg Heq.
rewrite -(is_RInt_unique _ _ _ _ Hf).
rewrite -(is_RInt_unique _ _ _ _ Hg).
apply RInt_le => //.
by exists If.
by exists Ig.
Qed.

Lemma ex_RInt_norm :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => norm (f x)) a b.
Proof.
intros f a b If.
apply ex_RInt_Reals_1.
apply RiemannInt_P16.
now apply ex_RInt_Reals_2.
Qed.

Lemma RInt_abs: forall f a b,
  a <= b -> ex_RInt f a b ->
  Rabs (RInt f a b) <= RInt (fun t => Rabs (f t)) a b.
Proof.
intros f a b H1 If.
replace (Rabs _) with (norm (RInt f a b)) by (unfold norm ; by simpl).
apply: (RInt_norm f (fun t : R => norm (f t)) a b).
by [].
move => x _ ; by apply Rle_refl.
by apply RInt_correct.
by apply RInt_correct, ex_RInt_norm.
Qed.

Lemma RInt_le_const: forall f a b M,
  ex_RInt f a b ->
  (forall t, Rmin a b <= t <= Rmax a b -> Rabs (f t) <= M) ->
  Rabs (RInt f a b) <= Rabs (b-a) * M.
intros f a b M If H.
wlog: a b H If / (a <= b) => [Hw | Hab] .
(* *)
case (Rle_or_lt a b); intros Hab.
now apply Hw.
rewrite <- RInt_swap.
replace (b-a) with (-(a-b)) by ring.
rewrite 2! Rabs_Ropp.
apply Hw.
intros t Ht; apply H.
rewrite Rmin_comm Rmax_comm.
exact Ht.
apply ex_RInt_swap.
exact If.
now left.
(* *)
rewrite (Rabs_right (b-a)).
rewrite <- RInt_const.
apply Rle_trans with (1:=RInt_abs _ _ _ Hab If).
apply RInt_le.
exact Hab.
now apply ex_RInt_norm.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt.
exact Hab.
intros x Hx eps Heps.
exists 1; split.
apply Rlt_0_1.
intros.
unfold dist; simpl; unfold R_dist; simpl.
rewrite /Rminus Rplus_opp_r Rabs_R0.
exact Heps.
intros x Hx; apply H.
rewrite (Rmin_left _ _ Hab).
now rewrite Rmax_right.
apply Rle_ge, Rplus_le_reg_l with a.
now ring_simplify.
Qed.

(** * Riemann integral and continuity *)

(* Lemma continuity_RInt: forall f a b,
  ex_RInt f a b ->
  (exists eps:posreal, ex_RInt f (b-eps) (b+eps)) ->
  continuity_pt (fun x : R => RInt f a x) b.
Proof.
intros f a b If (eps,Ifb).
assert (forall y, Rabs (y - b) < eps -> ex_RInt f b y).
  move => y Hy.
  apply ex_RInt_Chasles with (b - eps).
  apply ex_RInt_swap, ex_RInt_included1 with (1 := Ifb).
  apply Rabs_le_between' ; rewrite Rminus_eq_0 Rabs_R0.
  by apply Rlt_le, eps.
  apply ex_RInt_included1 with (1 := Ifb).
  apply Rabs_le_between'.
  by apply Rlt_le, Hy. 

apply continuity_pt_ext_loc with (fun x => RInt f a b + RInt f b x).
  exists eps => /= y Hy.
  apply RInt_Chasles.
  by apply If.
  by apply H.
apply continuity_pt_plus.
by apply continuity_pt_const.

apply continuity_pt_filterlim.
apply continuity_RInt_0 with f.
exists eps => /= y Hy.
apply RInt_correct.
by apply H.
Qed. *)

(** * Riemann integral and differentiability *)

Lemma derivable_pt_lim_RInt (f : R -> R) (a : R) (x : R) :
  ex_RInt f a x -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x -> derivable_pt_lim (fun x => RInt f a x) x (f x).
Proof.
  move => Iax Iloc Cx.
  apply filterdiff_Reals ; split.
  by apply @is_linear_scal.
  intros y Hy eps.
  rewrite -(is_filter_lim_locally_R _ _ Hy) => {y Hy}.
  destruct (Cx eps (cond_pos eps)) as (d,(Hd1,Hd2)).
  unfold dist in Hd2; simpl in Hd2; unfold R_dist in Hd2.
  destruct Iloc as (e,He).
  exists (mkposreal _ (Rmin_stable_in_posreal e (mkposreal _ Hd1))).
  (* *)
  simpl; intros y Hy.
  assert (ex_RInt f x y).
  assert (x-e <= y <= x+e).
  apply Rabs_le_between'.
  left; apply Rlt_le_trans with (1:=Hy); apply Rmin_l.
  case (Rle_or_lt x y); intros M.
  apply ex_RInt_included1 with (x+e).
  apply ex_RInt_included2 with (x-e).
  exact He.
  split; apply Rplus_le_reg_r with (-x); ring_simplify.
  apply Rplus_le_reg_r with e; ring_simplify.
  left; apply cond_pos.
  left; apply cond_pos.
  split;[exact M|apply H].
  apply ex_RInt_swap.
  apply ex_RInt_included1 with (x+e).
  apply ex_RInt_included2 with (x-e).
  exact He.
  exact H.
  split;[left; exact M|idtac].
  apply Rplus_le_reg_r with (-x); ring_simplify.
  left; apply cond_pos.
  assert (ex_RInt f a y).
  now apply ex_RInt_Chasles with x.
  (* *)
  replace (RInt f a y + - RInt f a x + - ((y + - x) * f x)) with
    (RInt (fun z => f z - f x) x y).
  rewrite Rmult_comm.
  apply RInt_le_const.
  apply @ex_RInt_minus.
  exact H.
  apply ex_RInt_const.
  intros t Ht.
  case (Req_dec x t); intros Hxt.
  unfold Rminus; rewrite Hxt Rplus_opp_r Rabs_R0.
  left; apply cond_pos.
  left; apply Hd2.
  split.
  now split.
  apply Rle_lt_trans with (Rabs (y - x)).
  apply Rabs_le_between_min_max.
  now rewrite Rmin_comm Rmax_comm.
  apply Rlt_le_trans with (1:=Hy); apply Rmin_r.
  (* *)
  rewrite RInt_minus.
  rewrite RInt_const.
  rewrite <- (RInt_Chasles f x a y).
  unfold Rminus; rewrite RInt_swap.
  ring.
  now apply ex_RInt_swap.
  exact H0.
  exact H.
  apply ex_RInt_const.
Qed.


Lemma RInt_Derive (f : R -> R) (a b : R):
  (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) ->
  (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt (Derive f) x) ->
  RInt (Derive f) a b = f b - f a.
Proof.
intros Df Cdf.
wlog: a b Df Cdf /(a <= b) => [Hw | Hab ].
case (Rle_or_lt a b); intros Hab.
now apply Hw.
rewrite <- RInt_swap.
rewrite Hw; try easy.
ring.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
now left.
rewrite Rmin_left in Df Cdf; try exact Hab.
rewrite Rmax_right in Df Cdf; try exact Hab.

wlog : f Df Cdf /((forall x, ex_derive f x) /\ (forall x, continuity_pt (Derive f) x))
  => [Hw | {Df Cdf} [Df Cdf]].
  rewrite -?(extension_C1_ext f a b) ; try (apply Rbar_finite_le ; intuition).
  rewrite -(RInt_ext (Derive (extension_C1 f a b))).
  apply Hw.
  move => x Hx.
  apply extension_C1_ex_derive.
  by apply Rbar_finite_le.
  move => y Hay Hyb.
  apply Df ; split ; by apply Rbar_finite_le.
  move => y Hy.
  apply extension_C1_Derive_cont.
  by apply Rbar_finite_le.
  move => x Hax Hxb ; split.
  apply Df ; split ; by apply Rbar_finite_le.
  apply Cdf ; split ; by apply Rbar_finite_le.
  split => x.
  apply extension_C1_ex_derive.
  by apply Rbar_finite_le.
  move => y Hay Hyb.
  apply Df ; split ; by apply Rbar_finite_le.
  apply extension_C1_Derive_cont.
  by apply Rbar_finite_le.
  move => y Hay Hyb ; split.
  apply Df ; split ; by apply Rbar_finite_le.
  apply Cdf ; split ; by apply Rbar_finite_le.
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ x Hx.
  apply is_derive_unique, extension_C1_is_derive.
  by apply Rbar_finite_le, Hx.
  by apply Rbar_finite_le, Hx.
  apply Derive_correct.
  by apply Df.

assert (forall x, continuity_pt f x).
intros x.
destruct (Df x) as (y,Hy).
apply derivable_continuous_pt.
now exists y.
(* *)
destruct (fn_eq_Derive_eq f (fun x => RInt (Derive f) a x) a b).
apply H.
apply H.
apply continuity_pt_filterlim, (continuity_RInt_0 (Derive f)).
exists (mkposreal _ Rlt_0_1) => /= y Hy.
by apply RInt_correct, ex_RInt_cont.
apply continuity_pt_filterlim, (continuity_RInt (Derive f) a).
by apply ex_RInt_cont.
exists (mkposreal _ Rlt_0_1) => /= y Hy.
by apply RInt_correct, ex_RInt_cont.
intros x Hx; apply Df.
intros x Hx.
eexists.
apply derivable_pt_lim_RInt.
by apply ex_RInt_cont.
exists (mkposreal _ Rlt_0_1).
by apply ex_RInt_cont.
apply Cdf.
intros x Hx.
apply sym_eq, is_derive_unique.
apply derivable_pt_lim_RInt.
by apply ex_RInt_cont.
exists (mkposreal _ Rlt_0_1).
by apply ex_RInt_cont.
apply Cdf.
rewrite (H0 a).
rewrite (H0 b).
rewrite RInt_point.
ring.
split;[apply Hab|apply Rle_refl].
split;[apply Rle_refl | apply Hab].
Qed.


Lemma is_RInt_Derive (f : R -> R) (a b : R) :
  (forall x, Rmin a b  <= x <= Rmax a b  -> ex_derive f x) ->
  (forall x, Rmin a b  <= x <= Rmax a b  -> continuity_pt (Derive f) x) ->
  is_RInt (Derive f) a b (f b - f a).
Proof.
  move => Df Cdf.
  rewrite -(RInt_Derive _ _ _ Df Cdf).
  cut (ex_RInt (Derive f) a b).
    case => l H.
    by rewrite (is_RInt_unique _ _ _ _ H).
  apply ex_RInt_cont.
  move => x Hx.
  by apply Cdf.
Qed.

Lemma derivable_pt_lim_RInt' :
  forall f a x,
  ex_RInt f x a -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x ->
  derivable_pt_lim (fun x => RInt f x a) x (- f x).
Proof.
intros f a x Hi Ix Cx.
apply (is_derive_ext (fun u => - RInt f a u)).
intros t.
apply RInt_swap.
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt ; try easy.
apply ex_RInt_Reals_1.
apply RiemannInt_P1.
now apply ex_RInt_Reals_2.
Qed.

Lemma is_RInt_comp (f g : R -> R) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f (g x))
  -> (forall x, Rmin a b <= x <= Rmax a b -> ex_derive g x /\ continuity_pt (Derive g) x)
  -> is_RInt (fun y => Derive g y * f (g y)) a b (RInt f (g a) (g b)).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
    move => Hf Hg.
    rewrite RInt_point ; by apply @is_RInt_point.
  wlog: a b Hab /(a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab' Hf Hg.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -RInt_swap.
    apply @is_RInt_swap.
    apply Hw => //.
    by apply sym_not_eq.
    rewrite Rmin_comm Rmax_comm.
    by apply Hf.
    rewrite Rmin_comm Rmax_comm.
    by apply Hg.
  rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab)
    => // _ _.

  wlog: g / (forall x : R, ex_derive g x /\ continuity_pt (Derive g) x) => [Hw Hf Hg | Hg Hf _].
    rewrite -?(extension_C1_ext g a b) ; try by [left | right].
    set g0 := extension_C1 g a b.
    apply is_RInt_ext with (fun y : R => Derive g0 y * f (g0 y)).
    rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
    apply f_equal2.
    apply is_derive_unique.
    apply extension_C1_is_derive.
    by apply Rbar_finite_le, Hx.
    by apply Rbar_finite_le, Hx.
    by apply Derive_correct, Hg.
    apply f_equal.
    apply extension_C1_ext.
    by apply Rbar_finite_le, Hx.
    by apply Rbar_finite_le, Hx.
    have Hg0 : forall x : R, ex_derive g0 x /\ continuity_pt (Derive g0) x.
    move => x ; rewrite /g0 ; split.
    apply extension_C1_ex_derive.
    by left.
    move => y Hay Hyb ; apply Hg.
    split ; by apply Rbar_finite_le.
    apply extension_C1_Derive_cont.
    by left.
    move => y Hay Hyb.
    apply Hg.
    split ; by apply Rbar_finite_le.
    apply Hw.
    by apply Hg0.
    move => x Hx.
    rewrite /g0 extension_C1_ext.
    by apply Hf.
    by apply Rbar_finite_le, Hx.
    by apply Rbar_finite_le, Hx.
    move => x Hx.
    by apply Hg0.
  wlog: f Hf / (forall x, continuity_pt f x) => [Hw | {Hf} Hf].
    case: (continuity_ab_maj g a b (Rlt_le _ _ Hab)) => [ | M HM].
      move => x Hx.
      apply derivable_continuous_pt.
      exists (Derive g x) ; apply Derive_correct.
      by apply Hg.
    case: (continuity_ab_min g a b (Rlt_le _ _ Hab)) => [ | m Hm].
      move => x Hx.
      apply derivable_continuous_pt.
      exists (Derive g x) ; apply Derive_correct.
      by apply Hg.
    have H : g m <= g M.
      apply Hm ; intuition.
    case: (prolongement_C0 f (g m) (g M)) => [ | y Hy | f0 Hf0].
    by [].
    case: (IVT_gen g m M y).
    move => x ; apply derivable_continuous_pt.
    exists (Derive g x) ; apply Derive_correct.
    by apply Hg.
    rewrite /Rmin /Rmax ; case: Rle_dec => //.
    move => x [Hx <-].
    apply Hf ; split.
    apply Rle_trans with (2 := proj1 Hx).
    apply Rmin_case ; intuition.
    apply Rle_trans with (1 := proj2 Hx).
    apply Rmax_case ; intuition.
    replace (RInt f (g a) (g b)) with (RInt f0 (g a) (g b)).
    apply is_RInt_ext with (fun y : R => Derive g y * f0 (g y)).
    rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hc.
    apply f_equal.
    apply Hf0 ; split.
    by apply Hm.
    by apply HM.
    apply Hw.
    move => x Hx ; apply Hf0.
    apply Hf0.
    apply RInt_ext => x Hx.
    apply Hf0 ; split.
    apply Rle_trans with (2 := proj1 Hx).
    apply Rmin_case ; intuition.
    apply Rle_trans with (1 := proj2 Hx).
    apply Rmax_case ; intuition.
  cut (ex_RInt (fun y : R => Derive g y * f (g y)) a b
    /\ RInt (fun y : R => Derive g y * f (g y)) a b = (RInt f (g a) (g b))).
  case => [[If H] <-].
  by rewrite (is_RInt_unique _ _ _ _ H).
  have H : forall x, continuity_pt (fun y : R => Derive g y * f (g y)) x.
    move => x.
    apply continuity_pt_mult.
    by apply Hg.
    apply continuity_pt_comp.
    apply derivable_continuous_pt.
    exists (Derive g x) ; apply Derive_correct.
    by apply Hg.
    by apply Hf.
  assert (H0 : forall a b, ex_RInt (fun y : R => Derive g y * f (g y)) a b).
    move => a0 b0.
    apply ex_RInt_cont => x Hx.
    by apply H.
  split.
  by apply H0.
  case: (fn_eq_Derive_eq (fun b => RInt (fun y : R => Derive g y * f (g y)) a b)
    (fun b => RInt f (g a) (g b)) a b).
  apply continuity_pt_filterlim, (continuity_RInt_0 (fun y : R => Derive g y * f (g y))).
  exists (mkposreal _ Rlt_0_1) => /= y Hy.
  by apply RInt_correct, H0.
  apply continuity_pt_filterlim, (continuity_RInt (fun y : R => Derive g y * f (g y)) a).
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /= y Hy.
  by apply RInt_correct, H0.
  apply (continuity_pt_comp g).
  apply derivable_continuous_pt.
  exists (Derive g a) ; apply Derive_correct.
  by apply Hg.
  apply continuity_pt_filterlim, (continuity_RInt_0 f).
  exists (mkposreal _ Rlt_0_1) => /= y Hy.
  apply RInt_correct, ex_RInt_cont => x Hx.
  by apply Hf.
  apply (continuity_pt_comp g).
  apply derivable_continuous_pt.
  exists (Derive g b) ; apply Derive_correct.
  by apply Hg.
  apply continuity_pt_filterlim, (continuity_RInt f (g a)).
  apply ex_RInt_cont => x Hx.
  by apply Hf.
  exists (mkposreal _ Rlt_0_1) => /= y Hy.
  apply RInt_correct, ex_RInt_cont => x Hx.
  by apply Hf.
  move => x Hx.
  evar (l : R) ; exists l ; unfold l.
  apply (derivable_pt_lim_RInt (fun y : R => Derive g y * f (g y)) a x).
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply H0.
  by apply H.
  move => x Hx.
  evar (l : R) ; exists l ; unfold l.
  apply derivable_pt_lim_comp.
  apply Derive_correct.
  by apply Hg.
  apply (derivable_pt_lim_RInt f (g a) (g x)).
  by apply ex_RInt_cont.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply ex_RInt_cont.
  by apply Hf.
  move => x Hx.
  search_derive.
  unfold l.
  apply (derivable_pt_lim_RInt (fun y : R => Derive g y * f (g y)) a x).
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply H0.
  by apply H.
  apply sym_eq ; search_derive.
  apply derivable_pt_lim_comp.
  apply Derive_correct.
  by apply Hg.
  apply (derivable_pt_lim_RInt f (g a) (g x)).
  by apply ex_RInt_cont.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply ex_RInt_cont.
  by apply Hf.
  by apply Rmult_comm.
  move => x H1.
  rewrite H1 ; intuition.
  apply Rminus_diag_uniq ; ring_simplify.
  move: (H1 a (conj (Rle_refl _) (Rlt_le _ _ Hab))) => {H1}.
  rewrite ?RInt_point Rplus_0_l.
  by apply sym_eq.
Qed.

Lemma RInt_Chasles_bound_comp_l_loc :
  forall f a b x,
  locally x (fun y => ex_RInt (f y) (a x) b) ->
  (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) ->
  continuity_pt a x ->
  locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) b =
    RInt (f x') (a x') b).
Proof.
intros f a b x Hab (eps,Hae) Ca.
move /continuity_pt_locally: Ca => Ca.
generalize (filter_and _ _ (Ca eps) (filter_and _ _ Hab Hae)).
apply filter_imp => {Ca Hae Hab} y [Hy [Hab Hae]].
apply RInt_Chasles with (2 := Hab).
apply ex_RInt_inside with (1 := Hae).
now apply Rlt_le.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
Qed.

Lemma RInt_Chasles_bound_comp_loc :
  forall f a b x,
  locally x (fun y => ex_RInt (f y) (a x) (b x)) ->
  (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) ->
  (exists eps : posreal, locally x (fun y => ex_RInt (f y) (b x - eps) (b x + eps))) ->
  continuity_pt a x ->
  continuity_pt b x ->
  locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) (b x') =
    RInt (f x') (a x') (b x')).
Proof.
intros f a b x Hab (ea,Hae) (eb,Hbe) Ca Cb.
move /continuity_pt_locally: Ca => Ca.
move /continuity_pt_locally: Cb => Cb.
set (e := mkposreal _ (Rmin_stable_in_posreal ea eb)).
generalize (filter_and _ _ (filter_and _ _ (Ca e) (Cb e))
  (filter_and _ _ Hab (filter_and _ _ Hae Hbe))).
apply filter_imp => {Ca Cb Hab Hae Hbe} y [[Hay Hby] [Hab [Hae Hbe]]].
apply RInt_Chasles.
apply ex_RInt_inside with (1 := Hae).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hay).
exact: Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply ex_RInt_Chasles with (1 := Hab).
apply ex_RInt_inside with (1 := Hbe).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hby).
exact: Rmin_r.
Qed.

Lemma derivable_pt_lim_RInt_bound_comp :
  forall f a b da db x,
  ex_RInt f (a x) (b x) ->
  (exists eps : posreal, ex_RInt f (a x - eps) (a x + eps)) ->
  (exists eps : posreal, ex_RInt f (b x - eps) (b x + eps)) ->
  continuity_pt f (a x) ->
  continuity_pt f (b x) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  derivable_pt_lim (fun x => RInt f (a x) (b x)) x (db * f (b x) - da * f (a x)).
Proof.
intros f a b da db x Hi Ia Ib Ca Cb Da Db.
apply is_derive_ext_loc with (fun x0 => comp (fun y => RInt f y (a x)) a x0
  + comp (fun y => RInt f (a x) y) b x0).
(* *)
unfold comp.
apply RInt_Chasles_bound_comp_loc.
by apply filter_forall.
destruct Ia as (d1,H1).
exists d1.
by apply filter_forall.
destruct Ib as (d2,H2).
exists d2.
by apply filter_forall.
apply derivable_continuous_pt.
eexists ; eassumption.
apply derivable_continuous_pt.
eexists ; eassumption.
(* *)
replace (db * f (b x) - da * f (a x)) with (- f(a x) * da + f (b x) * db) by ring.
apply derivable_pt_lim_plus.
apply derivable_pt_lim_comp.
exact Da.
apply derivable_pt_lim_RInt' ; trivial.
apply ex_RInt_point.
apply derivable_pt_lim_comp.
exact Db.
now apply derivable_pt_lim_RInt.
Qed.

(** * Parametric integrals *)

Lemma derivable_pt_lim_param_aux : forall f a b x,
  locally x (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally x (fun y => ex_RInt (fun t => f y t) a b) ->
  ex_RInt (fun t => Derive (fun u => f u t) x) a b ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x.
wlog: a b / a < b => H.
(* *)
destruct (total_order_T a b) as [[Hab|Hab]|Hab].
now apply H.
intros _ _ _ _.
rewrite Hab.
rewrite RInt_point.
apply (is_derive_ext (fun _ => 0)).
intros t.
apply sym_eq.
apply RInt_point.
apply derivable_pt_lim_const.
intros H1 H2 H3 H4.
apply (is_derive_ext (fun u => - RInt (fun t => f u t) b a)).
intros t.
apply RInt_swap.
rewrite -RInt_swap.
apply derivable_pt_lim_opp.
apply H.
exact Hab.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
move: H3 ; apply filter_imp => y H3.
now apply ex_RInt_swap.
now apply ex_RInt_swap.
(* *)
rewrite Rmin_left. 2: now apply Rlt_le.
rewrite Rmax_right. 2: now apply Rlt_le.
intros Df Cdf If IDf.
apply filterdiff_Reals ; split => [ | y Hy].
by apply @is_linear_scal.
rewrite -(is_filter_lim_locally_R _ _ Hy) => {y Hy}.
refine (let Cdf' := uniform_continuity_2d_1d (fun u v => Derive (fun z => f z u) v) a b x _ in _).
intros t Ht eps.
specialize (Cdf t Ht eps).
simpl in Cdf.
destruct Cdf as (d,Cdf).
exists d.
intros v u Hv Hu.
now apply Cdf.
intros eps. clear Cdf.
assert (H': 0 < eps / Rabs (b - a)).
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
apply Rgt_not_eq.
now apply Rgt_minus.
move: (Cdf' (mkposreal _ H')) => {Cdf'} [d1 Cdf].
generalize (filter_and _ _ Df If). move => {Df If} [d2 DIf].
exists (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))) => /= y Hy.
assert (D1: ex_RInt (fun t => f y t) a b).
apply DIf.
apply Rlt_le_trans with (1 := Hy).
apply Rle_trans with (1 := Rmin_r _ _).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
assert (D2: ex_RInt (fun t => f x t) a b).
apply DIf.
apply ball_center.
rewrite -!/(Rminus _ _) -RInt_minus //.
rewrite Rmult_comm.
rewrite Rmult_comm -RInt_scal //.
assert (D3: ex_RInt (fun t => f y t - f x t) a b).
  apply @ex_RInt_minus.
  by apply D1.
  by apply D2.
assert (D4: ex_RInt (fun t => (y - x) * Derive (fun u => f u t) x) a b) by now apply @ex_RInt_scal.
rewrite -RInt_minus //.
assert (D5: ex_RInt (fun t => f y t - f x t - (y - x) * Derive (fun u => f u t) x) a b) by now apply @ex_RInt_minus.
rewrite (RInt_Reals _ _ _ (ex_RInt_Reals_2 _ _ _ D5)).
assert (D6: ex_RInt (fun t => Rabs (f y t - f x t - (y - x) * Derive (fun u => f u t) x)) a b) by now apply ex_RInt_norm.
apply Rle_trans with (1 := RiemannInt_P17 _ (ex_RInt_Reals_2 _ _ _ D6) (Rlt_le _ _ H)).
refine (Rle_trans _ _ _ (RiemannInt_P19 _ (RiemannInt_P14 a b (eps / Rabs (b - a) * Rabs (y - x))) (Rlt_le _ _ H) _) _).
intros u Hu.
destruct (MVT_cor4 (fun t => f t u) x) with (eps := pos_div_2 d2) (b := y) as (z,Hz).
intros z Hz.
apply DIf.
apply Rle_lt_trans with (1 := Hz).
apply: Rlt_eps2_eps.
apply cond_pos.
split ; now apply Rlt_le.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
rewrite (proj1 Hz).
rewrite Rmult_comm.
rewrite -Rmult_minus_distr_l Rabs_mult.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rlt_le.
apply Cdf.
split ; now apply Rlt_le.
apply Rabs_le_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le.
apply cond_pos.
split ; now apply Rlt_le.
apply Rabs_le_between'.
apply Rle_trans with (1 := proj2 Hz).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite RiemannInt_P15.
rewrite Rabs_pos_eq.
right.
field.
apply Rgt_not_eq.
now apply Rgt_minus.
apply Rge_le.
apply Rge_minus.
now apply Rgt_ge.
Qed.


Lemma derivable_pt_lim_param : forall f a b x,
  locally x (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally x (fun y => ex_RInt (fun t => f y t) a b) ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply derivable_pt_lim_param_aux; try easy.
apply ex_RInt_Reals_1.
clear H1 H3.
wlog: a b H2 / a < b => H.
case (total_order_T a b).
intro Y; case Y.
now apply H.
intros Heq; rewrite Heq.
apply RiemannInt_P7.
intros  Y.
apply RiemannInt_P1.
apply H.
intros; apply H2.
rewrite Rmin_comm Rmax_comm.
exact H0.
exact Y.
rewrite Rmin_left in H2.
2: now left.
rewrite Rmax_right in H2.
2: now left.
apply continuity_implies_RiemannInt.
now left.
intros y Hy eps Heps.
destruct (H2 _ Hy (mkposreal eps Heps)) as (d,Hd).
simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist; simpl.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
Qed.

Lemma derivable_pt_lim_RInt_param_bound_comp_aux1: forall f a x,
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        a x-eps <= t <= a x+eps ->
        ex_derive (fun u : R => f u t) x0)) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->

  continuity_2d_pt
     (fun u v : R => Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) x (a x).
Proof.
intros f a x (d1,(d2,Ia)) (d3,(d4,Df)) Cdf e.
assert (J1:(continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x (a x)))
   by now apply locally_2d_singleton in Cdf.
destruct Cdf as (d5,Cdf).
destruct (J1 (mkposreal _ Rlt_0_1)) as (d6,Df1); simpl in Df1.
assert (J2: 0 < e / (Rabs (Derive (fun z : R => f z (a x)) x)+1)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
exists (mkposreal _ (Rmin_stable_in_posreal
                  (mkposreal _ (Rmin_stable_in_posreal
                        d1
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d2) d3))))
                  (mkposreal _ (Rmin_stable_in_posreal
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d4) d5))
                       (mkposreal _ (Rmin_stable_in_posreal d6 (mkposreal _ J2))))))).
simpl; intros u v Hu Hv.
rewrite (Derive_ext (fun z : R => RInt (fun t : R => f z t) (a x) (a x)) (fun z => 0)).
2: intros t; apply RInt_point.
replace (Derive (fun _ : R => 0) x) with 0%R.
2: apply sym_eq, is_derive_unique, derivable_pt_lim_const.
rewrite Rminus_0_r.
replace (Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) with
  (RInt (fun z => Derive (fun u => f u z) u) v (a x)).
(* *)
apply Rle_lt_trans with (Rabs (a x -v) *
   (Rabs (Derive (fun z : R => f z (a x)) x) +1)).
apply RInt_le_const.
apply ex_RInt_cont.
intros y Hy eps Heps.
assert (Y1:(Rabs (u - x) < d5)).
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
assert (Y2:(Rabs (y - a x) < d5)).
apply Rle_lt_trans with (Rabs (v-a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
destruct (Cdf u y Y1 Y2 (mkposreal eps Heps)) as (d,Hd); simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
intros t Ht.
apply Rplus_le_reg_r with (-Rabs (Derive (fun z : R => f z (a x)) x)).
apply Rle_trans with (1:=Rabs_triang_inv _ _).
ring_simplify.
left; apply Df1.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
replace (a x -v) with (-(v - a x)) by ring; rewrite Rabs_Ropp.
apply Rlt_le_trans with ((e / (Rabs (Derive (fun z : R => f z (a x)) x) + 1))
  * (Rabs (Derive (fun z : R => f z (a x)) x) + 1)).
apply Rmult_lt_compat_r.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
right; field.
apply sym_not_eq, Rlt_not_eq.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
(* *)
apply sym_eq, is_derive_unique.
apply derivable_pt_lim_param.
exists (pos_div_2 d4).
intros y Hy t Ht.
apply Df.
rewrite (double_var d4).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
by apply Hy.
apply (proj1 (Rabs_le_between' t (a x) d3)).
apply Rle_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
intros t Ht.
apply Cdf.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
exists (pos_div_2 d2).
intros y Hy.
apply ex_RInt_inside with (a x) d1.
apply Ia.
rewrite (double_var d2).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Hy.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
Qed.



Lemma derivable_pt_lim_RInt_param_bound_comp_aux2 :
  forall f a b x da,
  (locally x (fun y => ex_RInt (fun t => f y t) (a x) b)) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) ->
  derivable_pt_lim a x da ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
        ex_derive (fun u : R => f u t) x0)) ->
  (forall t : R,
          Rmin (a x) b <= t <= Rmax (a x) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
   continuity_pt (fun t => f x t) (a x) ->

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) b) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) b+(-f x (a x))*da).
Proof.
intros f a b x da Hi (d0,Ia) Da Df Cdf1 Cdf2 Cfa.
rewrite Rplus_comm.
apply is_derive_ext_loc with (fun x0 => RInt (fun t : R => f x0 t) (a x0) (a x) + RInt (fun t : R => f x0 t) (a x) b).
apply RInt_Chasles_bound_comp_l_loc.
exact Hi.
now exists d0.
apply derivable_continuous_pt.
eexists.
apply Da.
apply derivable_pt_lim_plus.
(* *)
replace (- f x (a x) * da) with (0*1+- f x (a x) * da) by ring.
apply derivable_pt_lim_comp_2d with
   (f1 := fun x0 y => RInt (fun t : R => f x0 t) y (a x)).
replace 0 with (Derive (fun u => RInt (fun t : R => f u t) (a x) (a x)) x).
apply derivable_differentiable_pt_lim.
(* . *)
destruct Df as (d1,(d2,Df)).
destruct Cdf2 as (d3,Cdf2).
destruct Ia as (d4,Ia).
exists (mkposreal _ (Rmin_stable_in_posreal
                (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2)))
                (mkposreal _ (Rmin_stable_in_posreal d3
                            (mkposreal _ (Rmin_stable_in_posreal d0 (pos_div_2 d4))))))).
simpl; intros u v Hu Hv.
eexists; eapply derivable_pt_lim_param.
exists (pos_div_2 d2).
intros y Hy t Ht.
apply Df.
rewrite (double_var d2).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
by apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (a x - d1).
apply Rmin_l.
apply Rmin_glb.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x + d1); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (a x + d1).
apply Rmax_lub.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x); ring_simplify.
left; apply cond_pos.
apply Rmax_l.
intros t Ht.
apply Cdf2.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
exists (pos_div_2 d4).
intros y Hy.
apply ex_RInt_inside with (a x) d0.
apply Ia.
rewrite (double_var d4).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
by apply Hy.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
(* . *)
apply derivable_pt_lim_RInt'.
apply ex_RInt_point.
apply locally_singleton in Ia.
now exists d0.
exact Cfa.
(* . *)
apply derivable_pt_lim_RInt_param_bound_comp_aux1; try easy.
exists d0; exact Ia.
destruct Df as (d,Hd).
exists d.
move: Hd ; apply filter_imp.
intros y H t Ht.
apply H.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rmax_l.
(* . *)
apply is_derive_unique.
apply is_derive_ext with (fun _ => 0).
intros t; apply sym_eq, RInt_point.
apply derivable_pt_lim_const.
(* . *)
apply derivable_pt_lim_id.
exact Da.
(* *)
apply derivable_pt_lim_param.
destruct Df as (d,Df).
move: Df ; apply filter_imp.
intros y Hy t Ht; apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x+d); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
exact Cdf1.
exact Hi.
Qed.

Lemma derivable_pt_lim_RInt_param_bound_comp_aux3 :
  forall f a b x db,
  (locally x (fun y => ex_RInt (fun t => f y t) a (b x))) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps))) ->
  derivable_pt_lim b x db ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        Rmin a (b x-eps) <= t <= Rmax a (b x+eps) ->
        ex_derive (fun u : R => f u t) x0)) ->
  (forall t : R,
          Rmin a (b x) <= t <= Rmax a (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (b x) ->

 derivable_pt_lim (fun x => RInt (fun t => f x t) a (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db).
Proof.
intros f a b x db If Ib Db Df Cf1 Cf2 Cfb.
apply is_derive_ext with (fun x0 => - RInt (fun t : R => f x0 t) (b x0) a).
intros t; apply RInt_swap.
replace (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db) with
      (- ((RInt (fun t : R => Derive (fun u : R => f u t) x) (b x) a) + - f x (b x)*db)).
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt_param_bound_comp_aux2; try easy.
move: If ; apply filter_imp.
intros y H.
now apply ex_RInt_swap.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
now rewrite Rmin_comm Rmax_comm.
intros t Ht.
apply Cf1.
now rewrite Rmin_comm Rmax_comm.
rewrite <- RInt_swap.
ring.
Qed.


Lemma derivable_pt_lim_RInt_param_bound_comp :
 forall f a b x da db,
  (locally x (fun y => ex_RInt (fun t => f y t) (a x) (b x))) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps))) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) (b x -eps) <= t <= Rmax (a x+eps) (b x+eps) ->
        ex_derive (fun u : R => f u t) x0)) ->
  (forall t : R,
          Rmin (a x) (b x) <= t <= Rmax (a x) (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
 (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (a x) ->   continuity_pt (fun t => f x t) (b x) ->

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) (b x)+(-f x (a x))*da+(f x (b x))*db).
Proof.
intros f a b x da db If Ifa Ifb Da Db Df Cf Cfa Cfb Ca Cb.
apply is_derive_ext_loc with (fun x0 : R => RInt (fun t : R => f x0 t) (a x0) (a x)
    + RInt (fun t : R => f x0 t) (a x) (b x0)).
apply RInt_Chasles_bound_comp_loc ; trivial.
apply derivable_continuous_pt.
eexists.
apply Da.
apply derivable_continuous_pt.
eexists.
apply Db.
replace (RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (b x) +
   - f x (a x) * da + f x (b x) * db) with
   ((RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (a x) + - f x (a x) * da) +
      (RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (b x) + f x (b x)*db)).
apply derivable_pt_lim_plus.
(* *)
apply derivable_pt_lim_RInt_param_bound_comp_aux2; try easy.
exists (mkposreal _ Rlt_0_1).
intros y Hy.
apply ex_RInt_point.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
intros t Ht.
apply Cf.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
now right.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
now right.
(* *)
apply derivable_pt_lim_RInt_param_bound_comp_aux3; try easy.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
rewrite RInt_point.
ring.
Qed.
