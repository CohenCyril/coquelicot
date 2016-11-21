(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rbar Hierarchy RInt Lim_seq Continuity Derive.
Require Import Rcomplements RInt_analysis.

(** This file describes improper integrals, such as integrals with an
infinity endpoint or integrals of a function with a singularity. A few
properties are given: Chasles, operations, composition, derivation.*)

Open Scope R_scope.

(** * Improper Riemann integral *)

Section RInt_gen.

Context {V : NormedModule R_AbsRing}.

Definition is_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) (l : V) :=
  exists (If : R * R -> V),
   filter_prod Fa Fb (fun ab => is_RInt f (fst ab) (snd ab) (If ab))
    /\ filterlim If (filter_prod Fa Fb) (locally l).
Definition ex_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) :=
  exists l : V, is_RInt_gen f Fa Fb l.

Definition is_RInt_gen_at_point f a b l :
  is_RInt_gen f (at_point a) (at_point b) l
    <-> is_RInt f a b l.
Proof.
  split.
  - case => If [[P Q Pa Qb Hif] Hl].
    apply filterlim_locally => eps.
    eapply filter_imp.
    intros x Hx.
    rewrite (double_var eps).
    apply ball_triangle with (If (a,b)).
    apply (fun H => proj1 (filterlim_locally _ _) H (pos_div_2 eps)) in Hl.
    case: Hl => P' Q' P'a Q'b Hl.
    apply Hl.
    apply P'a => ? ; apply ball_center.
    apply Q'b => ? ; apply ball_center.
    by apply Hx.
    apply Hif.
    apply Pa => ? ; apply ball_center.
    apply Qb => ? ; apply ball_center.
    by apply (locally_ball _ (pos_div_2 eps)).
  - intros Hl.
    exists (fun _ => l) ; split.
    exists (fun x => x = a) (fun x => x = b).
    intros x H. now apply eq_sym, ball_eq.
    intros x H. now apply eq_sym, ball_eq.
    by move => x y -> ->.
    by apply filterlim_const.
Qed.

End RInt_gen.

(** * Basic properties of integrals *)

Section Property.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (l : V) :
  filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab)
                               -> f x = g x) ->
  is_RInt_gen f Fa Fb l -> is_RInt_gen g Fa Fb l.
Proof.
  intros Heq [If [Hf Hl]].
  exists If ; split.
  generalize (filter_and _ _ Heq Hf) ; clear Heq Hf.
  apply filter_imp.
  intros x [Heq Hf].
  eapply is_RInt_ext.
  by apply Heq.
  by apply Hf.
  by apply Hl.
Qed.

Lemma is_RInt_gen_point (f : R -> V) (a : R) :
  is_RInt_gen f (at_point a) (at_point a) zero.
Proof.
  apply is_RInt_gen_at_point.
  by apply is_RInt_point.
Qed.

Lemma is_RInt_gen_swap {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fb Fa l -> is_RInt_gen f Fa Fb (opp l).
Proof.
  case => If [[P Q /= HP HQ Hif] Hl].
  exists (fun x => opp (If (snd x,fst x))) ; split.
  exists Q P.
  exact: HQ.
  exact: HP.
  move => /= a b Qa Pb.
  apply is_RInt_swap.
  by apply Hif.
  eapply filterlim_comp, filterlim_opp.
  apply filterlim_locally => eps.
  apply (fun H => proj1 (filterlim_locally _ _) H eps) in Hl.
  clear -Hl ; case: Hl => P Q /= HP HQ Hif.
  exists Q P.
  exact: HQ.
  exact: HP.
  move => /= a b Qa Pb.
  by apply Hif.
Qed.

Lemma is_RInt_gen_Chasles {Fa Fc : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFc : Filter Fc}
  (f : R -> V) (b : R) (l1 l2 : V) :
  is_RInt_gen f Fa (at_point b) l1 -> is_RInt_gen f (at_point b) Fc l2
  -> is_RInt_gen f Fa Fc (plus l1 l2).
Proof.
  case => If1 [[P1 Q1 /= HP1 HQ1 Hf1] Hl1].
  case => If2 [[P2 Q2 /= HP2 HQ2 Hf2] Hl2].
  exists (fun x => plus (If1 (fst x,b)) (If2 (b,snd x))) ; split.
  exists P1 Q2.
  exact: HP1.
  exact: HQ2.
  move => /= a c P1a Q2c.
  apply is_RInt_Chasles with b.
  apply Hf1 => //.
  apply HQ1 => ? ; apply ball_center.
  apply Hf2 => //.
  apply HP2 => ? ; apply ball_center.
  eapply filterlim_comp_2, filterlim_plus.
  eapply filterlim_comp , Hl1.
  clear -FFa FFc.
  intros P [P0 P1 P0a P1b HP].
  unfold filtermap.
  exists P0 (fun _ => True).
  exact: P0a.
  exact: filter_true.
  intros a c Q0a _ ; simpl.
  apply HP.
  by apply Q0a.
  apply P1b => ? ; apply ball_center.
  eapply filterlim_comp , Hl2.
  clear -FFa FFc.
  intros P [P0 P1 P0a P1b HP].
  unfold filtermap.
  exists (fun _ => True) P1.
  exact: filter_true.
  exact: P1b.
  intros a c _ Q0c ; simpl.
  apply HP.
  apply P0a => ? ; apply ball_center.
  by apply Q0c.
Qed.

End Property.

(** * Composition *)

Section Compose.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_gen_comp_opp {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f (filtermap opp Fa) (filtermap opp Fb) l ->
  is_RInt_gen (fun y => opp (f (- y))) Fa Fb l.
Proof.
  case => If [Hf Hl].
  exists (fun x => If (opp x)) ; split.
  case: Hf => P Q ;
  unfold filtermap => Pa Qb H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply is_RInt_comp_opp, H.
  eapply filterlim_comp, Hl.
  intros P [Q1 Q2 Q1a Q2b H].
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply H.
Qed.

Lemma is_RInt_gen_comp_lin {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (u v : R) (l : V) :
  is_RInt_gen f (filtermap (fun a => u * a + v) Fa) (filtermap (fun b => u * b + v) Fb) l
    -> is_RInt_gen (fun y => scal u (f (u * y + v))) Fa Fb l.
Proof.
  case => If [Hf Hl].
  exists (fun x => If (plus (scal u x) (v,v))) ; split.
  case: Hf => P Q ;
  unfold filtermap => Pa Qb H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply is_RInt_comp_lin, H.
  eapply filterlim_comp, Hl.
  intros P [Q1 Q2 Q1a Q2b H].
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply H.
Qed.

End Compose.

(** * Operations *)

Section Operations.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_gen_scal {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (k : R) (l : V) :
  is_RInt_gen f Fa Fb l ->
  is_RInt_gen (fun y => scal k (f y)) Fa Fb (scal k l).
Proof.
  case => If [Hf Hl].
  exists (fun x => scal k (If x)) ; split.
  move: Hf ; apply filter_imp => x.
  by apply is_RInt_scal.
  by eapply filterlim_comp, @filterlim_scal_r.
Qed.

Lemma is_RInt_gen_opp {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fa Fb l ->
  is_RInt_gen (fun y => opp (f y)) Fa Fb (opp l).
Proof.
  case => If [Hf Hl].
  exists (fun x => opp (If x)) ; split.
  move: Hf ; apply filter_imp => x.
  by apply is_RInt_opp.
  by eapply filterlim_comp, filterlim_opp.
Qed.

Lemma is_RInt_gen_plus {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (lf lg : V) :
  is_RInt_gen f Fa Fb lf ->
  is_RInt_gen g Fa Fb lg ->
  is_RInt_gen (fun y => plus (f y) (g y)) Fa Fb (plus lf lg).
Proof.
  case => If [Hf Hlf].
  case => Ig [Hg Hlg].
  exists (fun x => plus (If x) (Ig x)) ; split.
  generalize (filter_and _ _ Hf Hg) ;
  apply filter_imp => {Hf Hg} x [Hf Hg].
  by apply is_RInt_plus.
  by eapply filterlim_comp_2, filterlim_plus.
Qed.

Lemma is_RInt_gen_minus {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (a b : R) (lf lg : V) :
  is_RInt_gen f Fa Fb lf ->
  is_RInt_gen g Fa Fb lg ->
  is_RInt_gen (fun y => minus (f y) (g y)) Fa Fb (minus lf lg).
Proof.
  intros Hf Hg.
  apply is_RInt_gen_plus.
  by [].
  by apply is_RInt_gen_opp.
Qed.

End Operations.

Lemma RInt_gen_norm {V : NormedModule R_AbsRing} {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) (g : R -> R) (lf : V) (lg : R) :
  filter_prod Fa Fb (fun ab => fst ab <= snd ab)
  -> filter_prod Fa Fb (fun ab => forall x, fst ab <= x <= snd ab -> norm (f x) <= g x)
  -> is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg
    -> norm lf <= lg.
Proof.
  intros Hab Hle.
  case => If [Hf Hlf].
  case => Ig [Hg Hlg].
  apply (filterlim_le (F := filter_prod Fa Fb) (fun x => norm (If x)) Ig (norm lf) lg).
  generalize (filter_and _ _ Hab Hle) => {Hab Hle} H.
  generalize (filter_and _ _ H Hf) => {H Hf} H.
  generalize (filter_and _ _ H Hg) => {H Hg}.
  apply filter_imp => x [[[Hab Hle] Hf] Hg].
  eapply norm_RInt_le ; try by eassumption.
  by eapply filterlim_comp, filterlim_norm.
  by apply Hlg.
Qed.

Lemma is_RInt_gen_Derive {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb}
  (f : R -> R) (la lb : R) :
  filter_prod Fa Fb
    (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> ex_derive f x)
  -> filter_prod Fa Fb
    (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> continuous (Derive f) x)
  -> filterlim f Fa (locally la) -> filterlim f Fb (locally lb)
  -> is_RInt_gen (Derive f) Fa Fb (lb - la).
Proof.
  intros Df Cf Lfa Lfb.
  exists (fun ab => f (snd ab) - f (fst ab)) ; split.
  generalize (filter_and _ _ Df Cf) => {Df Cf}.
  apply filter_imp => [[a b]] /= [Df Cf].
  apply is_RInt_derive.
  intros ; by apply Derive_correct, Df.
  by apply Cf.
  rewrite /Rminus.
  eapply filterlim_comp_2, (filterlim_plus lb (- la)).
  eapply filterlim_comp, Lfb.
  by apply filterlim_snd.
  eapply filterlim_comp, @filterlim_opp.
  eapply filterlim_comp, Lfa.
  by apply filterlim_fst.
Qed.
