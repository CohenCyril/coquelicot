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

Require Import Reals ssreflect.
Require Import Rbar Rcomplements Markov.

(** This file gives properties of (least) upper and (greatest) lower
bounds, especially in [Rbar].
- There are links between our bounds on [Rbar] and those of the
standard library on [R]: for example Lemma [Rbar_ub_R_ub] between our
[Rbar_is_upper_bound] and the standard library [is_upper_bound].
- From [Markov]'s principle, we deduce the construction of a lub (and
of a glb) in [Rbar] from any non-empty set of reals: see Lemma
[ex_lub_Rbar_ne].  *)



Open Scope R_scope.

(** * Upper and lower bounds *)

(** ** For sets in Rbar *)

Definition Rbar_is_upper_bound (E : Rbar -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le x l.

Definition Rbar_is_lower_bound (E : Rbar -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le l x.

Lemma Rbar_ub_lb (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_upper_bound (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_lower_bound E l.
Proof.
  split => Hl x Hx.
  apply Rbar_opp_le.
  apply Hl.
  by rewrite Rbar_opp_involutive.
  apply Rbar_opp_le.
  rewrite Rbar_opp_involutive.
  by apply Hl.
Qed.

Lemma Rbar_lb_ub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lower_bound (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_upper_bound E l.
Proof.
  split => Hl x Hx.
  apply Rbar_opp_le.
  apply Hl.
  by rewrite Rbar_opp_involutive.
  apply Rbar_opp_le.
  rewrite Rbar_opp_involutive.
  by apply Hl.
Qed.

(** Basic properties *)

Lemma Rbar_ub_p_infty (E : Rbar -> Prop) :
  Rbar_is_upper_bound E p_infty.
Proof.
  now intros [x| |] Hx.
Qed.

Lemma Rbar_lb_m_infty (E : Rbar -> Prop) :
  Rbar_is_lower_bound E m_infty.
Proof.
  easy.
Qed.

Lemma Rbar_ub_Finite (E : Rbar -> Prop) (l : R) :
  Rbar_is_upper_bound E l ->
    is_upper_bound (fun (x : R) => E x) l.
Proof.
  intros H x Ex.
  now apply (H (Finite x)).
Qed.

Lemma Rbar_lb_Finite (E : Rbar -> Prop) (l : R) :
  Rbar_is_lower_bound E (Finite l) -> is_upper_bound (fun x => E (Finite (- x))) (- l).
Proof.
  intros H x Ex.
  apply Ropp_le_cancel ; rewrite Ropp_involutive ;
  now apply (H (Finite (-x))).
Qed.

Lemma Rbar_ub_m_infty (E : Rbar -> Prop) :
  Rbar_is_upper_bound E m_infty -> forall x, E x -> x = m_infty.
Proof.
  intros H [x| |] Hx ;
  now specialize (H _ Hx).
Qed.

Lemma Rbar_lb_p_infty (E : Rbar -> Prop) :
  Rbar_is_lower_bound E p_infty -> (forall x, E x -> x = p_infty).
Proof.
  intros H x ;
  case x ; auto ; clear x ; [intros x| ] ; intros Hx.
  case (H _ Hx) ; simpl ; intuition.
  case (H _ Hx) ; simpl ; intuition.
Qed.

Lemma Rbar_lb_le_ub (E : Rbar -> Prop) (l1 l2 : Rbar) : (exists x, E x) ->
  Rbar_is_lower_bound E l1 -> Rbar_is_upper_bound E l2 -> Rbar_le l1 l2.
Proof.
  intros (x, Hex) Hl Hu ;
  apply Rbar_le_trans with (y := x) ; [apply Hl | apply Hu] ; auto.
Qed.

Lemma Rbar_lb_eq_ub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lower_bound E l -> Rbar_is_upper_bound E l -> forall x, E x -> x = l.
Proof.
  intros Hl Hu x Hx.
  apply Rbar_le_antisym ; [apply Hu | apply Hl] ; auto.
Qed.

(** Decidability *)

Lemma Rbar_ub_dec (E : Rbar -> Prop) (Hp : ~ E p_infty) :
  {M : R | Rbar_is_upper_bound E M}
    + {(forall (M : R), ~Rbar_is_upper_bound E M)}.
Proof.
  set (G n := fun x => x = 0 \/ (E (Finite x) /\ x <= INR n)).
  assert (Hne : (forall n, exists x, G n x)).
    intro n ; exists 0 ; left ; intuition.
  assert (Hub : (forall n, bound (G n))).
    intro n ; exists (INR n) ; intros x Hx ; destruct Hx as [Hx|Hx].
    rewrite Hx ; apply pos_INR.
    apply Hx.
  set (g n := projT1 (completeness _ (Hub n) (Hne n))).
  cut ({N : nat | forall n, (g n <= INR N)} + {(forall N, exists n, (INR N < g n))}).
  intro H ; destruct H as[(N, H) | H].
  left ; exists (INR N) ; intros x Hx ; destruct x as [x | | ] ; intuition.
  case (Rlt_le_dec 0 x) ; intro Hx0.
  apply Rle_trans with (2 := H (S (nfloor1 _ Hx0))) ; clear H ;
  unfold nfloor1 ; case (nfloor1_ex _ _) ; simpl ; intros n Hn ;
  unfold g ; case (completeness _ _ _) ; intros l (Hl, Hl') ; apply Hl ;
  right ; intuition ; rewrite S_INR ; apply H0.
  apply Rle_trans with (1 := Hx0), pos_INR.
  easy.
  right ; intro M ; case (Rlt_le_dec 0 M) ; intro Hm0.
  case (H (S (nfloor1 M Hm0))) ; clear H ; intros n Hn.
  contradict Hn.
  unfold nfloor1 ; case (nfloor1_ex _ _) ; intros m Hm ; simpl projT1.
  rewrite S_INR ; apply Rle_not_lt, Rle_trans with (2 := proj2 Hm).
  unfold g ; case (completeness _ _ _) ; simpl ; intros x (Hx, Hx').
  apply Hx' ; intros x0 Hx0 ; case Hx0 ; clear Hx0 ; intros Hx0.
  rewrite Hx0 ; apply Rlt_le, Hm0.
  apply (Hn (Finite x0)), Hx0.
  case (H O) ; clear H ; intros n Hn ; contradict Hn.
  unfold g ; case (completeness _ _ _) ; simpl ; intros m (Hm, Hm').
  apply Rle_not_lt, Hm' ; intros x Hx ; case Hx ; clear Hx ; intro Hx.
  apply Req_le, Hx.
  apply Rle_trans with (2 := Hm0), (Hn (Finite x)), Hx.
  cut ({n : nat | forall n0 : nat, g n0 <= INR n} +
  {(forall n : nat, ~ (forall n0 : nat, g n0 <= INR n))}).
  intro H ; destruct H as [(N, H)|H].
  left ; exists N ; auto.
  right ; intro N ; generalize (H N) ; clear H ; intro H.
  apply Markov_cor1.
  intro n ; apply Rlt_dec.
  contradict H ; intro n ; apply Rnot_lt_le, H.
  apply (Markov (fun N => forall n : nat, g n <= INR N)).
  intro N.
  cut ({n : nat | INR N < g n} + {(forall n : nat, ~ INR N < g n)}).
  intro H ; destruct H as [(n, H)|H].
  right ; contradict H ; apply Rle_not_lt, H.
  left ; intro n ; apply Rnot_lt_le, H.
  apply (Markov (fun n => INR N < g n)).
  intro n ; apply Rlt_dec.
Qed.

Lemma Rbar_lb_dec (E : Rbar -> Prop) (Hm : ~ E m_infty) :
  {M : R | Rbar_is_lower_bound E (Finite M)}
    + {(forall M, ~Rbar_is_lower_bound E (Finite M))}.
Proof.
  destruct (Rbar_ub_dec (fun x => E (Rbar_opp x)) Hm) as [(M, H)|H].
  left ; exists (-M).
  apply Rbar_ub_lb ; simpl ; rewrite (Ropp_involutive M) ; auto.
  right ; intro M ; generalize (H (-M)) ; clear H ; intro H ; contradict H ;
  apply (Rbar_ub_lb E (Finite M)) ; auto.
Qed.

(** Order *)

Lemma Rbar_is_ub_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_upper_bound E2 l) -> (Rbar_is_upper_bound E1 l).
Proof.
  intros Hs Hl x Ex ; apply Hl, Hs ; auto.
Qed.

Lemma Rbar_is_lb_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_lower_bound E2 l) -> (Rbar_is_lower_bound E1 l).
Proof.
  intros Hs Hl x Ex ; apply Hl, Hs ; auto.
Qed.

(** ** Complements for sets in R *)

(** Links with the standard library *)

Definition is_lower_bound (E : R -> Prop) (l : R) :=
  forall x, E x -> l <= x.

Lemma Rbar_ub_R_ub (E : R -> Prop) (l : R) :
  Rbar_is_upper_bound (fun x => is_finite x /\ E x) l
  <-> is_upper_bound E l.
Proof.
  split => [H x Hx | H x [<- Hx]] ; apply (H (Finite x)) => //.
Qed.

Lemma Rbar_lb_R_lb (E : R -> Prop) (l : R) :
  Rbar_is_lower_bound (fun x => is_finite x /\ E x) (Finite l)
  <-> is_lower_bound E l.
Proof.
  split => [H x Hx | H x [<- Hx]] ; apply (H (Finite x)) => //.
Qed.

Lemma u_bound_dec (E : R -> Prop) :
  {l : R | is_upper_bound E l} + {(forall (l : R), ~ is_upper_bound E l)}.
Proof.
  case: (Rbar_ub_dec (fun x => is_finite x /\ E x)).
  by case.
  case => l Hl ; left ; exists l ; by apply Rbar_ub_R_ub.
  move => H ; right => l Hl ; eapply H ; apply Rbar_ub_R_ub, Hl.
Qed.
Lemma l_bound_dec (E : R -> Prop) :
  {l : R | is_lower_bound E l} +
    {(forall l, ~ is_lower_bound E l)}.
Proof.
  case: (Rbar_lb_dec (fun x => is_finite x /\ E x)).
  by case.
  case => M Hub ; left ; exists M ; by apply Rbar_lb_R_lb.
  move => H ; right => l Hl ; eapply H ; apply Rbar_lb_R_lb, Hl.
Qed.


(** New upper and lower bound *)

Definition is_ub_Rbar (E : R -> Prop) (l : Rbar) :=
  forall (x : R), E x -> Rbar_le x l.
Definition is_lb_Rbar (E : R -> Prop) (l : Rbar) :=
  forall (x : R), E x -> Rbar_le l x.

Lemma is_ub_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_ub_Rbar E l <-> Rbar_is_upper_bound (fun x => is_finite x /\ E x) l.
Proof.
  split => [H x [<- Hx] | H x Hx] ; apply H => // ;
  by exists x.
Qed.
Lemma is_lb_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_lb_Rbar E l <-> Rbar_is_lower_bound (fun x => is_finite x /\ E x) l.
Proof.
  split => [H x [<- Hx] | H x Hx] ; apply H => // ;
  by exists x.
Qed.

(** Order *)

Lemma is_ub_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_ub_Rbar E1 l -> is_ub_Rbar E2 l.
Proof.
  move => H ub1 x Hx.
  apply: ub1 ; by apply: H.
Qed.
Lemma is_lb_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_lb_Rbar E1 l -> is_lb_Rbar E2 l.
Proof.
  move => H ub1 x Hx.
  apply: ub1 ; by apply: H.
Qed.

(** * Least Upper Bound and Greatest Lower Bound *)

(** ** For sets in Rbar *)

(** Definitions *)

Definition Rbar_is_lub (E : Rbar -> Prop) (l : Rbar) :=
  Rbar_is_upper_bound E l /\
    (forall b : Rbar, Rbar_is_upper_bound E b -> Rbar_le l b).
Definition Rbar_is_glb (E : Rbar -> Prop) (l : Rbar) :=
  Rbar_is_lower_bound E l /\
    (forall b : Rbar, Rbar_is_lower_bound E b -> Rbar_le b l).

Lemma Rbar_lub_glb (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lub (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_glb E l.
Proof.
  split ; [intros (ub, lub) | intros (lb, glb)] ; split.
  apply Rbar_ub_lb ; auto.
  intros b Hb ; generalize (lub _ (proj2 (Rbar_ub_lb _ _) Hb)) ; apply Rbar_opp_le.
  apply Rbar_lb_ub ; intros x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply lb.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply glb, Rbar_ub_lb ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

Lemma Rbar_glb_lub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_glb (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_lub E l.
Proof.
  split ; [ intros (lb, glb) | intros (ub, lub)] ; split.
  apply Rbar_lb_ub ; auto.
  intros b Hb ; generalize (glb _ (proj2 (Rbar_lb_ub _ _) Hb)) ; apply Rbar_opp_le.
  apply Rbar_ub_lb ; intro x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply ub.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply lub, Rbar_lb_ub ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

(** Existence *)

Lemma Rbar_ex_lub_ne (E : Rbar -> Prop) : {E p_infty} + {~ E p_infty} ->
  (exists (x : R), E x) -> {l : Rbar | Rbar_is_lub E l}.
Proof.
  intros Hp Hex ; destruct Hp as [Hp|Hp].
(* E p_infty *)
  exists p_infty ; split.
  apply Rbar_ub_p_infty.
  intros b ; destruct b as [b | | ] ; intro ub.
  apply (ub _ Hp).
  easy.
  apply (ub _ Hp).
(* ~ E p_infty *)
  case (Rbar_ub_dec _ Hp).
(* bound E *)
  intros (M, HM) ; case (completeness (fun x => E (Finite x))) ; intuition.
  exists M ; apply Rbar_ub_Finite, HM.
  rename x into l ; destruct i as (ub,lub).
  exists (Finite l) ; split.
  intro x ; case x ; clear x ; [intro x | | ] ; intro Hx.
  now apply ub.
  generalize (Hp Hx) ; intuition.
  easy.
  intro b ; destruct b as [b | | ] ; intro Hb.
  apply lub, Rbar_ub_Finite, Hb.
  easy.
  generalize (Rbar_ub_m_infty _ Hb) ; clear Hb ; intro Hb.
  case Hex ; intros x Hx.
  discriminate (Hb _ Hx).
(* ~ bound E *)
  intro H ; exists p_infty ; split.
  apply Rbar_ub_p_infty.
  intro b ; destruct b as [b | | ] ; intro Hb.
  now contradict Hb.
  easy.
  case Hex ; intros x Hx.
  generalize (Hb _ Hx) ; clear Hb Hx ; intro Hb.
  contradict Hb ; apply Rbar_lt_not_le ; simpl ; auto.
Qed.

Lemma Rbar_ex_glb_ne (E : Rbar -> Prop) : {E m_infty} + {~ E m_infty} ->
  (exists (x : R), E x) -> {l : Rbar | Rbar_is_glb E l}.
Proof.
  intros Hm Hex ;
  case (Rbar_ex_lub_ne (fun x => E (Rbar_opp x))) ; auto.
  case Hex ; clear Hex ; intros x Hx ; exists (-x) ; simpl ; rewrite Ropp_involutive ; auto.
  intros l Hl ; exists (Rbar_opp l) ;
  apply Rbar_lub_glb ; rewrite Rbar_opp_involutive ; auto.
Qed.

(** Functions *)

Definition Rbar_lub_ne (E : Rbar -> Prop) (Hp : {E p_infty} + {~ E p_infty})
  (Hex : exists (x : R), E x) := projT1 (Rbar_ex_lub_ne E Hp Hex).
Definition Rbar_glb_ne (E : Rbar -> Prop) (Hp : {E m_infty} + {~ E m_infty})
  (Hex : exists (x : R), E x) := projT1 (Rbar_ex_glb_ne E Hp Hex).

Lemma Rbar_opp_glb_lub (E : Rbar -> Prop) Hp Hm Hex1 Hex2 :
  Rbar_glb_ne (fun x => E (Rbar_opp x)) Hm Hex1 = Rbar_opp (Rbar_lub_ne E Hp Hex2).
Proof.
  unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne _ _ _) ; simpl ; intros g [Hg Hg'] ;
  unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne _ _ _) ; simpl ; intros l [Hl Hl'] ;
  apply Rbar_le_antisym.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hl', Rbar_lb_ub ;
  rewrite Rbar_opp_involutive ; auto.
  apply Hg', Rbar_lb_ub ; auto.
Qed.
Lemma Rbar_opp_lub_glb (E : Rbar -> Prop) Hp Hm Hex1 Hex2 :
  Rbar_lub_ne (fun x => E (Rbar_opp x)) Hp Hex1 = Rbar_opp (Rbar_glb_ne E Hm Hex2).
Proof.
  unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne _ _ _) ; simpl ; intros g (Hg, Hg') ;
  unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne _ _ _) ; simpl ; intros l [Hl Hl'] ;
  apply Rbar_le_antisym.
  apply Hl', Rbar_lb_ub ; rewrite Rbar_opp_involutive ;
  apply (Rbar_is_lb_subset _ E) ; auto ; intros x ; rewrite Rbar_opp_involutive ; auto.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hg', Rbar_ub_lb ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

Lemma Rbar_is_lub_ne_unique (E : Rbar -> Prop) (Hp : {E p_infty} + {~ E p_infty})
  (Hex : exists (x : R), E x) (l : Rbar) :
  Rbar_is_lub E l -> Rbar_lub_ne E Hp Hex = l.
Proof.
  move => H.
  rewrite /Rbar_lub_ne.
  case: Rbar_ex_lub_ne => l0 H0 /=.
  apply Rbar_le_antisym.
  apply H0, H.
  apply H, H0.
Qed.
Lemma Rbar_is_glb_ne_unique (E : Rbar -> Prop) (Hp : {E m_infty} + {~ E m_infty})
  (Hex : exists (x : R), E x) (l : Rbar) :
  Rbar_is_glb E l -> Rbar_glb_ne E Hp Hex = l.
Proof.
  move => H.
  rewrite /Rbar_glb_ne.
  case: Rbar_ex_glb_ne => l0 H0 /=.
  apply Rbar_le_antisym.
  apply H, H0.
  apply H0, H.
Qed.

(** Order *)

Lemma Rbar_glb_le_lub (E : Rbar -> Prop) Hp Hm Hex1 Hex2 :
  Rbar_le (Rbar_glb_ne E Hm Hex1) (Rbar_lub_ne E Hp Hex2).
Proof.
  case Hex1 ; intros x Hex.
  apply Rbar_le_trans with (y := Finite x).
  unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne _ _ _) ; simpl ; intros g (Hg, _) ; apply Hg ; auto.
  unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne _ _ _) ; simpl ; intros l (Hl, _) ; apply (Hl (Finite x)) ; auto.
Qed.

Lemma Rbar_is_lub_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2)
  -> Rbar_le l1 l2.
Proof.
  intros Hs (_,H1) (H2, _).
  apply H1 ; intros x Hx ; apply H2, Hs, Hx.
Qed.
Lemma Rbar_is_glb_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E2 x -> E1 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2)
  -> Rbar_le l1 l2.
Proof.
  intros Hs (H1, _) (_, H2).
  apply H2 ; intros x Hx ; apply H1, Hs, Hx.
Qed.

Lemma Rbar_is_lub_unique (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2)
  -> l1 = l2.
Proof.
  intros Hs H1 H2 ; apply Rbar_le_antisym ;
  [apply (Rbar_is_lub_subset E1 E2) | apply (Rbar_is_lub_subset E2 E1) ] ; auto ; intros x H ;
  apply Hs ; auto.
Qed.
Lemma Rbar_is_glb_unique (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2)
  -> l1 = l2.
Proof.
  intros Hs H1 H2 ; apply Rbar_le_antisym ;
  [apply (Rbar_is_glb_subset E1 E2) | apply (Rbar_is_glb_subset E2 E1) ] ; auto ; intros x H ;
  apply Hs ; auto.
Qed.

Lemma Rbar_is_lub_ext (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l) -> (Rbar_is_lub E2 l).
Proof.
  intros Heq (H1,H2) ; split.
  apply (Rbar_is_ub_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
  intros b Hb ; apply H2 ; apply (Rbar_is_ub_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
Qed.
Lemma Rbar_is_glb_ext (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l) -> (Rbar_is_glb E2 l).
Proof.
  intros Heq (H1, H2) ; split.
  apply (Rbar_is_lb_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
  intros b Hb ; apply H2 ; apply (Rbar_is_lb_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
Qed.

Lemma Rbar_lub_subset (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E1 x -> E2 x) -> Rbar_le (Rbar_lub_ne E1 Hp1 Hex1) (Rbar_lub_ne E2 Hp2 Hex2).
Proof.
  intros Hs ; unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne E1 _ _) ; intros l1 Hl1 ;
  case (Rbar_ex_lub_ne E2 _ _) ; simpl ; intros l2 Hl2 ; apply (Rbar_is_lub_subset E1 E2) ; auto.
Qed.
Lemma Rbar_glb_subset (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E2 x -> E1 x) -> Rbar_le (Rbar_glb_ne E1 Hp1 Hex1) (Rbar_glb_ne E2 Hp2 Hex2).
Proof.
  intro Hs ; unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne E1 _ _) ; intros l1 Hl1 ;
  case (Rbar_ex_glb_ne E2 _ _) ; simpl ; intros l2 Hl2 ; apply (Rbar_is_glb_subset E1 E2) ; auto.
Qed.

Lemma Rbar_lub_rw (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E1 x <-> E2 x) -> (Rbar_lub_ne E1 Hp1 Hex1) = (Rbar_lub_ne E2 Hp2 Hex2).
Proof.
  intro Hs ; apply Rbar_le_antisym ; apply Rbar_lub_subset ; intros x H ; apply Hs ; auto.
Qed.
Lemma Rbar_glb_rw (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E1 x <-> E2 x) -> (Rbar_glb_ne E1 Hp1 Hex1) = (Rbar_glb_ne E2 Hp2 Hex2).
Proof.
  intros Hs ; apply Rbar_le_antisym ; apply Rbar_glb_subset ; intros x H ; apply Hs ; auto.
Qed.

(** ** For sets in R *)

(** Definition *)

Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) :=
  is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).
Definition is_glb_Rbar (E : R -> Prop) (l : Rbar) :=
  is_lb_Rbar E l /\ (forall b, is_lb_Rbar E b -> Rbar_le b l).

Lemma is_lub_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_lub_Rbar E l <-> Rbar_is_lub (fun x => is_finite x /\ E x) l.
Proof.
  split => [[Hub Hlub]|[Hub Hlub]].
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
Qed.
Lemma is_glb_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_glb_Rbar E l <-> Rbar_is_glb (fun x => is_finite x /\ E x) l.
Proof.
  split => [[Hub Hlub]|[Hub Hlub]].
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
Qed.

(** Existence *)

Lemma ex_lub_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) :
  {l : Rbar | is_lub_Rbar E l}.
Proof.
  case: (Rbar_ex_lub_ne (fun x => is_finite x /\ E x)) => [ | | l Hl].
  right ; case => //.
  case: Hex => x Hx ; by exists x.
  exists l ; by apply is_lub_Rbar_correct.
Qed.
Lemma ex_glb_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) :
  {l : Rbar | is_glb_Rbar E l}.
Proof.
  case: (Rbar_ex_glb_ne (fun x => is_finite x /\ E x)) => [ | | l Hl].
  right ; by case.
  case: Hex => x Hx ; by exists x.
  exists l ; by apply is_glb_Rbar_correct.
Qed.

(** Functions *)

Definition Lub_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) := projT1 (ex_lub_Rbar_ne E Hex).
Definition Glb_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) := projT1 (ex_glb_Rbar_ne E Hex).

Lemma is_lub_Rbar_ne_unique (E : R -> Prop) (pr : exists x : R, E x) (l : Rbar) :
  is_lub_Rbar E l -> Lub_Rbar_ne E pr = l.
Proof.
  move => Hl ; rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne => l' /= Hl'.
  apply Rbar_le_antisym.
  by apply Hl', Hl.
  by apply Hl, Hl'.
Qed.
Lemma is_glb_Rbar_ne_unique (E : R -> Prop) (pr : exists x : R, E x) (l : Rbar) :
  is_glb_Rbar E l -> Glb_Rbar_ne E pr = l.
Proof.
  move => Hl ; rewrite /Glb_Rbar_ne ; case: ex_glb_Rbar_ne => l' /= Hl'.
  apply Rbar_le_antisym.
  by apply Hl, Hl'.
  by apply Hl', Hl.
Qed.

Lemma Lub_Rbar_ne_correct (E : R -> Prop) (pr : exists x : R, E x) :
  is_lub_Rbar E (Lub_Rbar_ne E pr).
Proof.
  rewrite /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne => l /= Hl.
Qed.
Lemma Glb_Rbar_ne_correct (E : R -> Prop) (pr : exists x : R, E x) :
  is_glb_Rbar E (Glb_Rbar_ne E pr).
Proof.
  rewrite /Glb_Rbar_ne ; by case: ex_glb_Rbar_ne => l /= Hl.
Qed.

(** Order *)

Lemma is_lub_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_lub_Rbar E1 l1 -> is_lub_Rbar E2 l2
    -> Rbar_le l2 l1.
Proof.
  move => H [ub1 _] [_ lub2].
  apply: lub2 ; by apply (is_ub_Rbar_subset E1), ub1.
Qed.
Lemma is_glb_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_glb_Rbar E1 l1 -> is_glb_Rbar E2 l2
    -> Rbar_le l1 l2.
Proof.
  move => H [ub1 _] [_ lub2].
  apply: lub2 ; by apply (is_lb_Rbar_subset E1), ub1.
Qed.

Lemma is_lub_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x <-> E1 x) -> is_lub_Rbar E1 l -> is_lub_Rbar E2 l.
Proof.
  move => H [ub1 lub1] ; split.
  apply (is_ub_Rbar_subset E1) ; [apply H | apply ub1].
  move => b Hb ; apply: lub1 ; apply (is_ub_Rbar_subset E2) ; [apply H | apply Hb].
Qed.
Lemma is_glb_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x <-> E1 x) -> is_glb_Rbar E1 l -> is_glb_Rbar E2 l.
Proof.
  move => H [ub1 lub1] ; split.
  apply (is_lb_Rbar_subset E1) ; [apply H | apply ub1].
  move => b Hb ; apply: lub1 ; apply (is_lb_Rbar_subset E2) ; [apply H | apply Hb].
Qed.

Lemma Lub_Rbar_ne_eqset (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Lub_Rbar_ne E1 pr1 = Lub_Rbar_ne E2 pr2.
Proof.
  move => H ; rewrite {2}/Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => {pr2} l /= Hl.
  apply is_lub_Rbar_ne_unique.
  move: Hl ; by apply is_lub_Rbar_eqset.
Qed.
Lemma Glb_Rbar_ne_eqset (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Glb_Rbar_ne E1 pr1 = Glb_Rbar_ne E2 pr2.
Proof.
  move => H ; rewrite {2}/Glb_Rbar_ne ;
  case: (ex_glb_Rbar_ne E2 pr2) => {pr2} l2 H2 /=.
  apply is_glb_Rbar_ne_unique.
  move: H2 ; by apply is_glb_Rbar_eqset.
Qed.

Lemma Lub_Rbar_ne_pr :
  forall E (pr1 pr2 : exists x, E x),
  Lub_Rbar_ne E pr1 = Lub_Rbar_ne E pr2.
Proof.
intros E pr1 pr2.
by apply Lub_Rbar_ne_eqset.
Qed.
Lemma Glb_Rbar_ne_pr :
  forall E (pr1 pr2 : exists x, E x),
  Glb_Rbar_ne E pr1 = Glb_Rbar_ne E pr2.
Proof.
intros E pr1 pr2.
by apply Glb_Rbar_ne_eqset.
Qed.


(** * Emptiness is decidable *)

Lemma not_empty_0 (E : R -> Prop) :
  let F := fun x => x = 0 \/ E x in exists x, F x.
Proof.
  intros ; exists 0 ; left ; reflexivity.
Qed.

Lemma not_empty_1 (E : R -> Prop) :
  let F := fun x => x = 1 \/ E x in exists x, F x.
Proof.
  intros ; exists 1 ; left ; reflexivity.
Qed.

Definition Empty (E : R -> Prop) :=
  Lub_Rbar_ne _ (not_empty_0 E) = Glb_Rbar_ne _ (not_empty_0 E)
  /\ Lub_Rbar_ne _ (not_empty_1 E) = Glb_Rbar_ne _ (not_empty_1 E).

Lemma Empty_correct_1 (E : R -> Prop) :
  Empty E -> forall x, ~ E x.
Proof.
  case => E0 E1 x Ex.
  rewrite /Lub_Rbar_ne /Glb_Rbar_ne in E0 ;
  case : (ex_lub_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) E0 => /= s0 Hs0 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) => i0 Hi0 /= E0.
  have : (x = 0) ; last move => {s0 Hs0 i0 Hi0 E0}.
  apply Rle_antisym.
  apply (Rbar_le_trans x s0 0).
  apply Hs0 ; by right.
  rewrite E0 ; apply Hi0 ; by left.
  apply (Rbar_le_trans 0 s0 x).
  apply Hs0 ; by left.
  rewrite E0 ; apply Hi0 ; by right.
  rewrite /Lub_Rbar_ne /Glb_Rbar_ne in E1 ;
  case : (ex_lub_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) E1 => /= s1 Hs1 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) => i1 Hi1 /= E1.
  have : (x = 1) ; last move => {s1 Hs1 i1 Hi1 E1}.
  apply Rle_antisym.
  apply (Rbar_le_trans x s1 1).
  apply Hs1 ; by right.
  rewrite E1 ; apply Hi1 ; by left.
  apply (Rbar_le_trans 1 s1 x).
  apply Hs1 ; by left.
  rewrite E1 ; apply Hi1 ; by right.
  move => -> ; apply R1_neq_R0.
Qed.

Lemma Empty_correct_2 (E : R -> Prop) :
  (forall x, ~ E x) -> Empty E.
Proof.
  move => H ; split ;
  rewrite /Glb_Rbar_ne /Lub_Rbar_ne ;
  [ case : (ex_lub_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) => s0 Hs0 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) => i0 Hi0 /=
  | case : (ex_lub_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) => s1 Hs1 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) => i1 Hi1 /=].
  have : (i0 = Finite 0) ; last move => -> ;
  apply: Rbar_le_antisym.
  apply Hi0 ; by left.
  apply Hi0 => y ; case => H0.
  rewrite H0 ; by right.
  contradict H0 ; apply H.
  apply Hs0 => y ; case => H0.
  rewrite H0 ; by right.
  contradict H0 ; apply H.
  apply Hs0 ; by left.
  have : (i1 = Finite 1) ; last move => -> ;
  apply: Rbar_le_antisym.
  apply Hi1 ; by left.
  apply Hi1 => y ; case => H1.
  rewrite H1 ; by right.
  contradict H1 ; apply H.
  apply Hs1 => y ; case => H1.
  rewrite H1 ; by right.
  contradict H1 ; apply H.
  apply Hs1 ; by left.
Qed.

Lemma Empty_dec (E : R -> Prop) :
  {~Empty E}+{Empty E}.
Proof.
  case: (Rbar_eq_dec (Lub_Rbar_ne _ (not_empty_0 E)) (Glb_Rbar_ne _ (not_empty_0 E))) => H0 ;
    [ | left].
  case: (Rbar_eq_dec (Lub_Rbar_ne _ (not_empty_1 E)) (Glb_Rbar_ne _ (not_empty_1 E))) => H1 ;
    [by right | left].
  contradict H1 ; apply H1.
  contradict H0 ; apply H0.
Qed.
Lemma not_Empty_dec (E : R -> Prop) : (Decidable.decidable (exists x, E x)) ->
  {(exists x, E x)} + {(forall x, ~ E x)}.
Proof.
  move => He ;
  case: (Empty_dec E) => Hx ;
  [left|right].
  case: He => // He.
  contradict Hx ;
  apply: Empty_correct_2 => x ; contradict He ; by exists x.
  by apply: Empty_correct_1.
Qed.

(** * Other definitions for lub and glb *)

Lemma Lub_Rbar_ex (E : R -> Prop) (pr : Decidable.decidable (exists x, E x)) :
  {l : Rbar | is_lub_Rbar E l}.
Proof.
  intros.
  destruct (not_Empty_dec _ pr).
  destruct (ex_lub_Rbar_ne _ e) as (l,lub).
  exists l ; apply lub.
  exists m_infty ; split.
  intros x Ex ; contradict Ex ; apply n.
  now intros ; destruct b.
Qed.

Definition Lub_Rbar (E : R -> Prop) (pr : Decidable.decidable (exists x, E x)) :=
  projT1 (Lub_Rbar_ex E pr).

Lemma Lub_Rbar_eq_seq (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Lub_Rbar E1 pr1 = Lub_Rbar E2 pr2.
Proof.
  move => H ; rewrite /Lub_Rbar ;
  case: (Lub_Rbar_ex E1 pr1) => {pr1} l1 H1 ;
  case: (Lub_Rbar_ex E2 pr2) => {pr2} l2 H2 /=.
  apply Rbar_le_antisym ;
  [ apply (is_lub_Rbar_subset E2 E1)
  | apply (is_lub_Rbar_subset E1 E2)] => //= x ; by apply H.
Qed.

Lemma Glb_Rbar_ex (E : R -> Prop) (pr : Decidable.decidable (exists x, E x)) :
  {l : Rbar | is_glb_Rbar E l}.
Proof.
  intros.
  destruct (not_Empty_dec _ pr).
  destruct (ex_glb_Rbar_ne _ e) as (l,lub).
  exists l ; apply lub.
  exists p_infty ; split.
  intros x Ex ; contradict Ex ; apply n.
  now intros ; destruct b.
Qed.

Definition Glb_Rbar (E : R -> Prop) (pr : Decidable.decidable (exists x, E x)) :=
  projT1 (Glb_Rbar_ex E pr).

Lemma Glb_Rbar_eq_seq (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Glb_Rbar E1 pr1 = Glb_Rbar E2 pr2.
Proof.
  move => H ; rewrite /Glb_Rbar ;
  case: (Glb_Rbar_ex E1 pr1) => {pr1} l1 H1 ;
  case: (Glb_Rbar_ex E2 pr2) => {pr2} l2 H2 /=.
  apply Rbar_le_antisym ;
  [ apply (is_glb_Rbar_subset E1 E2)
  | apply (is_glb_Rbar_subset E2 E1)] => //= x ; by apply H.
Qed.

Lemma uniqueness_dec P : (exists ! x : R, P x) -> {x : R | P x}.
Proof.
  move => H.
  have H' : exists x, P x.
    case: H => x Hx.
    exists x ; by apply Hx.
  exists (Lub_Rbar_ne _ H').
  case: H => x Hx.
  replace (real (Lub_Rbar_ne P H')) with (real (Finite x)).
  by apply Hx.
  apply f_equal, sym_eq, is_lub_Rbar_ne_unique.
  split.
  move => y Hy.
  right ; by apply sym_eq, Hx.
  move => b Hb.
  by apply Hb, Hx.
Qed.
