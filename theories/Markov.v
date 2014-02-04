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

Require Import RIneq Rcomplements.

(** This file describes and proves [Markov]'s principle: if you have a
 decidable property P on [nat], then you either have a proof that P
 does never hold or you have constructed a witness on which P
 holds.
#<br /># Several variants are given. Additional lemmas are given in
 case you have the excluded middle. *)


Open Scope R_scope.

(** * Markov's principle *)

Lemma Markov_bool :
  forall f : nat -> bool,
  {n | f n = true} + {forall n, f n = false}.
Proof.
(* *)
assert (Hi: forall n, 0 < INR n + 1).
intros N.
rewrite <- S_INR.
apply lt_0_INR.
apply lt_0_Sn.
intros f.
set (u n := if f n then / (INR n + 1) else 0).
(* *)
assert (Bu: forall n, u n <= 1).
intros n.
unfold u.
case f.
rewrite <- S_INR, <- Rinv_1.
apply Rinv_le_contravar.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S.
apply le_0_n.
apply Rle_0_1.
(* *)
set (E y := exists n, y = u n).
destruct (completeness E) as (l,(ub,lub)).
exists 1.
intros y (n,->).
apply Bu.
exists (u O).
now exists O.
destruct (Rle_lt_dec l 0) as [Hl|Hl].
right.
intros n.
apply Bool.not_true_is_false.
intros H.
apply Rle_not_lt with (1 := Hl).
apply Rlt_le_trans with (/ (INR n + 1)).
now apply Rinv_0_lt_compat.
apply ub.
exists n.
unfold u.
now rewrite H.
left.
set (N := Zabs_nat (up (/l) - 2)).
(* *)
assert (HN: INR N + 1 = IZR (up (/ l)) - 1).
unfold N.
rewrite INR_IZR_INZ.
rewrite inj_Zabs_nat.
replace (IZR (up (/ l)) - 1) with (IZR (up (/ l) - 2) + 1).
apply (f_equal (fun v => IZR v + 1)).
apply Zabs_eq.
apply Zle_minus_le_0.
apply (Zlt_le_succ 1).
apply lt_IZR.
apply Rle_lt_trans with (/l).
apply Rmult_le_reg_r with (1 := Hl).
rewrite Rmult_1_l, Rinv_l by now apply Rgt_not_eq.
apply lub.
intros y (m,->).
apply Bu.
apply archimed.
rewrite minus_IZR.
simpl.
ring.
(* *)
exists N.
apply Bool.not_false_is_true.
intros H.
refine (Rle_not_lt _ _ (lub (/ (INR (S N) + 1)) _) _).
intros y (n,->).
unfold u.
destruct (le_or_lt n N) as [Hn|Hn].
case (le_lt_or_eq _ _ Hn) ; clear Hn ; intros Hn.
(* . *)
case_eq (f n).
intros Hf.
elimtype False.
apply (Rlt_not_le (/ (INR n + 1)) l).
rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
rewrite <- S_INR.
apply Rinv_1_lt_contravar.
apply (le_INR 1).
apply le_n_S.
apply le_0_n.
apply Rlt_le_trans with (INR N + 1).
rewrite <- S_INR.
apply lt_INR.
now apply lt_n_S.
rewrite HN.
apply Rplus_le_reg_r with (-/l + 1).
ring_simplify.
apply archimed.
apply ub.
exists n.
unfold u.
now rewrite Hf.
intros _.
apply Rlt_le.
now apply Rinv_0_lt_compat.
(* . *)
rewrite Hn, H.
apply Rlt_le.
now apply Rinv_0_lt_compat.
(* . *)
case f.
rewrite <- 2!S_INR.
apply Rinv_le_contravar.
apply lt_0_INR.
apply lt_0_Sn.
apply le_INR.
apply le_n_S.
now apply lt_le_S.
apply Rlt_le.
now apply Rinv_0_lt_compat.
(* *)
rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
apply Rinv_1_lt_contravar.
rewrite <- Rinv_1.
apply Rinv_le_contravar with (1 := Hl).
apply lub.
intros y (n,->).
apply Bu.
rewrite S_INR.
rewrite HN.
ring_simplify.
apply archimed.
Qed.

Lemma Markov : forall P : nat -> Prop, (forall n, {P n}+{~P n}) ->
  {n : nat| P n} + {forall n, ~ P n}.
Proof.
  intros P H.
  destruct (Markov_bool (fun n => if H n then true else false)) as [(n,K)|K].
  left.
  exists n.
  now destruct (H n).
  right.
  intros n.
  specialize (K n).
  now destruct (H n).
Qed.

(** ** Corollaries *)

Lemma Markov_cor1 : forall P : nat -> Prop, (forall n, {P n}+{~P n}) ->
  (~ forall n : nat, ~ P n) -> exists n : nat, P n.
Proof.
  intros.
  destruct (Markov P H).
  destruct s as (n,H1) ; exists n ; apply H1.
  contradict H0 ; apply n.
Qed.

Lemma Markov_cor2 : forall P : nat -> Prop, (forall n, {P n}+{~P n}) ->
  ~~ (exists n : nat, P n) -> exists n : nat, P n.
Proof.
  intros.
  apply Markov_cor1.
  apply H.
  contradict H0.
  intros (n,H1).
  contradict H1 ; apply H0.
Qed.

(** * Excluded-middle and decidability *)

Lemma EM_dec :
  forall P : Prop, {not (not P)} + {not P}.
Proof.
intros P.
set (E := fun x => x = 0 \/ (x = 1 /\ P)).
destruct (completeness E) as [x H].
- exists 1.
  intros x [->|[-> _]].
  apply Rle_0_1.
  apply Rle_refl.
- exists 0.
  now left.
destruct (Rle_lt_dec 1 x) as [H'|H'].
- left.
  intros HP.
  elim Rle_not_lt with (1 := H').
  apply Rle_lt_trans with (2 := Rlt_0_1).
  apply H.
  intros y [->|[_ Hy]].
  apply Rle_refl.
  now elim HP.
- right.
  intros HP.
  apply Rlt_not_le with (1 := H').
  apply H.
  right.
  now split.
Qed.

Lemma EM_dec' :
  forall P : Prop, P \/ not P -> {P} + {not P}.
Proof.
intros P HP.
destruct (EM_dec P) as [H|H].
- left.
  now destruct HP.
- now right.
Qed.
