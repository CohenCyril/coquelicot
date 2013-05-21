Require Import Reals Rbar_theory Rcomplements.
Require Import Lim_seq ssreflect.
Require Import Locally.
Open Scope R_scope.

(** * Limit *)

Definition is_lim (f : R -> R) (x l : Rbar) :=
  match l with
    | Finite l => 
      forall eps : posreal, Rbar_locally (fun y => Rabs (f y - l) < eps) x
    | p_infty => forall M : R, Rbar_locally (fun y => M < f y) x
    | m_infty => forall M : R, Rbar_locally (fun y => f y < M) x
  end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_f_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).

(** ** Equivalence with Coq definition *)

Lemma is_lim_Coq_0 (f : R -> R) (x l : R) :
  is_lim f x l -> limit1_in f (fun y => y <> x) l x.
Proof.
  intros H e He ; set (eps := mkposreal e He).
  elim (H eps) ; clear H ; intros (d,Hd) H.
  exists d ; split ; [apply Hd | ].
  intros y Hy ; apply (H y).
  apply Hy.
  apply Hy.
Qed.
Lemma is_lim_Coq_1 (f : R -> R) (x l : R) :
  limit1_in f (fun y => y <> x) l x -> is_lim f x l.
Proof.
  intros H (e,He).
  elim (H e He) ; clear H ; intros d (Hd,H) ; set (delta := mkposreal d Hd).
  exists delta ; intros y Hy Hxy ; apply (H y).
  split.
  by apply Hxy.
  by apply Hy.
Qed.
Lemma is_lim_Coq f x l :
  limit1_in f (fun y => y <> x) l x <-> is_lim f x l.
Proof.
  split ; [apply is_lim_Coq_1|apply is_lim_Coq_0].
Qed.

(** ** Compute limit *)

Lemma is_lim_comp_seq (f : R -> R) (x l : Rbar) :
  is_lim f x l -> forall u : nat -> R, 
    (exists N, forall n, (N <= n)%nat -> Finite (u n) <> x) ->
    is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
  case: l => [l | | ] /= ; case: x => [x | | ] /= Hf u Hu0 Hu.
(* l,x \in R *)
  move => eps.
  case: (Hf eps) => {Hf} delta Hf.
  case: Hu0 => N0 Hu0.
  case: (Hu delta) => {Hu} N1 Hu.
  exists (N0 + N1)%nat => n Hn.
  apply Hf.
  apply Hu ; by apply le_trans with (1 := le_plus_r N0 N1).
  apply Rbar_finite_neq, Hu0 ; by apply le_trans with (1 := le_plus_l N0 N1).
(* l \in R /\ x = p_infty *)
  move => eps.
  case: (Hf eps) => {Hf} M Hf.
  case: (Hu M) => {Hu} N Hu.
  exists N => n Hn.
  apply Hf.
  by apply Hu.
(* l \in R /\ x = m_infty *)
  move => eps.
  case: (Hf eps) => {Hf} M Hf.
  case: (Hu M) => {Hu} N Hu.
  exists N => n Hn.
  apply Hf.
  by apply Hu.
(* l = p_infty /\ x \in R *)
  move => M.
  case: (Hf M) => {Hf} delta Hf.
  case: Hu0 => N0 Hu0.
  case: (Hu delta) => {Hu} N1 Hu.
  exists (N0 + N1)%nat => n Hn.
  apply Hf.
  apply Hu ; by apply le_trans with (1 := le_plus_r N0 N1).
  apply Rbar_finite_neq, Hu0 ; by apply le_trans with (1 := le_plus_l N0 N1).
(* l = p_infty /\ x = p_infty *)
  move => M.
  case: (Hf M) => {Hf} M' Hf.
  case: (Hu M') => {Hu} N Hu.
  exists N => n Hn.
  apply Hf.
  apply Hu ; by apply Hn.
(* l = p_infty /\ x = m_infty *)
  move => M.
  case: (Hf M) => {Hf} M' Hf.
  case: (Hu M') => {Hu} N Hu.
  exists N => n Hn.
  apply Hf.
  apply Hu ; by apply Hn.
(* l = m_infty /\ x \in R *)
  move => M.
  case: (Hf M) => {Hf} delta Hf.
  case: Hu0 => N0 Hu0.
  case: (Hu delta) => {Hu} N1 Hu.
  exists (N0 + N1)%nat => n Hn.
  apply Hf.
  apply Hu ; by apply le_trans with (1 := le_plus_r N0 N1).
  apply Rbar_finite_neq, Hu0 ; by apply le_trans with (1 := le_plus_l N0 N1).
(* l = m_infty /\ x = p_infty *)
  move => M.
  case: (Hf M) => {Hf} M' Hf.
  case: (Hu M') => {Hu} N Hu.
  exists N => n Hn.
  apply Hf.
  apply Hu ; by apply Hn.
(* l = m_infty /\ x = m_infty *)
  move => M.
  case: (Hf M) => {Hf} M' Hf.
  case: (Hu M') => {Hu} N Hu.
  exists N => n Hn.
  apply Hf.
  apply Hu ; by apply Hn.
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

Lemma ex_f_lim_correct (f : R -> R) (x : Rbar) :
  ex_f_lim f x <-> ex_lim f x /\ is_finite (Lim f x).
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
  ex_f_lim f x -> is_lim f x (real (Lim f x)).
Proof.
  intro Hf.
  apply ex_f_lim_correct in Hf.
  rewrite (proj2 Hf).
  by apply Lim_correct, Hf.
Qed.

(** * Operations *)

Lemma is_lim_comp (f g : R -> R) (x k l : Rbar) : 
  is_lim f l k -> is_lim g x l -> Rbar_locally (fun y => Finite (g y) <> l) x
    -> is_lim (fun x => f (g x)) x k.
Proof.
  case: k => [k | | ] /= Hf Hg Hg' ;
  move => e0 ;
  case: (l) (Hf e0) Hg Hg' => {Hf l} [l | | ] /= [e1 Hf] Hg Hg' ;
  case: (x) Hf (Hg e1) Hg' => {Hg x} [x | | ] /= Hf [e2 Hg] [e3 Hg'].
(* l, k, x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
  apply Rbar_finite_neq, Hg'.
  by apply Rlt_le_trans with (2 := Rmin_r e2 e3).
  by apply Hxy.
(* l, k \in R /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
  apply Rbar_finite_neq, Hg'.
  by apply Rle_lt_trans with (1 := Rmax_r e2 e3).
(* l, k \in R /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  apply Rbar_finite_neq, Hg'.
  by apply Rlt_le_trans with (2 := Rmin_r e2 e3).
(* l = p_infty /\ k, x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
(* l = p_infty /\ k \in R /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
(* l = p_infty /\ k \in R /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
(* l = m_infty /\ k, x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
(* l = m_infty /\ k \in R /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
(* l = m_infty /\ k \in R /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
(* l, x \in R /\ k = p_infty *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
  apply Rbar_finite_neq, Hg'.
  by apply Rlt_le_trans with (2 := Rmin_r e2 e3).
  by apply Hxy.
(* l \in R /\ k = p_infty /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
  apply Rbar_finite_neq, Hg'.
  by apply Rle_lt_trans with (1 := Rmax_r e2 e3).
(* l \in R /\ k = p_infty /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  apply Rbar_finite_neq, Hg'.
  by apply Rlt_le_trans with (2 := Rmin_r e2 e3).
(* l = p_infty /\ k = p_infty /\ x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
(* l = p_infty /\ k = p_infty /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
(* l = p_infty /\ k = p_infty /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
(* l = m_infty /\ k = p_infty /\ x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
(* l = m_infty /\ k = p_infty /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
(* l = m_infty /\ k = p_infty /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
(* l, x \in R /\ k = p_infty *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
  apply Rbar_finite_neq, Hg'.
  by apply Rlt_le_trans with (2 := Rmin_r e2 e3).
  by apply Hxy.
(* l \in R /\ k = p_infty /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
  apply Rbar_finite_neq, Hg'.
  by apply Rle_lt_trans with (1 := Rmax_r e2 e3).
(* l \in R /\ k = p_infty /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  apply Rbar_finite_neq, Hg'.
  by apply Rlt_le_trans with (2 := Rmin_r e2 e3).
(* l = p_infty /\ k = p_infty /\ x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
(* l = p_infty /\ k = p_infty /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
(* l = p_infty /\ k = p_infty /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
(* l = m_infty /\ k = p_infty /\ x \in R *)
  exists (mkposreal _ (Rmin_stable_in_posreal e2 e3)) => /= y Hy Hxy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
  by apply Hxy.
(* l = m_infty /\ k = p_infty /\ x = p_infty *)
  exists (Rmax e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rle_lt_trans with (1 := Rmax_l e2 e3).
(* l = m_infty /\ k = p_infty /\ x = m_infty *)
  exists (Rmin e2 e3) => /= y Hy.
  apply Hf.
  apply Hg.
  by apply Rlt_le_trans with (2 := Rmin_l e2 e3).
Qed.
Lemma ex_lim_comp (f g : R -> R) (x : Rbar) : 
  ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally (fun y => Finite (g y) <> Lim g x) x
    -> ex_lim (fun x => f (g x)) x.
Proof.
  intros.
  exists (Lim f (Lim g x)).
  apply is_lim_comp with (Lim g x).
  by apply Lim_correct.
  by apply Lim_correct.
  by apply H1.
Qed.
Lemma Lim_comp (f g : R -> R) (x : R) : 
  ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally (fun y => Finite (g y) <> Lim g x) x
    -> Lim (fun x => f (g x)) x = Lim f (Lim g x).
Proof.
  intros.
  apply is_lim_unique.
  apply is_lim_comp with (Lim g x).
  by apply Lim_correct.
  by apply Lim_correct.
  by apply H1.
Qed.

