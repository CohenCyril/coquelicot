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
  is_lim f x l -> (forall u : nat -> R, 
    (exists N, forall n, (N <= n)%nat -> Finite (u n) <> x) ->
    is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l).
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

Ltac search_lim := let l := fresh "l" in
evar (l : Rbar) ;
match goal with
  | |- Lim _ _ = ?lu => apply is_lim_unique ; replace lu with l ; [ | unfold l]
  | |- is_lim _ _ ?lu => replace lu with l ; [ | unfold l]
end.

(** * Operations *)

(** Extentionality *)

Lemma is_lim_ext_loc (f g : R -> R) (x l : Rbar) :
  Rbar_locally (fun y => f y = g y) x
  -> is_lim f x l -> is_lim g x l.
Proof.
  case: l => [l | | ] /= Heq Hf eps ;
  move: (Hf eps) => {Hf} ;
  apply Rbar_locally_imply ;
  move: Heq ;
  apply Rbar_locally_imply ;
  by apply Rbar_locally_forall => y ->.
Qed.
Lemma ex_lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally (fun y => f y = g y) x
  -> ex_lim f x -> ex_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_lim_ext_loc with f.
Qed.
Lemma Lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally (fun y => f y = g y) x
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

(** Additive *)

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

(** Multiplicative *)

Lemma is_lim_inv (f : R -> R) (x l : Rbar) :
  is_lim f x l -> l <> 0 -> is_lim (fun y => / f y) x (Rbar_inv l).
Admitted.
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

Lemma is_lim_mult (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg
  -> is_Rbar_mult lf lg (Rbar_mult lf lg)
  -> is_lim (fun y => f y * g y) x (Rbar_mult lf lg).
Proof.
  wlog: lf lg f g / (Rbar_le lf lg) => [Hw | Hl].
    case: (Rbar_le_lt_dec lf lg) => Hl Hf Hg Hfg.
    by apply Hw.
    apply is_lim_ext with (fun y : R => g y * f y).
    move => y ; by apply Rmult_comm.
    rewrite Rbar_mult_comm.
    apply Hw.
    by apply Rbar_lt_le.
    by apply Hg.
    by apply Hf.
    apply is_Rbar_mult_comm.
    by rewrite Rbar_mult_comm.
  case: lf Hl => [lf | | ] //= ; case: lg => [lg | | ] => //= Hl Hf Hg Hm ;
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
  
  case: Rle_dec Hm => Hm Hlf //=.
  case: Rle_lt_or_eq_dec Hlf => {Hm} _ Hlf //=.
  move => M.
  move: (Hg (M / (lf / 2))) => {Hg} ; apply Rbar_locally_imply.
  move: (Hf (pos_div_2 (mkposreal _ Hlf))) => /= {Hf} ; apply Rbar_locally_imply.
  apply Rbar_locally_forall => y Hf Hg.
  apply Rabs_lt_between' in Hf ; case: Hf => Hf _ ; field_simplify in Hf.
  rewrite -Rdiv_1 in Hf.
  replace M with ((lf / 2) * (M / (lf / 2))) by (field ; apply Rgt_not_eq, Hlf).
Admitted.
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

(** * Particular limits *)

Lemma is_lim_id (x : Rbar) :
  is_lim (fun y => y) x x.
Admitted.
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

Lemma is_lim_const (a : R) (x : Rbar) :
  is_lim (fun _ => a) x a.
Admitted.
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

Lemma is_lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> is_lim f x (f x).
Admitted.
Lemma ex_lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> ex_lim f x.
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