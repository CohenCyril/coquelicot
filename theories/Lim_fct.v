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

(** Order *)

Lemma is_lim_le_loc (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg
  -> Rbar_locally (fun y => f y <= g y) x
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
  -> Rbar_locally (fun y => f y <= g y) x
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
  -> Rbar_locally (fun y => g y <= f y) x
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
Proof.
  move => Hf Hl.
  suff Hf' : Rbar_locally (fun y => Rabs (f y) > Rabs (real l) / 2) x.
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
  rewrite -Ropp_minus_distr Rabs_Ropp.
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
  field_simplify in Hf1 ; rewrite -Rdiv_1 in Hf1 ;
  field_simplify in Hf2 ; rewrite -Rdiv_1 in Hf2.
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
  rewrite -Rdiv_1 in Hf.
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

Lemma is_lim_const (a : R) (x : Rbar) :
  is_lim (fun _ => a) x a.
Proof.
  case: x => [x | | ] /= eps ; exists (mkposreal _ Rlt_0_1) => /= ;
  intros ;
  rewrite Rminus_eq0 Rabs_R0 ;
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
  continuity_pt f x -> ex_f_lim f x.
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

(** Exponential functions *)

Lemma Rle_exp (x : R) (n : nat) :
  0 <= x -> sum_f_R0 (fun k => x^k / INR (fact k)) n <= exp x.
Proof.
  move => Hx.
  rewrite /exp /exist_exp.
  case: Alembert_C3 => /= y Hy.
  apply Rnot_lt_le => H.
  apply Rminus_lt_0 in H.
  case: (Hy _ H) => N {Hy} Hy.
  move: (Hy _ (le_plus_r n N)) => {Hy}.
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: N => [ | N IH].
  rewrite plus_0_r.
  apply Req_le.
  elim: (n) => {n H} [ | n /= <-].
  apply Rmult_comm.
  apply f_equal.
  apply Rmult_comm.
  apply Rle_trans with (1 := IH).
  rewrite -plus_n_Sm.
  move: (n + N)%nat => {n H N IH} n.
  rewrite /sum_f_R0 -/sum_f_R0.
  apply Rminus_le_0 ; ring_simplify.
  apply Rmult_le_pos.
  apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
  by apply pow_le.
Qed.

Lemma is_lim_exp_p : is_lim (fun y => exp y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => 1 + y).
  pattern p_infty at 2.
  replace p_infty with (Rbar_plus 1 p_infty) by auto.
  apply is_lim_plus.
  apply is_lim_const.
  apply is_lim_id.
  by [].
  exists 0 => y Hy.
  by apply Rlt_le, exp_ineq1.
Qed.

Lemma is_lim_exp_m : is_lim (fun y => exp y) m_infty 0.
Proof.
  search_lim.
  apply is_lim_ext with (fun y => /(exp (- y))).
  move => y ; rewrite exp_Ropp ; apply Rinv_involutive.
  apply Rgt_not_eq, exp_pos.
  apply is_lim_inv.
  apply is_lim_comp with p_infty.
  apply is_lim_exp_p.
  replace p_infty with (Rbar_opp m_infty) by auto.
  apply is_lim_opp.
  apply is_lim_id.
  by apply Rbar_locally_forall.
  by [].
  by [].
Qed.

Lemma ex_lim_exp (x : Rbar) : ex_lim (fun y => exp y) x.
Proof.
  case: x => [x | | ].
  apply ex_f_lim_correct, ex_lim_continuity.
  apply derivable_continuous_pt, derivable_pt_exp.
  exists p_infty ; by apply is_lim_exp_p.
  exists 0 ; by apply is_lim_exp_m.
Qed.

Lemma Lim_exp (x : Rbar) : 
  Lim (fun y => exp y) x = 
    match x with
      | Finite x => exp x
      | p_infty => p_infty
      | m_infty => 0
    end.
Proof.
  apply is_lim_unique.
  case: x => [x | | ].
  apply is_lim_continuity.
  apply derivable_continuous_pt, derivable_pt_exp.
  by apply is_lim_exp_p.
  by apply is_lim_exp_m.
Qed.

Lemma is_lim_exp_aux1 : is_lim (fun y => exp y / y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => (1 + y + y^2 / 2)/y).
  evar (l : Rbar).
  pattern p_infty at 2.
  replace p_infty with l.
  apply is_lim_ext_loc with (fun y => /y + 1 + y / 2).
  exists 0 => y Hy.
  field.
  by apply Rgt_not_eq.
  apply is_lim_plus.
  apply is_lim_plus.
  apply is_lim_inv.
  apply is_lim_id.
  by [].
  apply is_lim_const.
  by [].
  apply is_lim_div.
  apply is_lim_id.
  apply is_lim_const.
  apply Rbar_finite_neq, Rgt_not_eq, Rlt_0_2.
  simpl.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  simpl.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  rewrite /l /=.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  exists 0 => y Hy.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rinv_0_lt_compat.
  rewrite /exp.
  rewrite /exist_exp.
  case: Alembert_C3 => /= x Hx.
  rewrite /Pser /infinite_sum in Hx.
  apply Rnot_lt_le => H.
  case: (Hx _ (proj1 (Rminus_lt_0 _ _) H)) => N {Hx} Hx.
  move: (Hx _ (le_plus_r 2 N)) => {Hx}.
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: N => [ | n IH].
  simpl ; apply Req_le ; field.
  apply Rle_trans with (1 := IH).
  rewrite -plus_n_Sm ; move: (2 + n)%nat => {n IH} n.
  rewrite /sum_f_R0 -/sum_f_R0.
  rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_eq0.
  apply Rmult_le_pos.
  apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
  apply pow_le.
  by apply Rlt_le.
Qed.

Lemma is_lim_exp_aux2 : is_lim (fun y => y * exp y) m_infty 0.
Proof.
  search_lim.
  apply is_lim_ext_loc with (fun y => - / (exp (-y) / (- y))).
  exists 0 => y Hy.
  rewrite exp_Ropp.
  field.
  split.
  apply Rgt_not_eq, exp_pos.
  by apply Rlt_not_eq.
  apply is_lim_opp.
  apply is_lim_inv.
  apply (is_lim_comp (fun y => exp y / y)) with p_infty.
  by apply is_lim_exp_aux1.
  search_lim.
  apply is_lim_opp.
  apply is_lim_id.
  by [].
  by apply Rbar_locally_forall.
  by [].
  simpl ; by rewrite Ropp_0.
Qed.
