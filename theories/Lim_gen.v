Require Import Reals ssreflect.
Open Local Scope R_scope.

Require Import Rbar_theory Floor Rcomplements.

(** * Definition *)

Definition is_lim_gen (f : R -> R) (x l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, Rbar_locally (fun y => Rabs (f y - l) < eps) x
    | p_infty => forall M : R, Rbar_locally (fun y => M < f y) x
    | m_infty => forall m : R, Rbar_locally (fun y => f y < m) x
  end.
Definition ex_lim_gen (f : R -> R) (x : Rbar) :=
  exists l : Rbar, is_lim_gen f x l.
Definition Lim_gen (f : R -> R) (x : Rbar) :=
  Rbar_lim_seq (fun n => Finite (f (Rbar_loc_seq x n))).

Lemma is_lim_gen_uniq (f : R -> R) (x l : Rbar) :
  is_lim_gen f x l -> Lim_gen f x = l.
Proof.
  case: l => [l | | ] /= H ; apply Rbar_is_lim_correct => M ;
  case: (Rbar_loc_seq_carac _ _ (H M)) => {H} N H ; exists N => //=.
  move => n Hn ; by apply Rabs_lt_between', H.
Qed.
Lemma is_lim_gen_correct (f : R -> R) (x : Rbar) :
  ex_lim_gen f x -> is_lim_gen f x (Lim_gen f x).
Proof.
  case => l H.
  replace (Lim_gen f x) with l.
  by [].
  apply sym_eq ; by apply is_lim_gen_uniq.
Qed.

(** * Operations *)
(** Extentionality *)

Lemma is_lim_gen_ext_loc (f g : R -> R) (x l : Rbar) :
  Rbar_locally (fun y => f y = g y) x
  -> is_lim_gen f x l
  -> is_lim_gen g x l.
Proof.
  case: l => [l | | ] /= Hloc Hf M ;
  move: (Hf M) ; apply Rbar_locally_imply ;
  move: Hloc ; apply Rbar_locally_imply ;
  by apply Rbar_locally_forall => y ->.
Qed.
Lemma ex_lim_gen_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally (fun y => f y = g y) x
  -> ex_lim_gen f x
  -> ex_lim_gen g x.
Proof.
  move => Hloc ; case => l Hf ; exists l.
  by apply is_lim_gen_ext_loc with f.
Qed.
Lemma Lim_gen_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally (fun y => f y = g y) x
  -> Lim_gen f x = Lim_gen g x.
Proof.
  case/Rbar_loc_seq_carac => N Hloc.
  apply Rbar_lim_seq_ext_loc ; simpl.
  exists N => n Hn ; by apply f_equal, Hloc.
Qed.
