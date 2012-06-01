Require Import Rcomplements Reals.
Require Import Rbar_theory Total_sup.
Require Import ssreflect.
Open Scope R_scope.

(** * upper ans lower bound of a sequence *)
(** ** upper bound *)
Definition is_sup_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, (forall n, u n < l + eps) /\ (exists n, l - eps < u n)
    | p_infty => forall M, exists n, M < u n
    | m_infty => False
  end.

Lemma is_sup_seq_correct (u : nat -> R) (l : Rbar) :
  is_sup_seq u l <-> Rbar_is_sup_seq (fun n => Finite (u n)) l.
Proof.
  case: l => [l | | ] // ; split => //= H.
  move: (H (u O) O) ; apply Rlt_irrefl.
Qed.

Lemma ex_sup_seq (u : nat -> R) :
  {l : Rbar | is_sup_seq u l}.
Proof.
  case: (Rbar_ex_sup_seq (fun n => Finite (u n))) => l Hl ; exists l ;
  by apply is_sup_seq_correct.
Qed.
Definition Sup_seq (u : nat -> R) := projT1 (ex_sup_seq u).

Lemma Sup_seq_eq (u : nat -> R) l :
  is_sup_seq u l -> Sup_seq u = l.
Proof.
  rewrite /Sup_seq ; case: (ex_sup_seq _) => Hl l' Hl'/=.
  apply (Rbar_is_sup_seq_rw (fun n => Finite (u n)) (fun n => Finite (u n))) => // ;
  by apply is_sup_seq_correct.
Qed.

(** ** lower bound *)

Definition is_inf_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, (forall n, l - eps < u n) /\ (exists n, u n < l + eps)
    | p_infty => False
    | m_infty => forall M, exists n, u n < M
  end.

Lemma is_inf_seq_correct (u : nat -> R) (l : Rbar) :
  is_inf_seq u l <-> Rbar_is_inf_seq (fun n => Finite (u n)) l.
Proof.
  case: l => [l | | ] // ; split => //= H.
  move: (H (u O) O) ; apply Rlt_irrefl.
Qed.

Lemma ex_inf_seq (u : nat -> R) :
  {l : Rbar | is_inf_seq u l}.
Proof.
  case: (Rbar_ex_inf_seq (fun n => Finite (u n))) => l Hl ; exists l ;
  by apply is_inf_seq_correct.
Qed.
Definition Inf_seq (u : nat -> R) :=
  projT1 (ex_inf_seq u).

Lemma Inf_seq_eq (u : nat -> R) l :
  is_inf_seq u l -> Inf_seq u = l.
Proof.
  rewrite /Inf_seq ; case: (ex_inf_seq _) => Hl l' Hl'/=.
  apply (Rbar_is_inf_seq_rw (fun n => Finite (u n)) (fun n => Finite (u n))) => // ;
  by apply is_inf_seq_correct.
Qed.

(** * upper and lower limit of a sequence *)

(** ** LimSup *)

Definition is_LimSup_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, 
        (forall N : nat, exists n : nat, (N <= n)%nat /\ l - eps < u n)
        /\ (exists N : nat, forall n : nat, (N <= n)%nat -> u n < l + eps)
    | p_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ M < u n)
    | m_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> u n < M)
  end.

Lemma is_LimSup_seq_correct (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l <-> Rbar_is_limsup_seq (fun n => Finite (u n)) l.
Proof.
  case: l => [l | | ] // ; split => H eps ; case: (H eps) => {H} [H H0]//.
Qed.

Lemma ex_LimSup_seq (u : nat -> R) : 
  {l : Rbar | is_LimSup_seq u l}.
Proof.
  case: (Rbar_ex_limsup_seq (fun n => Finite (u n))) => l Hl ; exists l ;
  by apply is_LimSup_seq_correct.
Qed.

Definition LimSup_seq (u : nat -> R) :=
  projT1 (ex_LimSup_seq u).

Lemma LimSup_seq_correct (u : nat -> R) :
  LimSup_seq u = Rbar_limsup_seq (fun n => Finite (u n)).
Proof.
  rewrite /LimSup_seq ; case: (ex_LimSup_seq _) => l Hl ;
  rewrite /Rbar_limsup_seq ; case: (Rbar_ex_limsup_seq _) => l' Hl' /=.
  apply (Rbar_is_limsup_eq (fun n => Finite (u n)) (fun n => Finite (u n))) => // ; 
  by apply is_LimSup_seq_correct.
Qed.

(** ** LimInf *)

Definition is_LimInf_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, 
        (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < l + eps)
        /\ (exists N : nat, forall n : nat, (N <= n)%nat -> l - eps < u n)
    | p_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> M < u n)
    | m_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < M)
  end.

Lemma is_LimInf_seq_correct (u : nat -> R) (l : Rbar) :
  is_LimInf_seq u l <-> Rbar_is_liminf_seq (fun n => Finite (u n)) l.
Proof.
  case: l => [l | | ] // ; split => H eps ; case: (H eps) => {H} [H H0]//.
Qed.

Lemma ex_LimInf_seq (u : nat -> R) : 
  {l : Rbar | is_LimInf_seq u l}.
Proof.
  case: (Rbar_ex_liminf_seq (fun n => Finite (u n))) => l Hl ; exists l ;
  by apply is_LimInf_seq_correct.
Qed.

Definition LimInf_seq (u : nat -> R) :=
  projT1 (ex_LimInf_seq u).

Lemma LimInf_seq_correct (u : nat -> R) :
  LimInf_seq u = Rbar_liminf_seq (fun n => Finite (u n)).
Proof.
  rewrite /LimInf_seq ; case: (ex_LimInf_seq _) => l Hl ;
  rewrite /Rbar_liminf_seq ; case: (Rbar_ex_liminf_seq _) => l' Hl' /=.
  apply (Rbar_is_liminf_eq (fun n => Finite (u n)) (fun n => Finite (u n))) => // ; 
  by apply is_LimInf_seq_correct.
Qed.