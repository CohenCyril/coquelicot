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

Lemma is_LimSup_seq_eq (u v : nat -> R) lu lv :
  (forall n, u n = v n)
  -> is_LimSup_seq u lu -> is_LimSup_seq v lv
  -> lu = lv.
Proof.
  move => Heq Hu Hv.
  apply is_LimSup_seq_correct in Hu ; apply is_LimSup_seq_correct in Hv.
  apply (Rbar_is_limsup_eq (fun n : nat => Finite (u n)) (fun n : nat => Finite (v n))) 
  => // n ; by rewrite Heq.
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

Lemma is_LimInf_seq_eq (u v : nat -> R) lu lv :
  (forall n, u n = v n)
  -> is_LimInf_seq u lu -> is_LimInf_seq v lv
  -> lu = lv.
Proof.
  move => Heq Hu Hv.
  apply is_LimInf_seq_correct in Hu ; apply is_LimInf_seq_correct in Hv.
  apply (Rbar_is_liminf_eq (fun n : nat => Finite (u n)) (fun n : nat => Finite (v n))) 
  => // n ; by rewrite Heq.
Qed.

(** * LimSup, LimInf and Rbar_opp *)

Lemma is_limsup_seq_opp (u : nat -> R) (l : Rbar) :
  is_LimInf_seq u l -> is_LimSup_seq (fun n => - u n) (Rbar_opp l).
Proof.
  case: l => [l | | ] /= Hu.
  
  move => eps ; case: (Hu eps) => {Hu} Hu [N Hu'] ; split.
  clear N Hu' => N.
  case: (Hu N) => {Hu} n [Hn Hu].
  exists n ; split.
  by [].
  rewrite /Rminus -Ropp_plus_distr.
  by apply Ropp_lt_contravar.
  exists N => n Hn.
  rewrite -(Ropp_involutive eps) -Ropp_plus_distr.
  by apply Ropp_lt_contravar, Hu'.
  
  move => M.
  case: (Hu (-M)) => N {Hu} Hu.
  exists N => n Hn.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  by apply Hu.
  
  move => M N.
  case: (Hu (-M) N) => {Hu} n [Hn Hu].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
Qed.
Lemma LimSup_seq_opp (u : nat -> R) :
  LimSup_seq (fun n => - u n) = Rbar_opp (LimInf_seq u).
Proof.
  rewrite /LimInf_seq ; case: ex_LimInf_seq => /= li Hli.
  apply is_limsup_seq_opp in Hli.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= ls Hls.
  by apply (is_LimSup_seq_eq (fun n : nat => - u n) (fun n : nat => - u n)).
Qed.

Lemma is_liminf_seq_opp (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l -> is_LimInf_seq (fun n => - u n) (Rbar_opp l).
Proof.
  case: l => [l | | ] /= Hu.
  
  move => eps ; case: (Hu eps) => {Hu} Hu [N Hu'] ; split.
  clear N Hu' => N.
  case: (Hu N) => {Hu} n [Hn Hu].
  exists n ; split.
  by [].
  rewrite -(Ropp_involutive eps) -Ropp_plus_distr.
  by apply Ropp_lt_contravar.
  exists N => n Hn.
  rewrite /Rminus -Ropp_plus_distr.
  by apply Ropp_lt_contravar, Hu'.
  
  move => M N.
  case: (Hu (-M) N) => {Hu} n [Hn Hu].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.

  move => M.
  case: (Hu (-M)) => N {Hu} Hu.
  exists N => n Hn.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  by apply Hu.
Qed.
Lemma LimInf_seq_opp (u : nat -> R) :
  LimInf_seq (fun n => - u n) = Rbar_opp (LimSup_seq u).
Proof.
  rewrite /LimInf_seq ; case: ex_LimInf_seq => /= li Hli.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= ls Hls.
  apply is_liminf_seq_opp in Hls.
  by apply (is_LimInf_seq_eq (fun n : nat => - u n) (fun n : nat => - u n)).
Qed.
















