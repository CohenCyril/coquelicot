Require Import Reals Rcomplements Markov Floor.
Require Import Sup_seq Rbar_theory Total_sup ssreflect.
Open Scope R_scope.

(** * Limit sequence *)

Definition Lim_seq (u : nat -> R) : R := (real (Rbar_plus (LimSup_seq u) (LimInf_seq u)))/2.
Definition is_lim_seq (u : nat -> R) (l : R) :=
  forall eps : posreal, exists N : nat, forall n : nat,
    (N <= n)%nat -> Rabs (u n - l) < eps.
Definition ex_lim_seq (u : nat -> R) :=
  exists l, is_lim_seq u l.

Lemma is_lim_seq_correct (u : nat -> R) (l : R) :
  is_lim_seq u l <-> Rbar_is_lim_seq (fun n => Finite (u n)) (Finite l).
Proof.
  split => /= Hl eps ; case: (Hl eps) => {Hl} N Hl ; exists N => n Hn ;
  by apply Rabs_lt_between', Hl.
Qed.
Lemma Lim_seq_Rbar (u : nat -> R) :
  Lim_seq u = real (Rbar_lim_seq (fun n => Finite (u n))).
Proof.
  rewrite /Lim_seq /Rbar_lim_seq.
  rewrite (LimSup_seq_correct u) (LimInf_seq_correct u) /= ;
  case: (Rbar_plus _ _) => //= ; field.
Qed.

(** ** Compute limit *)

Lemma is_lim_seq_unique (u : nat -> R) :
  forall l, is_lim_seq u l -> Lim_seq u = l.
Proof.
  move => l ; move/is_lim_seq_correct => Hl ; rewrite Lim_seq_Rbar ;
  by rewrite (Rbar_is_lim_correct _ _ Hl).
Qed.
Lemma Lim_seq_correct (u : nat -> R) :
  ex_lim_seq u -> is_lim_seq u (Lim_seq u).
Proof.
  intros (l,H).
  cut (Lim_seq u = l).
    intros ; rewrite H0 ; apply H.
  apply is_lim_seq_unique, H.
Qed.

(** * Operations *)

Lemma is_lim_seq_CL (u v : nat -> R) (a l1 l2 : R) {l : R} :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l = l1 + a * l2 ->
    is_lim_seq (fun n => u n + a * v n) l.
Proof.
  intros Hf Hg Hl e0 ; rewrite Hl ; clear Hl.
  assert (He : 0 < e0 / (1 + Rabs a)).
    unfold Rdiv ; apply Rmult_lt_0_compat ; [apply e0 | apply Rinv_0_lt_compat] ;
    apply Rlt_le_trans with (1 := Rlt_0_1) ; rewrite -{1}(Rplus_0_r 1) ;
    apply Rplus_le_compat_l, Rabs_pos.
  set (eps := mkposreal _ He).
  move: (Hf eps) => {Hf} [Nf Hf].
  move: (Hg eps) => {Hg} [Ng Hg].
  exists (Nf+Ng)%nat ; intros.
  assert (Rw : u n + a * v n - (l1 + a * l2) = (u n - l1) + a * (v n - l2)) ; 
  [ ring | rewrite Rw ; clear Rw].
  assert (Rw : (pos e0) = eps + Rabs a * eps) ;
  [ simpl ; field ; apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1) ; 
    rewrite -{1}(Rplus_0_r 1) ; apply Rplus_le_compat_l, Rabs_pos
  | rewrite Rw ; clear Rw].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_le_compat.
  apply Hf, le_trans with (2 := H) ; intuition.
  rewrite Rabs_mult ; apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, Hg, le_trans with (2 := H) ; intuition.
Qed.
Lemma ex_lim_seq_CL (u v : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq v -> ex_lim_seq (fun n => u n + a * v n).
Proof.
  intros (lf,Hf) (lg,Hg).
  exists (lf + a * lg) ; apply (is_lim_seq_CL u v a lf lg) ; [apply Hf | apply Hg | ring].
Qed.
Lemma Lim_seq_CL (u v : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq (fun n => u n + a * v n) = Lim_seq u + a * Lim_seq v.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply (is_lim_seq_CL _ _ _ (Lim_seq u) (Lim_seq v)).
  apply Lim_seq_correct, H.
  apply Lim_seq_correct, H0.
  reflexivity.
Qed.

Lemma is_lim_seq_plus (u v : nat -> R) {l : R} (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l = l1 + l2 ->
    is_lim_seq (fun n => u n + v n) l.
Proof.
  intros.
  rewrite H1 ; clear H1 ; intros eps.
  assert (He2 : 0 < eps / 2) ; 
    [unfold Rdiv ; destruct eps ; apply Rmult_lt_0_compat ; intuition | ].
  elim (H (mkposreal _ He2)) ; clear H ; simpl ; intros N1 H.
  elim (H0 (mkposreal _ He2)) ; clear H0 ; simpl ; intros N2 H0.
  exists (N1+N2)%nat ; intros.
  assert (Rw : (u n + v n - (l1 + l2)) = (u n - l1) + (v n - l2)) ;
    [ring | rewrite Rw ; clear Rw].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite (double_var eps) ; apply Rplus_lt_compat ; intuition.
Qed.
Lemma Lim_seq_plus (u v : nat -> R) :
  let w := fun n => u n + v n in
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq w = Lim_seq u + Lim_seq v.
Proof.
  intros w (l1,Hu) (l2,Hv).
  apply is_lim_seq_unique.
  rewrite (is_lim_seq_unique _ _ Hu).
  rewrite (is_lim_seq_unique _ _ Hv).
  apply is_lim_seq_plus with (l1 := l1) (l2 := l2) ; intuition.
Qed.

Lemma is_lim_seq_const {a : R} :
  is_lim_seq (fun n => a) a.
Proof.
  intros eps ; exists O ; intros.
  unfold Rminus ; rewrite (Rplus_opp_r a) Rabs_R0 ; apply eps.
Qed.
Lemma Lim_seq_const (a : R) :
  Lim_seq (fun n => a) = a.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_const.
Qed.
Lemma is_lim_seq_inv_n :
  is_lim_seq (fun n => /INR n) 0.
Proof.
  intros eps.
  assert (He : 0 <= /eps) ; 
    [apply Rlt_le, Rinv_0_lt_compat, eps|].
  destruct (nfloor_ex _ He) as (N,HN).
  exists (S N) ; intros.
  assert (Rw : (pos eps) = INR n * (eps / INR n)) ; 
    [field ; apply Rgt_not_eq, Rlt_gt, lt_0_INR, lt_le_trans with (2 := H), lt_O_Sn 
    | rewrite Rw ; clear Rw].
  assert (Rw : Rabs (/ INR n - 0) = /eps * (eps/INR n)) ; 
    [rewrite Rminus_0_r Rabs_right ; intuition ; field ; split ; 
    [ apply Rgt_not_eq ; intuition | apply Rgt_not_eq, eps ]
    | rewrite Rw ; clear Rw ].
  apply Rmult_lt_compat_r.
  unfold Rdiv ; apply Rmult_lt_0_compat ; intuition ; apply eps.
  apply Rlt_le_trans with (1 := proj2 HN).
  rewrite <- S_INR ; apply le_INR, H.
Qed.
Lemma Lim_seq_inv_n (a : R) :
  Lim_seq (fun n => /INR n) = 0.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_inv_n.
Qed.

Lemma is_lim_seq_opp (u : nat -> R) (l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => -u n) (-l).
Proof.
  move => H eps ; case: (H eps) => {H} N H ; exists N => n Hn.
  replace (-u n--l) with (-(u n-l)) by ring ;
  rewrite Rabs_Ropp ; by apply H.
Qed.
Lemma ex_lim_seq_opp (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => -u n).
Proof.
  case => l Hl ; exists (-l) ; by apply is_lim_seq_opp.
Qed.

Lemma Lim_seq_scal (u : nat -> R) (a : R) :
  Lim_seq (fun n => a * u n) = a * Lim_seq u.
Proof.
  wlog: u a / (0 <= a) => [Hw | Ha].
    case: (Rle_lt_dec 0 a) => Ha.
    by apply Hw.
    apply Ropp_0_gt_lt_contravar, Rlt_le in Ha ; 
    move: (Hw (fun n => - u n) _ Ha) => {Hw}.
    rewrite /Lim_seq.
    have H : (forall u, Rbar_limsup_seq u = 
      Rbar_inf_seq (fun n => Rbar_sup_seq (fun m => u (n+m)%nat))).
      move => u0 ; rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq => ls Hls ;
      rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq => i Hi /=.
      apply (Rbar_is_inf_seq_rw (fun n : nat => Rbar_sup_seq (fun m : nat => u0 (n + m)%nat)) 
      (fun n : nat => Rbar_sup_seq (fun m : nat => u0 (n + m)%nat))) => //.
      by apply Rbar_limsup_caract_1.
    rewrite ?LimSup_seq_correct ?H => {H}.
    have H : (forall u, Rbar_liminf_seq u = 
      Rbar_sup_seq (fun n => Rbar_inf_seq (fun m => u (n+m)%nat))).
      move => u0 ; rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq => ls Hls ;
      rewrite /Rbar_sup_seq ; case: Rbar_ex_sup_seq => i Hi /=.
      apply (Rbar_is_sup_seq_rw (fun n : nat => Rbar_inf_seq (fun m : nat => u0 (n + m)%nat)) 
      (fun n : nat => Rbar_inf_seq (fun m : nat => u0 (n + m)%nat))) => //.
      by apply Rbar_liminf_caract_1.
    rewrite ?LimInf_seq_correct ?H => {H}.
    move => Hw.
    rewrite (Rbar_inf_seq_rw (fun n : nat =>
      Rbar_sup_seq (fun m : nat => Finite (a * u (n + m)%nat))) 
      (fun n : nat =>
      Rbar_sup_seq (fun m : nat => Finite (-a * -u (n + m)%nat)))).
    rewrite (Rbar_sup_seq_rw (fun n : nat =>
      Rbar_inf_seq (fun m : nat => Finite (a * u (n + m)%nat))) 
      (fun n : nat =>
      Rbar_inf_seq (fun m : nat => Finite (-a * -u (n + m)%nat)))).
    rewrite Hw => {Hw} ;
    rewrite Ropp_mult_distr_l_reverse -Ropp_mult_distr_r_reverse ;
    apply Rmult_eq_compat_l ; rewrite -Ropp_mult_distr_l_reverse ;
    apply Rmult_eq_compat_r.
    rewrite -Rbar_opp_real.
    have : (forall x y, Rbar_opp (Rbar_plus x y) = Rbar_plus (Rbar_opp x) (Rbar_opp y)).
      case => [x | | ] ; case => [y | | ] //= ; apply Rbar_finite_eq ; intuition.
    move => ->.
    rewrite Rbar_plus_comm.
    rewrite Rbar_inf_opp_sup Rbar_opp_involutive ;
    rewrite Rbar_sup_opp_inf Rbar_opp_involutive.
    rewrite (Rbar_inf_seq_rw (fun n : nat =>
      Rbar_opp (Rbar_inf_seq (fun m : nat => Finite (- u (n + m)%nat))))
      (fun n : nat => Rbar_sup_seq (fun m : nat => Finite (u (n + m)%nat)))).
    rewrite (Rbar_sup_seq_rw (fun n : nat =>
      Rbar_opp (Rbar_sup_seq (fun m : nat => Finite (- u (n + m)%nat))))
      (fun n : nat => Rbar_inf_seq (fun m : nat => Finite (u (n + m)%nat)))) //.
    move => n ; by rewrite -(Rbar_inf_opp_sup (fun m => Finite (u (n+m)%nat))).
    move => n ; by rewrite -(Rbar_sup_opp_inf (fun m => Finite (u (n+m)%nat))).
    move => n ; apply Rbar_inf_seq_rw => m ; apply Rbar_finite_eq ; ring.
    move => n ; apply Rbar_sup_seq_rw => m ; apply Rbar_finite_eq ; ring.
  
  rewrite /Lim_seq /LimSup_seq /LimInf_seq ;
  case: ex_LimSup_seq => ls' Hls' ; case: ex_LimSup_seq => ls Hls ;
  case: ex_LimInf_seq => li' Hli' ; case: ex_LimInf_seq => li Hli /=.
  apply Rle_lt_or_eq_dec in Ha ; case: Ha => Ha.
(* 0 < a *)
  replace ls' with (Rbar_mult_pos ls (mkposreal _ Ha)).
  replace li' with (Rbar_mult_pos li (mkposreal _ Ha)).
  case: (ls) ; case: (li) => //= ; intros ; field.
(* a*li = li'*)
  apply (is_LimInf_seq_eq (fun n => a * u n) (fun n => a * u n)) => // ;
  case: li Hli => [li | | ] /= Hli.
  move => eps ; have He : (0 < eps / a) ; 
  [apply Rdiv_lt_0_compat => // ; apply eps | set e := mkposreal _ He ].
  move: (Hli e) => {Hli} Hli.
  split ; [case: Hli => Hli _ | case: Hli => _ [N Hli]].
  move => N ; case: (Hli N) => {Hli} n Hli ; exists n ; intuition.
  replace (_*_+_) with (a * (li+e)).
  by apply Rmult_lt_compat_l.
  simpl ; field ; by apply Rgt_not_eq.
  exists N => n Hn.
  replace (_*_-_) with (a * (li-e)).
  by apply Rmult_lt_compat_l, Hli.
  simpl ; field ; by apply Rgt_not_eq.
  move => M ; case: (Hli (M/a)) => {Hli} N Hli ; 
  exists N => n Hn.
  replace M with (a*(M/a)).
  by apply Rmult_lt_compat_l, Hli.
  field ; by apply Rgt_not_eq.
  move => M N ; case: (Hli (M/a) N) => {Hli} n Hli.
  exists n ; replace M with (a*(M/a)) ; intuition.
  field ; by apply Rgt_not_eq.
  (* a*ls = ls'*)
  apply (is_LimSup_seq_eq (fun n => a * u n) (fun n => a * u n)) => // ;
  case: ls Hls => [ls | | ] /= Hls.
  move => eps ; have He : (0 < eps / a) ; 
  [apply Rdiv_lt_0_compat => // ; apply eps | set e := mkposreal _ He ].
  move: (Hls e) => {Hls} Hls.
  split ; [case: Hls => Hls _ | case: Hls => _ [N Hls]].
  move => N ; case: (Hls N) => {Hls} n Hls ; exists n ; intuition.
  replace (_*_-_) with (a * (ls-e)).
  by apply Rmult_lt_compat_l.
  simpl ; field ; by apply Rgt_not_eq.
  exists N => n Hn.
  replace (_*_+_) with (a * (ls+e)).
  by apply Rmult_lt_compat_l, Hls.
  simpl ; field ; by apply Rgt_not_eq.
  move => M N ; case: (Hls (M/a) N) => {Hls} n Hls.
  exists n ; replace M with (a*(M/a)) ; intuition.
  field ; by apply Rgt_not_eq.
  move => M ; case: (Hls (M/a)) => {Hls} N Hls ; 
  exists N => n Hn.
  replace M with (a*(M/a)).
  by apply Rmult_lt_compat_l, Hls.
  field ; by apply Rgt_not_eq.
(* a = 0 *)
  rewrite -Ha in Hls' Hli' |- *.
  replace ls' with (Finite 0).
  replace li' with (Finite 0).
  simpl ; field.
(* li' = 0*)
  apply (is_LimInf_seq_eq (fun n => 0 * u n) (fun n => 0 * u n)) => //= ;
  intuition ; [exists N | exists O] ; intuition ; ring_simplify ; 
  case: eps ; intuition.
(* ls' = 0*)
  apply (is_LimSup_seq_eq (fun n => 0 * u n) (fun n => 0 * u n)) => //= ;
  intuition ; [exists N | exists O] ; intuition ; ring_simplify ; 
  case: eps ; intuition.
Qed.


Lemma Lim_seq_ext:  forall u v, 
  (forall n, u n = v n) -> 
  Lim_seq u = Lim_seq v.
Proof.
intros u v H.
unfold Lim_seq, LimSup_seq, LimInf_seq.
destruct (ex_LimSup_seq u) as (lu1,Hlu1).
destruct (ex_LimSup_seq v) as (lv1,Hlv1).
destruct (ex_LimInf_seq u) as (lu2,Hlu2).
destruct (ex_LimInf_seq v) as (lv2,Hlv2).
simpl.
rewrite (is_LimSup_seq_eq _ _ _ _ H Hlu1 Hlv1).
rewrite (is_LimInf_seq_eq _ _ _ _ H Hlu2 Hlv2).
easy.
Qed.



