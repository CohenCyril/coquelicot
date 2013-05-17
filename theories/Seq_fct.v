Require Import Reals ssreflect.
Require Import Rcomplements Locally.
Require Import Lim_seq Sup_seq Lim_fct Derive Series.

Open Scope R_scope.

(** * Sequence of functions *)

(** ** Definitions *)

Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) :=
  forall x : R, D x -> ex_lim_seq (fun n => fn n x).

Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) :=
  forall eps : posreal, exists N : nat, 
  forall (n : nat) (x : R), D x -> (N <= n)%nat
    -> Rabs (fn n x - (Lim_seq (fun n => fn n x))) < eps.
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) :=
  forall eps : posreal, exists N : nat, 
  forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat
    -> Rabs (fn n x - fn m x) < eps.

(** equivalences with standard library *)

Lemma CVU_dom_equiv (fn : nat -> R -> R) (f : R -> R) (x : R) (r : posreal) :
  (forall y, (Boule x r y) -> f y = Lim_seq (fun n => fn n y)) ->
  (CVU fn f x r <-> CVU_dom fn (Boule x r)).
Proof.
  split ; move => Hcvu.
  have Hf : forall y, Boule x r y -> is_lim_seq (fun n => fn n y) (f y).
    move => y Hy [e He] /=.
    case: (Hcvu e He) => {Hcvu} N Hcvu.
    exists N => n Hn.
    rewrite -Ropp_minus_distr' Rabs_Ropp.
    by apply Hcvu.
  move => [e He] /=.
  case: (Hcvu e He) => {Hcvu} N Hcvu.
  exists N => n y Hy Hn.
  rewrite (is_lim_seq_unique (fun n0 : nat => fn n0 y) _ (Hf y Hy)).
  rewrite -Ropp_minus_distr' Rabs_Ropp.
  by apply Hcvu.
  
  move => e He ; set eps := mkposreal e He.
  case: (Hcvu eps) => {Hcvu} N Hcvu.
  exists N => n y Hn Hy.
  rewrite -Ropp_minus_distr' Rabs_Ropp (H y Hy).
  by apply Hcvu.
Qed.

(** Various inclusions and equivalence between definitions *)

Lemma CVU_CVS_dom (fn : nat -> R -> R) (D : R -> Prop) :
  CVU_dom fn D -> CVS_dom fn D.
Proof.
  move => Hcvu x Hx.
  exists (Lim_seq (fun n => fn n x)) => eps.
  case: (Hcvu eps) => {Hcvu} N Hcvu.
  exists N => n Hn.
  by apply Hcvu.
Qed.
Lemma CVU_dom_cauchy (fn : nat -> R -> R) (D : R -> Prop) :
  CVU_dom fn D <-> CVU_cauchy fn D.
Proof.
  split => H eps.
(* CVU_dom -> CVU_cauchy *)
  case: (H (pos_div_2 eps)) => {H} N /= H.
  exists N => n m x Hx Hn Hm.
  rewrite (double_var eps).
  replace (fn n x - fn m x) 
    with ((fn n x - Lim_seq (fun n0 : nat => fn n0 x))
      - (fn m x - Lim_seq (fun n0 : nat => fn n0 x)))
    by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _) ; rewrite Rabs_Ropp.
  apply Rplus_lt_compat ; by apply H.
(* CVU_cauchy -> CVU_dom *)
  rewrite /Lim_seq.
  case: (H (pos_div_2 eps)) => {H} N /= H.
  exists N => n x Hx Hn.
  rewrite /LimSup_seq ; case: ex_LimSup_seq ; case => [ls | | ] /= Hls.
  rewrite /LimInf_seq ; case: ex_LimInf_seq ; case => [li | | ] /= Hli.
  replace (fn n x - (ls + li) / 2)
    with (((fn n x - ls) + (fn n x - li))/2)
    by field.
  rewrite Rabs_div ; [ | by apply Rgt_not_eq, Rlt_R0_R2].
  rewrite (Rabs_pos_eq 2) ; [ | by apply Rlt_le, Rlt_R0_R2].
  rewrite Rlt_div_l ; [ | by apply Rlt_R0_R2].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (eps * 2) with (eps + eps) by ring.
  apply Rplus_lt_compat ; apply Rabs_lt_between'.
  case: (Hls (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
  case: (H0 N) => {H0} m [Hm H0].
  apply Rlt_trans with (fn m x - eps/2).
  replace (ls - eps) 
    with ((ls - eps / 2) - eps/2)
    by field.
  by apply Rplus_lt_compat_r.
  replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
  replace (fn m x - eps / 2) with ((fn m x - fn n x) + (fn n x - eps/2)) by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  apply Rlt_trans with (fn (n+N0)%nat x + eps/2).
  replace (fn n x) with (fn (n + N0)%nat x + (fn n x - fn (n+N0)%nat x)) by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  replace (ls + eps) with ((ls + eps/2) + eps/2) by field.
  apply Rplus_lt_compat_r.
  apply H1 ; by intuition.
  case: (Hli (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
  apply Rlt_trans with (fn (n+N0)%nat x - eps/2).
  replace (li - eps) with ((li - eps/2) - eps/2) by field.
  apply Rplus_lt_compat_r.
  apply H1 ; by intuition.
  replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
  replace (fn (n + N0)%nat x - eps / 2) 
    with ((fn (n + N0)%nat x - fn n x) + (fn n x - eps/2))
    by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  case: (H0 N) => {H0} m [Hm H0].
  apply Rlt_trans with (fn m x + eps/2).
  replace (fn n x) with (fn m x + (fn n x - fn m x)) by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  replace (li + eps) 
    with ((li + eps / 2) + eps/2)
    by field.
  by apply Rplus_lt_compat_r.
  case: (Hli (fn n x + eps / 2)) => {Hls Hli} N0 H0.
  move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn (N + N0)%nat x)
    with (fn n x + (fn (N + N0)%nat x - fn n x))
    by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  case: (Hli (fn n x - eps / 2) N) => {Hls Hli} m [Hm H0].
  contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn m x) with (eps/2 + (fn m x - eps/2)) by ring.
  replace (fn n x - eps / 2) 
    with ((fn n x - fn m x) + (fn m x - eps/2)) by ring.
  apply Rplus_lt_compat_r, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  case: (Hls (fn n x + eps / 2) N) => {Hls} m [Hm H0].
  contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn m x) with (fn n x + (fn m x - fn n x)) by ring.
  apply Rplus_lt_compat_l, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  case: (Hls (fn n x - eps / 2)) => {Hls} N0 H0.
  move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn (N + N0)%nat x)
    with (eps/2 + (fn (N + N0)%nat x - eps/2))
    by ring.
  replace (fn n x - eps / 2) 
    with ((fn n x - fn (N+N0)%nat x) + (fn (N+N0)%nat x - eps/2)) by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
Qed.

Lemma CVU_dom_include (fn : nat -> R -> R) (D1 D2 : R -> Prop) :
  (forall y, D2 y -> D1 y) -> CVU_dom fn D1 -> CVU_dom fn D2.
Proof.
  move => H H1 eps.
  case: (H1 eps) => {H1} N H1.
  exists N => n x Hx Hn.
  apply: H1.
  by apply H.
  exact: Hn.
Qed.

(** ** Limits, integrals and differentiability *)

Definition is_open (D : R -> Prop) :=
  forall x, D x -> locally D x.
Definition is_connex (D : R -> Prop) :=
  forall a b x, D a -> D b -> a <= x <= b -> D x.

Lemma CVU_limits_open (fn : nat -> R -> R) (D : R -> Prop) :
  is_open D
  -> CVU_dom fn D
  -> (forall x n, D x -> ex_lim (fn n) x)
  -> forall x, D x -> ex_lim_seq (fun n => Lim (fn n) x) 
    /\ ex_lim (fun y => Lim_seq (fun n => fn n y)) x
    /\ Lim_seq (fun n => Lim (fn n) x) = Lim (fun y => Lim_seq (fun n => fn n y)) x.
Proof.
  move => Ho Hfn Hex x Hx.
  have H : ex_lim_seq (fun n : nat => Lim (fn n) x).
    apply CVU_dom_cauchy in Hfn.
    apply ex_lim_seq_cauchy_corr => eps.
    case: (Hfn (pos_div_2 eps)) => {Hfn} /= N Hfn.
    exists N => n m Hn Hm.
    case: (Hex x n Hx) => ln Hex_n ;
    rewrite (is_lim_unique _ _ _ Hex_n).
    case: (Hex x m Hx) => {Hex} lm Hex_m ;
    rewrite (is_lim_unique _ _ _ Hex_m).
    case: (Hex_n (pos_div_2 (pos_div_2 eps))) => {Hex_n} /= dn Hex_n.
    case: (Hex_m (pos_div_2 (pos_div_2 eps))) => {Hex_m} /= dm Hex_m.
    case: (Ho x Hx) => {Ho} d0 Ho.
    set y := x + Rmin (Rmin dn dm) d0 / 2.
    have Hd : 0 < Rmin (Rmin dn dm) d0 / 2.
      apply Rdiv_lt_0_compat.
      apply Rmin_case ; [ | by apply d0].
      apply Rmin_case ; [ by apply dn | by apply dm].
      exact: Rlt_R0_R2.
    have Hy : Rabs (y - x) < d0.
      rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
      rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
      apply Rle_lt_trans with (d0/2).
      apply Rmult_le_compat_r.
      by intuition.
      exact: Rmin_r.
      rewrite -(Rplus_0_l (d0/2)) {2}(double_var d0).
      by apply Rplus_lt_compat_r, is_pos_div_2.
    move : (Ho y Hy) => {Ho Hy} Hy.
    replace (ln - lm) 
      with (- (fn n y - ln) + (fn m y - lm) + (fn n y - fn m y))
      by ring.
    rewrite (double_var eps) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    rewrite (double_var (eps/2)) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    rewrite Rabs_Ropp ; apply Hex_n.
    rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
    apply Rle_lt_trans with (Rmin dn dm / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_l.
    apply Rle_lt_trans with (dn / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_l.
    rewrite -(Rplus_0_l (dn/2)) {2}(double_var dn).
    by apply Rplus_lt_compat_r, is_pos_div_2.
    apply Rgt_not_eq, Rlt_gt, Rminus_lt_0.
    rewrite /y ; by ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    apply Hex_m.
    rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
    apply Rle_lt_trans with (Rmin dn dm / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_l.
    apply Rle_lt_trans with (dm / 2).
    apply Rmult_le_compat_r.
    by intuition.
    exact: Rmin_r.
    rewrite -(Rplus_0_l (dm/2)) {2}(double_var dm).
    by apply Rplus_lt_compat_r, is_pos_div_2.
    apply Rgt_not_eq, Rlt_gt, Rminus_lt_0.
    rewrite /y ; by ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
    by apply Hfn.
  split.
  exact: H.
  apply Lim_seq_correct in H.
  move: (Lim_seq (fun n : nat => Lim (fn n) x)) H => l H.
  have H0 : is_lim (fun y : R => Lim_seq (fun n : nat => fn n y)) x l.
    move => eps.
    case: (Hfn (pos_div_2 (pos_div_2 eps))) => {Hfn} /= n1 Hfn.
    case: (H (pos_div_2 (pos_div_2 eps))) => {H} /= n2 H.
    set n := (n1 + n2)%nat.
    move: (fun y Hy => Hfn n y Hy (le_plus_l _ _)) => {Hfn} Hfn.
    move: (H n (le_plus_r _ _)) => {H} H.
    move: (Hex x n Hx) => {Hex} Hex.
    apply Lim_correct in Hex.
    case: (Hex (pos_div_2 eps)) => {Hex} /= d1 Hex.
    case: (Ho x Hx) => {Ho} /= d0 Ho.
    have Hd : 0 < Rmin d0 d1.
      apply Rmin_case ; [by apply d0 | by apply d1].
    exists (mkposreal _ Hd) => /= y Hy Hxy.
    replace (Lim_seq (fun n0 : nat => fn n0 y) - l)
      with ((Lim (fn n) x - l)
            - (fn n y - Lim_seq (fun n : nat => fn n y))
            + (fn n y - Lim (fn n) x))
      by ring.
    rewrite (double_var eps) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    rewrite (double_var (eps/2)) ;
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    exact: H.
    rewrite Rabs_Ropp ; apply Hfn.
    by apply Ho, Rlt_le_trans with (1 := Hy), Rmin_l.
    apply Hex.
    by apply Rlt_le_trans with (1 := Hy), Rmin_r.
    exact: Hxy.
  split.
  by exists l.
  by apply sym_eq, is_lim_unique.
Qed.
Lemma CVU_cont_open (fn : nat -> R -> R) (D : R -> Prop) :
  is_open D ->
  CVU_dom fn D ->
  (forall n, forall x, D x -> continuity_pt (fn n) x)
    -> forall x, D x -> continuity_pt (fun y => Lim_seq (fun n => fn n y)) x.
Proof.
  move => Ho Hfn Hc x Hx.
  case: (fun H => CVU_limits_open fn D Ho Hfn H x Hx) 
    => [{x Hx} x n Hx | Hex_s [Hex_f Heq]].
  exists (fn n x) => eps.
  case: (Hc n x Hx eps (cond_pos eps)) => {Hc} d [Hd Hc].
  exists (mkposreal d Hd) => /= y Hy Hxy.
  apply (Hc y).
  split.
  split.
  exact: I.
  by apply sym_not_eq, Hxy.
  exact: Hy.
  apply Lim_correct in Hex_f.
  rewrite -Heq in Hex_f => {Heq}.
  replace (Lim_seq (fun n : nat => Lim (fn n) x))
    with (Lim_seq (fun n : nat => (fn n) x)) in Hex_f.
  move => e He.
  case: (Hex_f (mkposreal e He)) => {Hex_f} /= delta Hex_f.
  exists delta ; split => [ | y [[_ Hxy] Hy]].
  by apply delta.
  apply Hex_f.
  exact: Hy.
  by apply sym_not_eq.
  apply Lim_seq_ext => n.
  apply sym_eq, is_lim_unique.
  move => eps.
  case: (Hc n x Hx eps (cond_pos eps)) => {Hc} d [Hd Hc].
  exists (mkposreal d Hd) => /= y Hy Hxy.
  apply (Hc y).
  split.
  split.
  exact: I.
  by apply sym_not_eq, Hxy.
  exact: Hy.
Qed.
(*Lemma CVU_Nint (fn Fn : nat -> R -> R) (F : R -> R) (a b : R) (Hab : a < b) :
  CVU_dom fn (fun x => a <= x <= b)
  -> (forall n, forall x, a <= x <= b -> continuity_pt (fn n) x)
  -> (forall n x, a <= x <= b -> is_derive (Fn n) x (fn n x)) -> (forall n, Fn n a = 0)
  -> (forall x, a <= x <= b -> is_derive F x (Lim_seq (fun n => fn n x))) -> (F a = 0)
  -> CVU_dom Fn (fun x => a <= x <= b) 
    /\ (forall x, a <= x <= b -> Lim_seq (fun n => Fn n x) = F x).
Admitted. (** Admitted *)
Lemma CVU_Rint (fn : nat -> R -> R) (a b : R) (Hab : a < b) :
  CVU_dom fn (fun x => a <= x <= b)
  -> (forall n, forall x, a <= x <= b -> continuity_pt (fn n) x)
  -> CVU_dom (fun n x => RInt (fn n) a x) (fun x => a <= x <= b) 
    /\ (forall x, a <= x <= b -> Lim_seq (fun n => RInt (fn n) a x) = RInt (fun y => Lim_seq (fun n => fn n y)) a x).
Admitted. (** Admitted *)*)
Lemma CVU_Derive (fn : nat -> R -> R) (D : R -> Prop) :
  is_open D -> is_connex D
  -> CVU_dom fn D
  -> (forall n x, D x -> ex_derive (fn n) x)
  -> (forall n x, D x -> continuity_pt (Derive (fn n)) x)
  -> CVU_dom (fun n x => Derive (fn n) x) D
  -> (forall x , D x ->
       (is_derive (fun y => Lim_seq (fun n => fn n y)) x (Lim_seq (fun n => Derive (fn n) x)))).
Proof.
  move => Ho Hc Hfn Edn Cdn Hdn.
  
  set rn := fun x n h => match (Req_EM_T h 0) with
    | left _ => Derive (fn n) x
    | right _ => (fn n (x+h) - fn n x)/h
  end.
  
  have Ho' : forall x : R, D x -> is_open (fun h : R => D (x + h)).
    move => x Hx h Hh.
    case: (Ho _ Hh) => d Hd.
    exists d => /= y Hy.
    apply Hd ; ring_simplify (x + y - (x + h)).
    by apply Hy.

  have Crn : forall x, D x -> forall n h, D (x+h) -> is_lim (rn x n) h (rn x n h).
    move => x Hx n h Hh.
    rewrite {2}/rn ; case: (Req_EM_T h 0) => [-> | Hh0].
    move => eps.
    suff H : locally (fun y : R => y <> 0 ->
      Rabs ((fn n (x + y) - fn n x) / y - Derive (fn n) x) < eps) 0.
    case: H => d H.
    exists d => y Hy Hxy.
    rewrite /rn ; case: Req_EM_T => // _ ; by apply H.
    move: (Edn n x Hx) => {Edn} Edn.
    apply Derive_correct in Edn.
    case: (Edn eps (cond_pos eps)) => {Edn} delta Edn.
    exists delta => y Hy Hxy.
    rewrite Rminus_0_r in Hy.
    by apply Edn.
    
    have H : continuity_pt (fun h => ((fn n (x + h) - fn n x) / h)) h.
      apply derivable_continuous_pt.
      apply derivable_pt_div.
      apply derivable_pt_minus.
      apply derivable_pt_comp.
      apply (derivable_pt_plus (fun _ => x) (fun h => h) h).
      exact: derivable_pt_const.
      exact: derivable_pt_id.
      exists (Derive (fn n) (x + h)) ; by apply Derive_correct, Edn.
      exact: derivable_pt_const.
      exact: derivable_pt_id.
      exact: Hh0.
    
    move => eps.
    case: (H eps (cond_pos eps)) => {H} d [Hd H].
    have Hd0 : 0 < Rmin d (Rabs h).
      apply Rmin_case.
      exact: Hd.
      by apply Rabs_pos_lt.
    exists (mkposreal _ Hd0) => /= y Hy Hhy.
    rewrite /rn ; case: Req_EM_T => /= Hy'.
    contradict Hy.
    apply Rle_not_lt ; rewrite Hy' Rminus_0_l Rabs_Ropp ; by apply Rmin_r.
    apply (H y) ; split.
    split.
    exact: I.
    by apply sym_not_eq.
    by apply Rlt_le_trans with (1 := Hy), Rmin_l.


  have Hrn : forall x, D x -> CVU_dom (rn x) (fun h : R => D (x + h)).
    move => x Hx.
    apply CVU_dom_cauchy => eps.
    apply CVU_dom_cauchy in Hdn.
    case: (Hdn eps) => {Hdn} /= N Hdn.
    exists N => n m h Hh Hn Hm.
    rewrite /rn ; case: Req_EM_T => Hh0.
    exact: (Hdn n m x Hx Hn Hm).
    replace ((fn n (x + h) - fn n x) / h - (fn m (x + h) - fn m x) / h)
      with (((fn n (x + h) - fn m (x + h)) - (fn n x - fn m x))/h)
      by (field ; auto).
    case: (MVT_gen (fun x => (fn n x - fn m x)) x (x+h)) => [y Hy | y Hy | z [Hz ->]].
    apply ex_derive_minus ; apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    split ; apply Rlt_le ; by apply Hy.
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    split ; apply Rlt_le ; by apply Hy.
    apply derivable_continuous_pt, derivable_pt_minus.
    exists (Derive (fn n) y) ; apply Derive_correct, Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hy.
    exists (Derive (fn m) y) ; apply Derive_correct, Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hy.
    replace (Derive (fun x1 : R => fn n x1 - fn m x1) z * (x + h - x) / h)
      with (Derive (fun x1 : R => fn n x1 - fn m x1) z)
      by (field ; auto).
    rewrite Derive_minus.
    apply (Hdn n m z).
    apply (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hz.
    exact: Hn.
    exact: Hm.
    apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hz.
    apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
    apply Rmin_case ; [by apply Hx | by apply Hh].
    apply Rmax_case ; [by apply Hx | by apply Hh].
    by apply Hz.

  have Lrn : forall x, D x -> (forall (y : R) (n : nat),
    (fun h : R => D (x + h)) y -> ex_lim (rn x n) y).
    intros ; exists (rn x n y) ; by intuition.
  
  move => x Hx.
  
  case: (CVU_limits_open (rn x) _ (Ho' x Hx) (Hrn x Hx) (Lrn x Hx) 0) => [ | H [H0 H1]].
  by rewrite Rplus_0_r.
  
  have : ex_derive (fun y : R => Lim_seq (fun n : nat => fn n y)) x
    /\ Derive (fun y : R => Lim_seq (fun n : nat => fn n y)) x
      = (Lim_seq (fun n : nat => Derive (fn n) x)).
  
  split.
  case: H0 => df H0.
  exists df => e He.
  case: (H0 (mkposreal e He)) => {H0} /= delta H0.
  case: (Ho x Hx) => {Ho} dx Ho.
  have H2 : 0 < Rmin delta dx.
    apply Rmin_case ; [by apply delta | by apply dx].
  exists (mkposreal _ H2) => /= h Hh0 Hh.
  rewrite -Lim_seq_minus.
  rewrite /Rdiv (Rmult_comm _ (/h)) -Lim_seq_scal.
  replace (Lim_seq (fun n : nat => / h * (fn n (x + h) - fn n x)))
    with (Lim_seq (fun n : nat => rn x n h)).
  apply H0.
  rewrite Rminus_0_r ; apply Rlt_le_trans with (1 := Hh), Rmin_l.
  exact: Hh0.
  apply Lim_seq_ext => n.
  rewrite /rn /Rdiv ; case: Req_EM_T => // _ ; exact: Rmult_comm.
  apply CVU_CVS_dom with D.
  exact: Hfn.
  apply Ho.
  ring_simplify (x + h - x) ; apply Rlt_le_trans with (1 := Hh), Rmin_r.
  apply CVU_CVS_dom with D.
  exact: Hfn.
  apply Ho.
  rewrite Rminus_eq0 Rabs_R0 ; by apply dx.
  
  rewrite /Derive.
  replace (Lim_seq (fun n : nat => Lim (fun h : R => (fn n (x + h) - fn n x) / h) 0))
    with (Lim_seq (fun n : nat => Lim (rn x n) 0)).
  rewrite H1.
  case: H0 => drn H0.
  rewrite (is_lim_unique _ _ _ H0).
  apply is_lim_unique => eps.
  case: (H0 eps) => {H0} delta H0.
  case: (Ho x Hx) => {Ho} dx Ho.
  have H2 : 0 < Rmin delta dx.
    apply Rmin_case ; [by apply delta | by apply dx].
  exists (mkposreal _ H2) => /= h Hh0 Hh.
  rewrite -Lim_seq_minus.
  rewrite /Rdiv (Rmult_comm _ (/h)) -Lim_seq_scal.
  replace (Lim_seq (fun n : nat => / h * (fn n (x + h) - fn n x)))
    with (Lim_seq (fun n : nat => rn x n h)).
  apply H0.
  apply Rlt_le_trans with (1 := Hh0), Rmin_l.
  exact: Hh.
  apply Lim_seq_ext => n.
  rewrite /rn /Rdiv ; case: Req_EM_T => // _ ; exact: Rmult_comm.
  apply CVU_CVS_dom with D.
  exact: Hfn.
  apply Ho.
  ring_simplify (x + h - x) ; rewrite -(Rminus_0_r h) ;
  apply Rlt_le_trans with (1 := Hh0), Rmin_r.
  apply CVU_CVS_dom with D.
  exact: Hfn.
  apply Ho.
  rewrite Rminus_eq0 Rabs_R0 ; by apply dx.
  apply Lim_seq_ext => n.
  apply sym_eq, is_lim_unique.
  have Hx' : D (x + 0).
    by rewrite Rplus_0_r.
  rewrite (is_lim_unique _ _ _ (Crn x Hx n 0 Hx')).
  move: (Crn x Hx n 0 Hx') => H2 eps.
  case: (H2 eps) => {H2} delta H2.
  exists delta => y Hy Hy0.
  move: (H2 y Hy Hy0).
  rewrite {1}/rn ; by case: Req_EM_T.
  
  case => H2 H3.
  rewrite -H3.
  by apply Derive_correct.
Qed.

(** ** Series of functions *)

Lemma CVN_CVU_r (fn : nat -> R -> R) (r : posreal) :
  CVN_r fn r -> forall x, (Rabs x < r) -> exists e : posreal, 
    CVU (fun n => SP fn n) (fun x => Series (fun n => fn n x)) x e.
Proof.
  case => An [l [H H0]] x Hx.
  have H1 : ex_series An.
    apply ex_series_equiv_1.
    exists l => e He.
    case: (H e He) => {H} N H.
    exists N => n Hn.
    replace (sum_f_R0 An n) with (sum_f_R0 (fun k : nat => Rabs (An k)) n).
    by apply H.
    elim: n {Hn} => /= [ | n IH].
    apply Rabs_pos_eq.
    apply Rle_trans with (Rabs (fn O 0)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
    rewrite IH Rabs_pos_eq.
    by [].
    apply Rle_trans with (Rabs (fn (S n) 0)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.

  have H2 : is_lim_seq (fun n => Series (fun k => An (n + k)%nat)) 0.
    apply is_lim_seq_incr_1.
    apply is_lim_seq_ext with (fun n => Series An - sum_f_R0 An n).
    move => n ; rewrite (Series_decal_n An (S n)) /=.
    ring.
    by apply lt_O_Sn.
    by apply H1.
    apply is_lim_seq_plus with (Series An) (-Series An).
    by apply is_lim_seq_const.
    apply is_lim_seq_opp.
    rewrite /Series ;
    apply (is_lim_seq_ext (sum_f_R0 (fun k => An k))).
    elim => /= [ | n IH].
    by [].
    by rewrite IH.
    apply Lim_seq_correct, H1.
    ring.

  apply Rminus_lt_0 in Hx.
  set r0 := mkposreal _ Hx.
  exists r0 => e He ; set eps := mkposreal e He.
  case: (H2 eps) => {H2} N H2.
  exists N => n y Hn Hy.
  apply Rle_lt_trans with (2 := H2 (S n) (le_trans _ _ _ (le_n_Sn _) (le_n_S _ _ Hn))).
  rewrite Rminus_0_r /SP.
  rewrite (Series_decal_n (fun k : nat => fn k y) (S n)) /=.
  ring_simplify (sum_f_R0 (fun k : nat => fn k y) n +
    Series (fun k : nat => fn (S (n + k)) y) -
    sum_f_R0 (fun k : nat => fn k y) n).

  apply Rle_trans with (2 := Rle_abs _).
  apply Rle_trans with (Series (fun k : nat => Rabs (fn (S (n + k)) y))).
  apply Rabs_le_between ; rewrite -Lim_seq_opp /Series ; split.

  apply is_lim_seq_le with 
    (fun n0 : nat => - sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y)) n0)
    (sum_f_R0 (fun k : nat => fn (S (n + k)) y)).
  elim => /= [ | k IH].
  apply Ropp_le_cancel ; rewrite Ropp_involutive.
  by apply Rabs_maj2.
  rewrite Ropp_plus_distr ; apply Rplus_le_compat.
  by apply IH.
  apply Ropp_le_cancel ; rewrite Ropp_involutive.
  by apply Rabs_maj2.
  apply Lim_seq_correct, ex_lim_seq_opp.
  apply Comp_ex_series with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  apply Lim_seq_correct.
  apply Abs_ex_series.
  apply Comp_ex_series with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  
  apply is_lim_seq_le with 
    (sum_f_R0 (fun k : nat => fn (S (n + k)) y))
    (sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y))).
  elim => /= [ | k IH].
  by apply Rle_abs.
  apply Rplus_le_compat.
  by apply IH.
  apply Rle_abs.
  apply Lim_seq_correct.
  apply Abs_ex_series.
  apply Comp_ex_series with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  apply (is_lim_seq_ext (sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y)))).
  by [].
  apply Lim_seq_correct.
  apply (Comp_ex_series) with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  
  apply is_lim_seq_le with 
    (sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y)))
    (sum_f_R0 (fun k : nat => An (S (n + k)))).
  elim => /= [ | k IH].
  apply H0.
  rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  apply Rplus_le_compat.
  by apply IH.
  apply H0.
  rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  
  apply Lim_seq_correct.
  apply (Comp_ex_series) with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  
  apply Lim_seq_correct.
  by apply (ex_series_decal_n An (S n)).
  by apply lt_O_Sn.
  
  apply Abs_ex_series.
  apply (Comp_ex_series) with An.
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply H1.
Qed.