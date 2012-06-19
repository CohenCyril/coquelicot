Require Import Reals.
Require Import Rcomplements Derive RInt Locally Differential.
Require Import AutoDerive.
Require Import ssreflect.

Open Local Scope R_scope.

Ltac auto_derive_2 :=
  match goal with
  | |- is_derive_n ?f 2 ?x ?d =>
    auto_derive_fun f ;
    match goal with
    | |- (forall x, _ -> is_derive _ x (@?d x)) -> _ =>
      let H := fresh "H" in
      let u := fresh "u" in
      intro H ;
      apply (is_derive_ext d) ;
      [ intro u ;
        apply sym_eq, is_derive_unique ;
        apply H
      | auto_derive ] ;
      clear H
    end
  end.

Section DAlembert.

Parameter c : R.

Hypothesis Zc : c <> 0.

Parameter u0 : R -> R.

Hypothesis Du0 : forall x, ex_derive (fun u => u0 u) x.
Hypothesis D2u0 : forall x, ex_derive_n (fun u => u0 u) 2 x.

Section Alpha.

Definition alpha x t := 1/2 * (u0 (x + c * t) + u0 (x - c * t)).
Definition alpha20 x t := 1/2 * (Derive_n u0 2 (x + c * t) + Derive_n u0 2 (x - c * t)).
Definition alpha02 x t := c^2/2 * (Derive_n u0 2 (x + c * t) + Derive_n u0 2 (x - c * t)).

Lemma alpha_20_lim :
  forall x t, is_derive_n (fun u => alpha u t) 2 x (alpha20 x t).
Proof.
intros x t.
unfold alpha.
auto_derive_2.
repeat split ; apply Du0.
repeat split ; apply D2u0.
unfold alpha20, Derive_n, Rminus.
ring.
Qed.

Lemma alpha_02_lim :
  forall x t, is_derive_n (fun u => alpha x u) 2 t (alpha02 x t).
Proof.
intros x t.
unfold alpha.
auto_derive_2.
repeat split ; apply Du0.
repeat split ; apply D2u0.
unfold alpha02, Derive_n, Rminus, Rdiv.
ring.
Qed.

End Alpha.

Parameter u1 : R -> R.

Hypothesis Du1 : forall x, ex_derive (fun u => u1 u) x.

Lemma Cu1 : forall x, continuity_pt (fun u => u1 u) x.
intros x eps Heps.
destruct (Du1 x) as (l,Hl).
(* *)
case (Req_dec l 0); intros Hleq.
apply equiv_deriv_pt_lim_0 in Hl.
destruct (Hl (mkposreal eps Heps)) as (d,Hd).
exists (Rmin d 1); split.
apply Rmin_case.
apply cond_pos.
apply Rlt_0_1.
simpl in Hd; unfold dist; simpl; unfold R_dist; simpl.
intros y (_,Hy).
replace  (u1 y - u1 x) with ((u1 y - u1 x - l * (y - x))).
apply Rle_lt_trans with (eps * Rabs (y - x)).
apply Hd.
apply Rlt_le_trans with (1:=Hy).
apply Rmin_l.
pattern eps at 2; rewrite <- (Rmult_1_r eps).
apply Rmult_lt_compat_l.
apply Heps.
apply Rlt_le_trans with (1:=Hy).
apply Rmin_r.
rewrite Hleq; ring.
(* *)
apply equiv_deriv_pt_lim_0 in Hl.
destruct (Hl (pos_div_2 (mkposreal eps Heps))) as (d,Hd).
exists (Rmin d (Rmin 1 ((eps/2)/Rabs l))).
split.
apply Rmin_case.
apply cond_pos.
apply Rmin_case.
apply Rlt_0_1.
apply Rdiv_lt_0_compat.
apply Rdiv_lt_0_compat.
exact Heps.
exact Rlt_0_2.
now apply Rabs_pos_lt.
simpl in Hd; unfold dist; simpl; unfold R_dist; simpl.
intros y (_,Hy).
replace  (u1 y - u1 x) with ((u1 y - u1 x - l * (y - x))+ (l*(y-x))) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var eps).
apply Rplus_lt_compat.
apply Rle_lt_trans with (eps / 2 * Rabs (y - x)).
apply Hd.
apply Rlt_le_trans with (1:=Hy).
apply Rmin_l.
pattern (eps/2) at 2; rewrite <- (Rmult_1_r (eps/2)).
apply Rmult_lt_compat_l.
unfold Rdiv ; apply Rmult_lt_0_compat ; 
  [apply Heps | apply Rinv_0_lt_compat, Rlt_0_2].
apply Rlt_le_trans with (1:=Hy).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs l *  (eps / 2 / Rabs l)).
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
apply Rlt_le_trans with (1:=Hy).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
right; field.
now apply Rabs_no_R0.
Qed.

Lemma Iu1: forall a b, ex_RInt (fun u => u1 u) a b.
intros a b.
case (Rle_or_lt a b); intros H.
apply ex_RInt_correct_3.
apply continuity_implies_RiemannInt.
exact H.
intros x Hx.
apply Cu1.
apply ex_RInt_bound.
apply ex_RInt_correct_3.
apply continuity_implies_RiemannInt.
left; exact H.
intros x Hx.
apply Cu1.
Qed.


Section Beta.

Definition beta (x t : R) := 1/(2*c) * RInt (fun u => u1 u) (x - c * t) (x + c * t).
Definition beta20 x t := 1/(2*c) * (Derive (fun u => u1 u) (x + c * t) - Derive (fun u => u1 u) (x - c * t)).
Definition beta02 x t := c/2 * (Derive (fun u => u1 u) (x + c * t) - Derive (fun u => u1 u) (x - c * t)).

Lemma beta20_lim :
  forall x t, is_derive_n (fun u => beta u t) 2 x (beta20 x t).
Proof.
intros x t.
unfold beta.
auto_derive_2.
split.
apply Iu1.
repeat split.
apply Locally.locally_forall.
apply Cu1.
apply Locally.locally_forall.
apply Cu1.
repeat split ; apply Du1.
unfold beta20, Rminus.
ring.
Qed.

Lemma beta02_lim :
  forall x t, is_derive_n (fun u => beta x u) 2 t (beta02 x t).
Proof.
intros x t.
unfold beta.
auto_derive_2.
split.
apply Iu1.
repeat split.
apply Locally.locally_forall.
apply Cu1.
apply Locally.locally_forall.
apply Cu1.
repeat split ; apply Du1.
unfold beta02, Rminus, Rdiv.
now field.
Qed.

End Beta.

Hypothesis f : R -> R -> R.

Section Gamma.

Definition gamma x t := 1/(2*c) * RInt (fun tau => RInt (fun xi => f xi tau) (x - c * (t - tau)) (x + c * (t - tau))) 0 t.
Definition gamma20 x t := 1/(2*c) * RInt (fun tau => Derive (fun u => f u tau) (x + c * (t - tau)) - Derive (fun u => f u tau) (x - c * (t - tau))) 0 t.
Definition gamma02 x t := (f x t + c/2 * RInt (fun tau => Derive (fun u => f u tau) (x + c * (t - tau)) - Derive (fun u => f u tau) (x - c * (t - tau))) 0 t).

Lemma gamma20_lim :
  forall x t, is_derive_n (fun u => gamma u t) 2 x (gamma20 x t).
Proof.
intros x t.
unfold gamma.
auto_derive_2.
admit.
admit.
unfold gamma20.
ring_simplify.
apply f_equal.
apply RInt_ext => z _.
now rewrite 4!Rmult_1_l 2!Rplus_0_r.
Qed.

Lemma RInt_null : forall g a, RInt g a a = 0.
Proof.
intros g a.
apply Rmult_eq_reg_r with 2.
rewrite Rmult_plus_distr_l Rmult_0_l Rmult_1_r.
rewrite -{1}(Ropp_involutive (RInt g a a)).
rewrite RInt_swap.
apply Rplus_opp_l.
apply Rgt_not_eq.
apply Rlt_R0_R2.
Qed.

Lemma gamma02_lim :
  forall x t, is_derive_n (fun u => gamma x u) 2 t (gamma02 x t).
Proof.
intros x t.
unfold gamma.
auto_derive_2.
admit.
admit.
unfold gamma02.
ring_simplify.
(* rewrite Rplus_opp_r Rmult_0_r Ropp_0 Rplus_0_r.
rewrite RInt_null Rmult_0_r Rplus_0_r.
apply Rplus_eq_reg_l with (- f x t).
field_simplify.
2: exact Zc.
rewrite Rmult_1_r.*)
Abort.

End Gamma.

End DAlembert.
