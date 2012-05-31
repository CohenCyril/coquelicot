Require Import Reals.
Require Import Deriv_fct RInt.
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

Hypothesis Cu1 : forall x, continuity_pt (fun u => u1 u) x.
Hypothesis Iu1 : forall a b, ex_RInt (fun u => u1 u) a b.
Hypothesis Du1 : forall x, ex_derive (fun u => u1 u) x.

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
rewrite Rplus_opp_r Rmult_0_r Ropp_0 Rplus_0_r.
rewrite RInt_null Rmult_0_r Rplus_0_r.
apply Rplus_eq_reg_l with (- f x t).
field_simplify.
2: exact Zc.
rewrite Rmult_1_r.
Abort.

End Gamma.

End DAlembert.
