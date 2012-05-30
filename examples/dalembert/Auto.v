Require Import Reals.
Require Import Deriv_fct RInt.
Require Import AutoDerive.
Require Import ssreflect.
Require Import seq.

Open Local Scope R_scope.

Section DAlembert.

Parameter c : R.

Hypothesis Zc : c <> 0.

Parameter u0 : R -> R.

Hypothesis Du0 : forall x, ex_deriv (fun u => u0 u) x.
Hypothesis D2u0 : forall x, ex_deriv_n (fun u => u0 u) 2 x.

Section Alpha.

Definition alpha x t := 1/2 * (u0 (x + c * t) + u0 (x - c * t)).
Definition alpha20 x t := 1/2 * (Deriv_n u0 2 (x + c * t) + Deriv_n u0 2 (x - c * t)).
Definition alpha02 x t := c^2/2 * (Deriv_n u0 2 (x + c * t) + Deriv_n u0 2 (x - c * t)).

Lemma alpha_20_lim :
  forall x t, is_deriv_n (fun u => alpha u t) 2 x (alpha20 x t).
Proof.
intros x t.
unfold is_deriv_n, is_deriv, Deriv_n, alpha.
apply (is_deriv_eq (fun x => 1/2 * (Deriv (fun x => u0 x) (x + c * t) + Deriv (fun x => u0 x) (x - c * t)))).
intros u.
apply sym_eq, Deriv_correct.
unfold is_deriv.
auto_derive.
repeat split ; apply Du0.
unfold Rminus.
ring.
unfold is_deriv.
auto_derive.
repeat split ; apply D2u0.
unfold alpha20, Deriv_n, Rminus.
ring.
Qed.

Lemma alpha_02_lim :
  forall x t, is_deriv_n (fun u => alpha x u) 2 t (alpha02 x t).
Proof.
intros x t.
unfold is_deriv_n, is_deriv, Deriv_n, alpha.
apply (is_deriv_eq (fun t => 1/2 * c * (Deriv (fun x => u0 x) (x + c * t) - Deriv (fun x => u0 x) (x - c * t)))).
intros u.
apply sym_eq, Deriv_correct.
unfold is_deriv.
auto_derive.
repeat split ; apply Du0.
unfold Rminus.
ring.
unfold is_deriv.
auto_derive.
repeat split ; apply D2u0.
unfold alpha02, Deriv_n, Rminus, Rdiv.
ring.
Qed.

End Alpha.

Parameter u1 : R -> R.

Hypothesis Cu1 : forall x, continuity_pt (fun u => u1 u) x.
Hypothesis Iu1 : forall a b, ex_RInt (fun u => u1 u) a b.
Hypothesis Du1 : forall x, ex_deriv (fun u => u1 u) x.

Section Beta.

Definition beta (x t : R) := 1/(2*c) * RInt (fun u => u1 u) (x - c * t) (x + c * t).
Definition beta20 x t := 1/(2*c) * (Deriv (fun u => u1 u) (x + c * t) - Deriv (fun u => u1 u) (x - c * t)).
Definition beta02 x t := c/2 * (Deriv (fun u => u1 u) (x + c * t) - Deriv (fun u => u1 u) (x - c * t)).

Lemma beta20_lim :
  forall x t, is_deriv_n (fun u => beta u t) 2 x (beta20 x t).
Proof.
intros x t.
unfold is_deriv_n, is_deriv, Deriv_n, beta.
apply (is_deriv_eq (fun x => 1/(2*c) * (u1 (x + c * t) - u1 (x - c * t)))).
intros u.
apply sym_eq, Deriv_correct.
unfold is_deriv.
auto_derive.
split.
apply Iu1.
repeat split.
apply Locally.locally_forall.
apply Cu1.
apply Locally.locally_forall.
apply Cu1.
unfold Rminus.
ring.
unfold is_deriv.
auto_derive.
repeat split ; apply Du1.
unfold beta20, Rminus.
ring.
Qed.

Lemma beta02_lim :
  forall x t, is_deriv_n (fun u => beta x u) 2 t (beta02 x t).
Proof.
intros x t.
unfold is_deriv_n, is_deriv, Deriv_n, beta.
apply (is_deriv_eq (fun t => 1/2 * (u1 (x + c*t) + u1 (x - c*t)))).
intros u.
apply sym_eq, Deriv_correct.
unfold is_deriv.
auto_derive.
split.
apply Iu1.
repeat split.
apply Locally.locally_forall.
apply Cu1.
apply Locally.locally_forall.
apply Cu1.
unfold Rminus.
now field.
unfold is_deriv.
auto_derive.
repeat split ; apply Du1.
unfold beta02, Rminus, Rdiv.
ring.
Qed.

End Beta.

Hypothesis f : R -> R -> R.

Section Gamma.

Definition gamma x t := 1/(2*c) * RInt (fun tau => RInt (fun xi => f xi tau) (x - c * (t - tau)) (x + c * (t - tau))) 0 t.
Definition gamma20 x t := 1/(2*c) * RInt (fun tau => Deriv (fun u => f u tau) (x + c * (t - tau)) - Deriv (fun u => f u tau) (x - c * (t - tau))) 0 t.

Lemma gamma20_lim :
  forall x t, is_deriv_n (fun u => gamma u t) 2 x (gamma20 x t).
Proof.
intros x t.
unfold is_deriv_n, is_deriv, Deriv_n, gamma.
Admitted.

End Gamma.

End DAlembert.
