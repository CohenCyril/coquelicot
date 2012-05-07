Require Import Reals.

Require Import Function1 Function2.

Open Local Scope R_scope.

(** * Paramètres *)
Parameters (c : R) (u0 u1 : R -> R) (f : R -> R -> R).
Hypothesis Hc : c <> 0.

(** * Mise en équation *)
Definition Cond1 (u : R -> R -> R) l20 l02
  (D20 : forall x t, derivable20_pt_lim u x t (l20 x t))
  (D02 : forall x t, derivable02_pt_lim u x t (l02 x t)) :=
  forall x t : R, l02 x t - c^2 * l20 x t = f x t.
Definition Cond2 (u : R -> R -> R) :=
  forall x : R, u x 0 = u0 x.
Definition Cond3 (u : R -> R -> R) l01 
  (D01 : forall x t, derivable01_pt_lim u x t (l01 x t)) :=
  forall x : R, l01 x 0 = u1 x.

Definition Prob (u : R -> R -> R) l20 l02 l01 D20 D02 D01 :=
  (Cond1 u l20 l02 D20 D02) /\ (Cond2 u) /\ (Cond3 u l01 D01).