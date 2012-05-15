Require Import Reals.
Require Import Lim_fct.
Open Scope R_scope.

(** * Deriv *)

Definition Deriv (f : R -> R) (x : R) := Lim (fun h => (f (x+h) - f x)/h) 0.

Definition is_deriv f x l := derivable_pt_lim f x l.
Definition ex_deriv f x := exists l, is_deriv f x l.

(** ** Compute Deriv *)

Lemma Deriv_correct f x l :
  is_deriv f x l -> Deriv f x = l.
Proof.
  intros.
  apply (uniqueness_step1 f x).
  apply is_lim_Coq_0.
  apply Lim_prop.
  exists l.
  apply is_lim_Coq_1.
  
  apply uniqueness_step2, H.
  apply uniqueness_step2, H.
Qed.
Lemma Deriv_prop f x :
  ex_deriv f x -> is_deriv f x (Deriv f x).
Proof.
    intros (l,H).
  cut (Deriv f x = l).
    intros ; rewrite H0 ; apply H.
  apply Deriv_correct, H.
Qed.

(** * Operations *)

Lemma is_deriv_opp :
  forall f x, ex_deriv f x ->
  is_deriv (fun x => - f x) x (- Deriv f x).
Proof.
intros f x Df.
apply derivable_pt_lim_opp.
now apply Deriv_prop.
Qed.

Lemma ex_deriv_opp :
  forall f x, ex_deriv f x ->
  ex_deriv (fun x => - f x) x.
Proof.
intros f x Df.
eexists.
now apply is_deriv_opp.
Qed.

Lemma Deriv_opp :
  forall f x, ex_deriv f x ->
  Deriv (fun x => - f x) x = - Deriv f x.
Proof.
intros f x Df.
apply Deriv_correct.
now apply is_deriv_opp.
Qed.

Lemma is_deriv_plus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  is_deriv (fun x => f x + g x) x (Deriv f x + Deriv g x).
Proof.
intros f g x Df Dg.
apply derivable_pt_lim_plus ; now apply Deriv_prop.
Qed.

Lemma ex_deriv_plus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  ex_deriv (fun x => f x + g x) x.
Proof.
intros f g x Df Dg.
eexists.
now apply is_deriv_plus.
Qed.

Lemma Deriv_plus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  Deriv (fun x => f x + g x) x = Deriv f x + Deriv g x.
Proof.
intros f g x Df Dg.
apply Deriv_correct.
now apply is_deriv_plus.
Qed.

Lemma is_deriv_minus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  is_deriv (fun x => f x - g x) x (Deriv f x - Deriv g x).
Proof.
intros f g x Df Dg.
apply derivable_pt_lim_minus ; now apply Deriv_prop.
Qed.

Lemma ex_deriv_minus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  ex_deriv (fun x => f x - g x) x.
Proof.
intros f g x Df Dg.
eexists.
now apply is_deriv_minus.
Qed.

Lemma Deriv_minus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  Deriv (fun x => f x - g x) x = Deriv f x - Deriv g x.
Proof.
intros f g x Df Dg.
apply Deriv_correct.
now apply is_deriv_minus.
Qed.

Lemma is_deriv_comp (f g : R -> R) (x df dg : R) : 
  is_deriv f (g x) df -> is_deriv g x dg -> is_deriv (fun x => f (g x)) x (df * dg).
Proof.
  intros Hf Hg.
  apply derivable_pt_lim_comp ; auto.
Qed.
Lemma ex_lim_comp (f g : R -> R) (x : R) : 
  ex_deriv f (g x) -> ex_deriv g x -> ex_deriv (fun x => f (g x)) x.
Proof.
  intros.
  exists (Deriv f (g x) * Deriv g x) ; apply is_deriv_comp.
  apply Deriv_prop, H.
  apply Deriv_prop, H0.
Qed.
Lemma Deriv_comp (f g : R -> R) (x : R) :
  ex_deriv f (g x) -> ex_deriv g x -> Deriv (fun x => f (g x)) x = Deriv f (g x) * Deriv g x.
Proof.
  intros.
  apply Deriv_correct.
  apply is_deriv_comp.
  apply Deriv_prop, H.
  apply Deriv_prop, H0.
Qed.

Lemma is_deriv_CL (f g : R -> R) (a x lf lg : R) :
  is_deriv f x lf -> is_deriv g x lg -> is_deriv (fun x => f x + a * g x) x (lf + a * lg).
Proof.
  intros Hf Hg.
  apply derivable_pt_lim_plus.
  apply Hf.
  apply derivable_pt_lim_scal, Hg.
Qed.
Lemma ex_deriv_CL (f g : R -> R) (a x : R) :
  ex_deriv f x -> ex_deriv g x -> ex_deriv (fun x => f x + a * g x) x.
Proof.
  intros (lf,Hf) (lg,Hg).
  exists (lf + a * lg) ; apply is_deriv_CL ; [apply Hf | apply Hg].
Qed.
Lemma Deriv_CL (f g : R -> R) (a x : R) :
  ex_deriv f x -> ex_deriv g x -> Deriv (fun x => f x + a * g x) x = Deriv f x + a * Deriv g x.
Proof.
  intros.
  apply Deriv_correct.
  apply is_deriv_CL ; apply Deriv_prop.
  apply H.
  apply H0.
Qed.

(** * nth deriv *)
Fixpoint Deriv_n (f : R -> R) (n : nat) x :=
  match n with
    | O => f x
    | S n => Deriv (Deriv_n f n) x
  end.

Definition ex_deriv_n f n x :=
  match n with
  | O => True
  | S n => ex_deriv (Deriv_n f n) x
  end.

Definition is_deriv_n f n x l :=
  match n with
  | O => f x = l
  | S n => is_deriv (Deriv_n f n) x l
  end.

Lemma Deriv_n_correct f n x l :
  is_deriv_n f n x l -> Deriv_n f n x = l.
Proof.
  case n.
  easy.
  simpl; intros n0 H.
  apply Deriv_correct, H.
Qed.
