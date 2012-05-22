Require Import Reals.
Require Import ssreflect seq.
Require Import Arithmetique Locally Deriv_fct.

Fixpoint Rn n :=
  match n with
  | O => R
  | S n => R -> Rn n
  end.

Inductive bop :=
  | Eplus
  | Emult.

Inductive uop :=
  | Eopp.

Inductive expr :=
  | Var : nat -> expr
  (*| AppExt : forall k, Rn k -> seq expr -> expr*)
  | App : expr -> expr -> expr
  | Subst : expr -> expr -> expr
  | Cst : R -> expr
  | Binary : bop -> expr -> expr -> expr
  | Unary : uop -> expr -> expr
  | Int : expr -> expr -> expr -> expr.

Fixpoint apply p : Rn p -> seq R -> R :=
  match p return Rn p -> seq R -> R with
  | O => fun (x : R) l => x
  | S p => fun (f : Rn (S p)) l => match l with h::q => apply p (f h) q | nil => apply p (f R0) l end
  end.

Axiom RInt : (R -> R) -> R -> R -> R.

Fixpoint interp (l : seq R) (e : expr) : R :=
  match e with
  | Var n => nth R0 l n
  (*| AppExt k f le => apply k f (map (interp l) le)*)
  | App e1 e2 => interp ((interp l e2) :: l) e1
  | Subst e1 e2 => interp (set_nth R0 l 0 (interp l e2)) e1
  | Cst c => c
  | Binary o e1 e2 => match o with Eplus => Rplus | Emult => Rmult end (interp l e1) (interp l e2)
  | Unary o e => match o with Eopp => Ropp end (interp l e)
  | Int e1 e2 e3 => RInt (fun x => interp (x :: l) e1) (interp l e2) (interp l e3)
  end.

Inductive domain :=
  | Never : domain
  | Always : domain
  | Derivable : expr -> nat -> domain
  | And : seq domain -> domain
  | Forall : expr -> expr -> domain -> domain.

Fixpoint interp_domain (l : seq R) (d : domain) : Prop :=
  match d with
  | Never => False
  | Always => True
  | Derivable e n => ex_deriv (fun x => interp (set_nth R0 l n x) e) (nth R0 l n)
  | And ld => foldl (fun acc d => acc /\ interp_domain l d) True ld
  | Forall e1 e2 s =>
    let a1 := interp l e1 in let a2 := interp l e2 in
    exists eps : posreal, forall t, -eps < t < 1 + eps ->
    interp_domain (a1 + t * (a2 - a1) :: l) s
  end.

Fixpoint is_const (e : expr) n : bool :=
  match e with
  | Var v => negb (ssrnat.eqn v n)
  | Cst _ => true
  | App f e => andb (is_const f (S n)) (is_const e n)
  | Subst f e => andb (orb (ssrnat.eqn n 0) (is_const f n)) (is_const e n)
  | Binary b e1 e2 => andb (is_const e1 n) (is_const e2 n)
  | Unary u e => is_const e n
  | Int f e1 e2 => andb (is_const f (S n)) (andb (is_const e1 n) (is_const e2 n))
  end.

Lemma is_const_correct :
  forall e n, is_const e n ->
  forall l x1 x2,
  interp (set_nth 0 l n x1) e = interp (set_nth 0 l n x2) e.
Proof.
induction e.
(* *)
simpl => k Hk l x1 x2.
rewrite 2!nth_set_nth /=.
now rewrite -ssrnat.eqnE (ssrbool.negbTE Hk).
(* *)
simpl => n.
move /ssrbool.andP => [H1 H2] l x1 x2.
rewrite (IHe2 n H2 l x1 x2).
now apply: (IHe1 (S n) _ (interp (set_nth 0 l n x2) e2 :: l)).
(* *)
intros n.
simpl is_const.
move /ssrbool.andP => [H1 H2] l x1 x2.
change (interp (set_nth 0 (set_nth 0 l n x1) 0 (interp (set_nth 0 l n x1) e2)) e1 =
  interp (set_nth 0 (set_nth 0 l n x2) 0 (interp (set_nth 0 l n x2) e2)) e1).
move: H1.
replace (orb (ssrnat.eqn n 0) (is_const e1 n)) with
  (orb (ssrnat.eqn n 0) (andb (negb (ssrnat.eqn n 0)) (is_const e1 n))).
move /ssrbool.orP => [H1|].
rewrite 2!set_set_nth.
rewrite -ssrnat.eqnE H1.
now rewrite (IHe2 n H2 l x1 x2).
move /ssrbool.andP => [H1 H3].
rewrite 2!set_set_nth.
rewrite -ssrnat.eqnE (ssrbool.negbTE H1).
rewrite (IHe2 n H2 l x1 x2).
now apply IHe1.
now case (ssrnat.eqn n 0).
(* *)
easy.
(* *)
simpl => n.
move /ssrbool.andP => [H1 H2] l x1 x2.
now rewrite (IHe1 n H1 l x1 x2) (IHe2 n H2 l x1 x2).
(* *)
simpl => n H l x1 x2.
now rewrite (IHe n H l x1 x2).
(* *)
simpl => n.
move /ssrbool.andP => [H1].
move /ssrbool.andP => [H2 H3] l x1 x2.
rewrite (IHe2 n H2 l x1 x2) (IHe3 n H3 l x1 x2).
admit. (* RInt_eq *)
Qed.

Fixpoint D (e : expr) n : expr * domain :=
  match e with
  | Var v => (if ssrnat.eqn v n then Cst 1 else Cst 0, Always)
  | Cst _ => (Cst 0, Always)
  | App f e => (Cst 0, Never)
  | Subst f e => (Cst 0, Never)
  | Binary b e1 e2 =>
    let '(a1,b1) := D e1 n in
    let '(a2,b2) := D e2 n in
    (match b with
    | Eplus => Binary Eplus a1 a2
    | Emult => Binary Eplus (Binary Emult a1 e2) (Binary Emult e1 a2)
    end, And (b1::b2::nil))
  | Unary u e =>
    let '(a,b) := D e n in
    match u with
    | Eopp => (Unary Eopp a, b)
    end
  | Int f e1 e2 =>
    let '(a1,b1) := D e1 n in
    let '(a2,b2) := D e2 n in
    let '(a3,b3) := D f (S n) in
    (Binary Eplus
      (Binary Eplus
        (Binary Emult a2 (App f e2))
        (Unary Eopp (Binary Emult a1 (App f e1))))
      (Int a3 e1 e2), And (b1::b2::(Forall e1 e2 b3)::nil))
  end.

Lemma is_deriv_eq :
  forall f g x l,
  (forall t, f t = g t) ->
  is_deriv f x l -> is_deriv g x l.
Proof.
intros f g x l Heq Hf eps Heps.
move: (Hf eps Heps) => {Hf} [delta Hf].
exists delta => h Zh Hh.
rewrite -2!Heq.
now apply Hf.
Qed.

Lemma interp_subst :
  forall n l e,
  interp (set_nth 0 l n (nth 0 l n)) e = interp l e.
Proof.
intros n l e.
revert n l.
induction e.
(* *)
simpl => k l.
rewrite nth_set_nth /= /eqtype.eq_op /=.
case ssrnat.eqnP.
move => -> //.
easy.
(* *)
simpl => n l.
rewrite IHe2.
change (interp l e2 :: set_nth 0 l n (nth 0 l n)) with
  (set_nth 0 (interp l e2 :: l) (S n) (nth 0 (interp l e2 :: l) (S n))).
apply IHe1.
(* *)
intros n l.
rewrite /interp -/interp.
rewrite IHe2.
rewrite set_set_nth.
case ssrnat.eqnP => H.
easy.
replace (nth 0 l n) with (nth 0 (set_nth 0 l 0 (interp l e2)) n).
apply IHe1.
rewrite nth_set_nth /=.
case ssrnat.eqnP => H'.
now contradict H.
easy.
(* *)
easy.
(* *)
simpl => n l.
now rewrite IHe1 IHe2.
(* *)
simpl => n l.
now rewrite IHe.
(* *)
simpl => n l.
rewrite IHe2 IHe3.
admit. (* RInt_eq *)
Qed.

Lemma D_correct : forall (e : expr) l n,
  let '(a,b) := D e n in
  interp_domain l b ->
  is_deriv (fun x => interp (set_nth R0 l n x) e) (nth R0 l n) (interp l a).
Proof.
induction e.
(* *)
simpl => l k _.
apply is_deriv_eq with (fun x => if ssrnat.eqn n k then x else nth 0 l n).
intros t.
now rewrite nth_set_nth.
case ssrnat.eqnP => [H|H].
apply derivable_pt_lim_id.
apply derivable_pt_lim_const.
(* *)
simpl => l n [].
(* *)
simpl => l n [].
(* *)
simpl => l n _.
apply derivable_pt_lim_const.
(* *)
simpl => l n.
specialize (IHe1 l n).
specialize (IHe2 l n).
destruct (D e1 n) as (a1,b1).
destruct (D e2 n) as (a2,b2).
simpl.
intros ((_,H1),H2).
specialize (IHe1 H1).
specialize (IHe2 H2).
case b.
simpl.
now apply derivable_pt_lim_plus.
simpl.
rewrite -(interp_subst n _ e1) -(interp_subst n _ e2).
apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).
exact IHe1.
exact IHe2.
(* *)
simpl => l n.
specialize (IHe l n).
destruct (D e n) as (a,b).
case u.
simpl.
intros H.
apply derivable_pt_lim_opp.
now apply IHe.
(* *)
simpl => l n.
specialize (IHe2 l n).
specialize (IHe3 l n).
move: (fun l => IHe1 l (S n)) => {IHe1} IHe1.
destruct (D e1 (S n)) as (a1,b1).
destruct (D e2 n) as (a2,b2).
destruct (D e3 n) as (a3,b3).
simpl.
intros (((_,H2),H3),(eps,H1)).
specialize (IHe2 H2).
specialize (IHe3 H3).
admit.
Qed.
