(**
This library provides vernacular files containing a formalization of real
analysis for Coq. It is a conservative extension of the standard library Reals
with a focus on usability. It has been developed by Sylvie Boldo, Catherine
Lelay, and Guillaume Melquiond.

The goal of Coquelicot is to ease the writing of formulas and theorem statements
for real analysis. This is achieved by using total functions in place of
dependent types for limits, derivatives, integrals, power series, and so on.
To help with the proof process, the library comes with a comprehensive set
of theorems that cover not only these notions, but also some extensions such
as parametric integrals, two-dimensional differentiability, asymptotic
behaviors. It also offers some automations for performing differentiability
proofs. Since Coquelicot is a conservative extension of Coq's standard
library, we provide correspondence theorems between the two libraries.


* Main types


- [R]: the set of real numbers defined by Coq's standard library.
- [Rbar]: [R] extended with signed infinities [p_infty] and [m_infty].
- [C]: the set of complex numbers, defined as pairs of real numbers.
- [@matrix T m n]: matrices with m rows and n columns of coefficients of type T.


* Main classes


- [UniformSpace]: a uninform space with a predicate [ball] defining an ecart.
- [CompleteSpace]: a [UniformSpace] that is also complete.
- [AbelianGroup]: a type with a commutative operator [plus] and a neutral
  element [zero]; elements are invertible ([opp], [minus]).
- [Ring]: an [AbelianGroup] with a commutative operator [mult] that is
  distributive with respect to [plus]; [one] is the neutral element of [mult].
- [AbsRing]: a [Ring] with an operator [abs] that is subdistributive
- with respect to [plus] and [mult].
- [ModuleSpace]: an [AbelianGroup] with an operator [scal] that defines a
  left-module over a [Ring].
- [NormedModule]: a [ModuleSpace] that is also a [UniformSpace]; it provides an
  operator [norm] that defines the same topology as [ball].
- [CompleteNormedModule]: a [NormedModule] that is also a [CompleteSpace].


In the following definitions, K will designate either a [Ring] or an [AbsRing],
while U and V will designate either some [ModuleSpace], [NormedModule], or
[CompleteNormedModule].


* Low-level concepts of topology


Limits and neighborhoods are expressed thanks to filters, that is, predicates
of type [(T -> Prop) -> Prop]. Generic properties about filters are prefixed
with [filter_], e.g. [filter_and] and [filter_imp].


In a [UniformSpace], [ball x eps y] states that y lies in a ball of center x and
radius eps. [locally x] is the filter containing all the balls of center x.
The supported filters are as follows:
- [locally x].
- [locally' x] is similar to [locally x], except that x is missing from every
  set, and thus properties of point x do not matter.
- [Rbar_locally x] is defined for x in [Rbar]. It is [locally x] if x is finite,
  otherwise it is the set of half-bounded open intervals extending to either
  [m_infty] or [p_infty], depending on which infinity x is.
- [Rbar_locally' x] is to [Rbar_locally x] what [locally' x] is to [locally x].
- [at_left x] restricts the open ball of [locally x] to points strictly less
  than x, thus properties of points on the right of x do not matter.
- [at_right x] is symmetric to [at_left x].
- [filter_prod G H] is a filter describing the neighborhoods of point (g,h) if
  G describes the neighborhoods of g while H describes the neighborhoods of h.
- [eventually] is a filter on natural numbers that converges to plus infinity.
- [within dom F] weakens a filter F by only considering points that satisfy dom.


Examples:
- [locally 2 (fun x => 0 < ln x)] means that [ln] has positive values in
  a neighborhood of 2.
- [at_left 1 (fun x => -1 < ln x < 0)] means that [ln] has values between -1
  and 0 in the left part of a neighborhood of 1.


Open sets are described by the predicate [open]. It states that a set is open
if it is a neighborhood of any of its points (in terms of [locally]).


* Limits and continuity


Limits and continuity are expressed by filters using the generic construction
[filterlim f K L] with f a function, K a filter describing a limit point of the
domain of f, and L a filter describing a limit point of the range of f.


Examples:
- [filterlim f (locally x) (locally (f x))] means that the preimage of any
  neighborhood of f x is a neighborhood of x. Said otherwise, f is continuous
  at point x.
- [filterlim f (at_right x) (locally y)] means that f t tends to y when t tends
  to x from the right.
- [filterlim exp (Rbar_locally m_infty) (at_right 0)] means that [exp] tends
  to 0 at minus infinity but only takes positive values there.
- [forall x y : R, filterlim (fun z => fst z + snd z) (filter_prod (locally x)
  (locally y)) (locally (x + y))] states that [Rplus] is continuous.


Lemma [filterlim_locally] gives the traditional epsilon-delta definition of
continuity. Compatibility with the [continuity_pt] predicate from the standard
library is provided by lemmas such as [continuity_pt_filterlim].


The following predicates specialize [filterlim] to the usual cases of
real-valued sequences and functions:
- [is_lim_seq : (nat -> R) -> Rbar -> Prop], e.g. [is_lim_seq (fun n => 1 + /
  INR n) 1].
- [is_lim : (R -> R) -> Rbar -> Rbar -> Prop], e.g. [is_lim exp p_infty
  p_infty].


The unicity of the limits is given by lemmas [is_lim_seq_unique] and
[is_lim_unique]. The compatibility with the arithmetic operators is given
by lemmas such as [is_lim_seq_plus] and [is_lim_seq_plus']. They are
derived from the generic lemmas [filterlim_plus] and [filterlim_compose].


Lemmas [is_lim_seq_spec] and [is_lim_sprec] gives the traditional epsilon-delta
definition of convergence. Compatibility with the [Un_cv] and [limit1_in]
predicates from the standard library is provided by lemmas [is_lim_seq_Reals]
and [is_lim_Reals].


When only the convergence matters but not the actual value of the limit, the
following predicates can be used instead, depending on whether the value can
be infinite or not:
- [ex_lim_seq : (nat -> R) -> Prop].
- [ex_lim : (R -> R) -> Rbar -> Prop].
- [ex_finite_lim_seq : (nat -> R) -> Prop].
- [ex_finite_lim : (R -> R) -> Rbar -> Prop].


Finally, there are also some total functions that are guaranteed to return the
proper limits if the sequences or functions actually converge:
- [Lim_seq : (nat -> R) -> Rbar], e.g. [Lim_seq (fun n => 1 + / INR n)] is equal
  to 1.
- [Lim : (R -> R) -> Rbar -> Rbar].


If they do not converge, the returned value is arbitrary and no interesting
results can be derived. These functions are related to the previous predicates
by lemmas [Lim_seq_correct] and [Lim_correct].


As with predicates [filterlim], [is_lim_seq], and [is_lim], compatibility with
the arithmetic operators is given by lemmas such as [ex_lim_seq_mult] and
[Lim_inv].


* Functions and predicates

Total functions:
- [Derive : (R -> R) -> R -> R]
- [RInt : (R -> R) -> R -> R -> R]
- [Series : (nat -> R) -> R]
- [PSeries : (nat -> R) -> R -> R]
- [CV_radius : (nat -> R) -> Rbar]


The corresponding predicates are:
- [is_derive : (R -> R) -> R -> R -> Prop]
- and so on, except for [CV_radius].


There are also predicates in case the actual value does not matter:
- [ex_derive : (R -> R) -> R -> Prop]
- and so on.


** Example

[Derive f x] is a real number. If function f is derivable at point x, then
this number is equal to the derivative of f at point x. Otherwise it is an
arbitrary real number. The differentiability of f at x is given by the
predicate [ex_derive f x]. Predicate [is_derive f x l] encompasses both
properties: it is equivalent to [ex_derive f x /\ Derive f x = l].

Theorems [is_derive_unique] and [Derive_correct] provide relations between
these predicates. Theorems [ex_derive_Reals_0], [ex_derive_Reals_1], and
[Derive_Reals], relate these definitions to those of Coq's standard library.


* Naming conventions


- Correspondence theorems with the standard library contain [_Reals] in their name.
- Extensionality theorems contain [_ext] in their name.
  If the equality only needs to be local, they also contain [_loc].
- Uniqueness theorems contain [_unique] in their name.
- Theorems about asymptotic behaviors are suffixed by [_p] or [_m]
  if they are at infinite points.
*)

Require Export AutoDerive Compactness Complex Continuity Derive.
Require Export Derive_2d Equiv ElemFct Hierarchy Limit.
Require Export Lub Markov PSeries Rbar Rcomplements.
Require Export RInt Seq_fct Series SF_seq.

(** #<img src="deps.png" usemap="##coquelicot_deps" /># *)

(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2013 Sylvie Boldo
#<br />#
Copyright (C) 2011-2013 Catherine Lelay
#<br />#
Copyright (C) 2011-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)
