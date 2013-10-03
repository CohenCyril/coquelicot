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


* Functions and predicates

Total functions:
- [Lim_seq : (nat -> R) -> Rbar]
- [Lim : (R -> R) -> Rbar -> Rbar]
- [Derive : (R -> R) -> R -> R]
- [RInt : (R -> R) -> R -> R -> R]
- [Series : (nat -> R) -> R]
- [PSeries : (nat -> R) -> R -> R]
- [CV_radius : (nat -> R) -> Rbar]


The corresponding predicates are:
- [is_lim_seq : (nat -> R) -> Rbar -> Prop]
- [is_lim : (R -> R) -> Rbar -> Rbar -> Prop]
- [is_derive : (R -> R) -> R -> R -> Prop]
- and so on, except for [CV_radius].


There are also predicates in case the actual value does not matter:
- [ex_lim_seq : (nat -> R) -> Prop]
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

* Limits and filters

Limits and continuity are expressed by filters using the generic construction
[filterlim f K L] with f a function, K a filter describing a limit point of the
domain of f, and L a filter describing a limit point of the range of f.

The following filters are available:
- [locally x] is the set of all the open balls centered on x, with x an element
  from a [MetricSpace].
- [locally' x] is similar to [locally x], except that x is missing from every ball.
- [Rbar_locally x] is defined for x in [Rbar]. It is [locally x] if x is finite,
  otherwise it is the set of half-bounded open intervals extending to either
  [m_infty] or [p_infty], depending on which infinity x is.
- [Rbar_locally' x] is to [Rbar_locally x] what [locally' x] is to [locally x].
- [at_left x] restricts the open ball of [locally x] to points strictly less than x.
- [at_right x] is symmetric to [at_left x].
- [filter_prod G H] is a filter describing the neighborhoods of point [(g,h)] if
  G describes the neighborhoods of g while H describes the neighborhoods of h.


Theorems such as [is_lim_seq_spec], [is_lim_spec], [filterlim_locally] give
a more traditional epsilon-delta representation of limits.

** Examples

- [is_lim f x l] means [filterlim f (Rbar_locally' x) (Rbar_locally x)].
- [continuity_pt f x], [filterlim f (locally x) (locally (f x))],
  and [filterlim f (locally' x) (locally (f x))], are equivalent properties.
- Addition is a continuous function:
  [forall x y : R, filterlim (fun z => fst z + snd z) (filter_prod (locally x) (locally y)) (locally (x + y))].
- [ln] has a limit at 0+: [filterlim ln (at_right 0) (Rbar_locally m_infty)].


* Naming conventions

- Correspondence theorems with the standard library contain [_Reals] in their name.
- Extensionality theorems contain [_ext] in their name.
  If the equality only needs to be local, they also contain [_loc].
- Uniqueness theorems contain [_unique] in their name.
- Theorems about asymptotic behaviors are suffixed by [_p] or [_m]
  if they are at infinite points.
*)

Require Export AutoDerive Compactness Continuity Derive.
Require Export Derive_2d Equiv ElemFct Hierarchy Limit.
Require Export Locally Lub Markov PSeries Rbar Rcomplements.
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
