# Simultaneous logarithm bounds with rank in the exponent

- **ID:** CDG-SIM
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Goal:** A proved collective small-form estimate beyond maximal-minor
  reduction to a scalar Baker bound.

## External benchmark

For distinct primes `p_j≤y`, an integer `r×k` matrix of rank `r`, and
`|a_ij|≤H`, put `L_i=Σ_j a_ij log p_j`, where `H≥1`, `1≤r≤k`.
Theorem 1.1 of [Gaudron (2014), pp. 2–3](https://lmbp.uca.fr/~gaudron/art12.pdf)
specializes to

`max_i |L_i| ≥ exp(−G)`,

`G=(10k)^(58k²/r) A^(1/r) (max(1,log H)+A) (1+e log y)^(k/r)`,

`A=floor(log(e+1+ek log y))+1`.

Here the number field is `ℚ`, the theorem's exponential parameter is `e`,
`log a=e log y`, and `log b=max(1,log H)`.
Unique factorization supplies independence of the prime logarithms.
This is an external theorem, not a new result or a Lean dependency.
The 2012 arXiv text has different constants; the formula above uses the
published version.

## Why this comparison matters

At proportional rank `r≈k/2`, the published dimension factor is
`exp(O(k log k))`. The current Cramer reduction uses a scalar Baker
exponent in about `k/2` logarithms, with dimension dependence
`exp(O(k² log(k log y)))`. Thus scalar slicing does not exhaust the
available collective arithmetic. Near full rank the existing elementary
determinant bound, or the two-logarithm reduction, can instead be stronger.
Any replacement must retain these regimes.

## Proof gap

The corpus's Fel'dman argument handles one form. Replacing its pivot by
several pivots does not prove a simultaneous estimate: the auxiliary-section
dimension, multiplicity estimate, and small-values construction must all
retain the rank gain. Gaudron's proof supplies these through approximate
Siegel theory and multiplicity estimates on an additive group times a torus.
No version of that input is assumed here.

## Rational-coefficient construction to test

Choose a largest absolute `r×r` column minor `B`, put `D=det B`, and
write the remaining columns as `C`. For an exponent vector `(u,v)` in
`[0,q)^r×[0,q)^(k−r)`, use the integral free coordinates

`γ(u,v)=D v−u adj(B) C`.

The perturbed frequency is `Σ_j (γ_j/D) log p_j`, over free coordinates.
Its difference from the true frequency is `u B⁻¹ L`.
Maximality of the minor bounds each entry of `B⁻¹C` by one; the error
still pays the explicit adjugate bound against `max_i|L_i|`.

Fel'dman's polynomial jets can then use `k−r` free directions and one
polynomial direction. The proposed Siegel system has
`X₀ S^(k−r+1)` equations and `(N+1)q^k` unknowns. Its entries are integers,
so the existing integer Siegel lemma applies directly; an approximate
Siegel lemma is not automatically necessary in this rational specialization.
The corpus's `Matveev/FeldmanSiegelSystem.lean` and
`Matveev/FeldmanAuxiliaryBounds.lean` give the one-pivot construction.

The unresolved step is a parameter choice retaining this rank gain through
analytic extrapolation, denominator clearing, and final coefficient
vanishing. A count of unknowns alone is not a proof of a simultaneous bound.
Only a dependency-closed argument can advance to stage 2 and formalization.

## Scope

This addresses collective small forms and the rank profile. Even the
published bound does not by itself prove early-return exclusion: a form
acts on a return through its total coefficient height times phase error.
The constant-precision breadth mechanism remains a separate open problem.
