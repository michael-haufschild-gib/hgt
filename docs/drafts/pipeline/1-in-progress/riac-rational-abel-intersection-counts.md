# Rational Abel energy from actual arithmetic intersections

- **ID:** RIAC-rational-Abel-counts
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Statement:** Realize rational-radius torsion energy by finite integral intersection rings and derive the self-energy factor arithmetically.

## Independent counting object

For positive conductors `m,n` and integers `0≤a<b`, take the monic
polynomials `P=scaleRoots(Φ_m,a)` and `Q=scaleRoots(Φ_n,b)`.
Their roots lie on circles of radii `a,b`, so they have no common root.
Define `C_{m,n}(a,b)=# ℤ[X]/(P,Q)` from this actual finite intersection.
The complex resultant should give the exact comparison

`log C_{m,n}(a,b)=φ(m)φ(n)log b−T_{a/b}(m,n)`.

Thus the original Abel energy is recovered from an independently defined
integer count. Equal thickening has the quadratic local multiplicity law
of the actual two-divisor quotient. Simultaneous integral dilation should
multiply the cardinality by `k^(φ(m)φ(n))`.

## Critical self-interaction

For `P_a=scaleRoots(Φ_n,a)`, construct the integral divided-difference
polynomial `D_{a,b}` coefficientwise, with
`P_b−P_a=(b−a)D_{a,b}`. Its definition extends to `a=b` by the polynomial
power-difference sum. The renormalized object is the actual ring
`ℤ[X]/(P_a,D_{a,b})`, defined before its cardinality.

Prove `C(P_a,P_b)=|b−a|^φ(n) C(P_a,D_{a,b})`. Multiplication by
`b−a` should realize this through the exact sequence of actual quotients
`0→O/(D)→O/((b−a)D)→O/(b−a)→0`, where `O=ℤ[X]/(P_a)` is
free over `ℤ`. This removes the coincident-root factor arithmetically.

At `a=b=1`, the divided difference is `dΦ_n−XΦ_n'`, `d=φ(n)`.
Identify the resulting finite quotient count with the absolute discriminant.
Common radial dilation has remaining degree `d(d−1)`, explaining the two
normalizations in the analytic self-energy law. Prove the diagonal limit
and retain the finite-radius error and its sign. No counterterm chosen
from the desired quadratic form is allowed.

## Governing cancellation test

The target remains `Σ_p index_p(N)=1−M(N)` at square-root scale.
Individual residue counts do not control signed combinations. This branch
must identify exactly what integrality and divisibility survive after
self-interaction is removed, and whether they constrain the signed source.
It must not infer positivity of a renormalized limit from positive raw
cardinalities. No critical sign or Mertens bound is assumed.

## Existing foundations and status

The generic proper-intersection count is developed in
[thickened intersections](../3-formalized/riac-thickened-intersection-counts.md).
HHAC `FiniteRadiusTorsionEnergy.lean` proves the analytic self-energy
separation and radial error law. AET constructs the literal Abel energy and
its Fourier Gram formula. The missing contribution here is the actual
integral quotient and its arithmetic self-factor comparison.

No Lean theorem for these rational-radius counts is claimed yet.

## Literature boundary

Radial resultants and discriminant deformations are classical. Apostol's
[scaled cyclotomic resultant paper](https://doi.org/10.1090/S0025-5718-1975-0366801-7)
treats dilated cyclotomic equations;
[Tran, §1](https://arxiv.org/html/1601.04382v1) states the root-pair
`q`-discriminant and its diagonal specialization, crediting Ismail.
The contribution sought here is an actual integral residual quotient, its
local-global count, and the exact bridge to the existing torsion energy.
No classical resultant identity is claimed as new.
