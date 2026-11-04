# Fifth cross-load from scale seven

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** The fixed endpoint-compatible cross-load is positive definite for every `q=π exp(2x)≥7`.

Strict positivity is known at `q=7` and on `q≥5000`.
The intervening source sign remains open.

For `K=4q² exp(x−2q)`, the compensation satisfies `G/K≥g(q)`, where

`g(q)=3(2q−3)² − (1000001/1000000)(q/7−99/500)((2q−3)(8q²−30q+15)/2+(2q−3)²/100000)`.

The first-atom slope denominator cancels against its squared mass. The exact
slope, likelihood errors and tangent `2x≤q/7−99/500` prove this quartic bound.
Also `0<exp(−3q)≤(19/25000000000)(7/q)^15`.

Let `A(q,z)` be the leading-pair Gaussian form, `U(q)=loadMap·nativeBasis(q)`,
and `V=paidSevenSchur`. The complete normalized cross-load dominates

`M(q,exp(−3q))`, where `M(q,z)=A(q,z)+g(q)U(q)ᵀVU(q)−(147/4000)I`.

These bounds are formalized in `FifthEvenCrossLoadPolynomialEnvelope.lean`:
`compensation_polynomial_lower`, `cross_weight_upper`, `cross_model_lower`.

A sufficient remaining certificate is positivity of both affine weight endpoints:
`M(q,0)` and `M(q,(19/25000000000)(7/q)^15)` for every `q≥7`.
Multiplication by `q^8` and `q^23` respectively gives polynomial matrices of
degrees at most 10 and 25. Their signs on the full ray remain open.
