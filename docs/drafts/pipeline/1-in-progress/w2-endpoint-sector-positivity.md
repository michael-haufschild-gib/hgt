# W2: endpoint sector positivity

- **ID:** w2-endpoint-sector-positivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Arithmetic symmetric-group characters](w2-representation-construction.md)
- **Target:** Transfer existing divisor visibility cones to finite-order total positivity of endpoint exterior coefficients.

## Candidate transfer

Write `t_q=xiSpectralPoint q`, `D_q=1/4+t_q²`, and `α_q=1/D_q`. If
`cos(π/(k+1)) |t_q²| ≤ Re(t_q²)`, then adding the positive real number `1/4` preserves this
sector inequality: for `0≤c≤1` and `a≥0`,
`c|a+z|≤ca+c|z|≤a+Re z`. Inversion and positive normalization preserve the absolute argument.
Conjugate endpoint factors therefore have the quadratic `PF_k` property.

The corpus provides `PFSeq.quadratic_of_cone`, closure under convolution and coefficient
limits, and grouping finite products under an involution in
`RHTower/XiHorizontalSlicePolyaFrequencyCone.lean`. Applying them to the endpoint product
should give `PFSeq k (fun n => (xiEndpointExteriorCoefficient n).re)` from the same cone.
An unconditional corollary must discharge the cone using an existing unconditional theorem.

## Product mechanism

For a conjugate pair with denominator `D`, the even factor is
`(1+x²/D)(1+x²/conj D) = (x⁴+2 Re(D)x²+|D|²)/|D|²`.
Set `A=(|D|+Re D)/2` and `C=(|D|−Re D)/2`. The corpus quadratic cone theorem applies directly.
Products over `S ∪ conj(S)` are conjugation-stable and form a cofinal net. Genus-zero local
uniform convergence is supplied by
`HTGeometry.canonicalWeightProduct_hasProdLocallyUniformlyOn` in `GeneralPrimaryFactor.lean`.
The `PFTaylorAtZero` closure theorem then applies to `x↦E(x²)`.

## Obligations

- Prove sector preservation under positive real translation.
- Match conjugate factors with the exact quadratic coefficient criterion.
- Pass from conjugation-stable finite products to the endpoint coefficients.
- Identify relevant Toeplitz minors with Young projections before claiming representation positivity.

No transfer theorem or mixed Young projection is yet formalized. Fixed finite order does not
establish the full arithmetic character criterion.
