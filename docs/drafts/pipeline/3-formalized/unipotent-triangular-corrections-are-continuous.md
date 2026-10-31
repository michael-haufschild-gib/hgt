# Unipotent triangular corrections are continuous

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Over every topological commutative ring, actual unipotent
  multiplication and inversion are continuous in coefficient-stream coordinates. Each finite
  triangular correction is continuous in its two strict prefixes.

## Proof

Every coefficient of a product is a finite convolution of input coefficients.
The coefficient recursion for `invOfUnit(a,1)` uses only earlier inverse
coefficients; strong induction proves continuity of each inverse coefficient.

Decoding a stream gives three entries whose coefficients are projections or
constants. The determinant-forced fourth entry is `a⁻¹(1+bc)`, so all four
entries have continuous coefficients. Matrix multiplication and coefficient
extraction therefore give a continuous map on the product of two stream spaces.
The determinant-one inverse is the adjugate, so its four entries are the
original entries with signs and positions changed; its stream is continuous too.

Zero extension of a finite prefix is continuous coordinatewise. The triangular
correction is one product-stream coordinate minus the two input coordinates,
evaluated on these zero extensions. It is consequently continuous.

## Lean

`HTGeometry/LoopEisenstein/UnipotentCoefficientContinuity.lean`:
`continuous_unipotentStreamProduct`, `continuous_unipotentStreamInverse`,
`continuous_unipotentTriangularCorrection`.
Direct `lake --old env lean` check passed. All three transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
