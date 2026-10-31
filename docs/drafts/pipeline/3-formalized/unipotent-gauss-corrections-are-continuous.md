# Unipotent Gauss corrections are continuous

- **Stage:** 3-formalized
- **Parent:** [Triangular root coefficients](../1-in-progress/triangular-root-coefficients-unfold-arithmetic-cells.md).
- **Statement:** Over any commutative ring, upper and lower Gauss
  coefficients of an actual unipotent product equal the current input
  coefficients plus a correction depending only on the two strict prefixes.
  Over a topological ring, these corrections are continuous.

## Proof

A fixed product coefficient is a finite convolution. The inverse of a
principal unit has coefficients given recursively by finite polynomial
expressions in earlier coefficients. Thus every decoded Gauss coefficient
is continuous in the free stream.

Complete each strict prefix by zeros. The audited prefix-dependence laws
identify its Gauss defect with the original product defect. Define the
correction by this finite completion. Completion is continuous coordinatewise;
stream multiplication and Gauss coefficient evaluation are continuous.
Subtracting the two current coefficients proves continuity of the correction
and the exact product identities.

## Lean

`HTGeometry/LoopEisenstein/UnipotentGaussContinuity.lean`:
`unipotentUpperGauss_product_eq_correction`,
`unipotentLowerGauss_product_eq_correction`,
`continuous_unipotentUpperGaussCorrection`, and
`continuous_unipotentLowerGaussCorrection` passed direct Lean and transitive
axiom audits. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
