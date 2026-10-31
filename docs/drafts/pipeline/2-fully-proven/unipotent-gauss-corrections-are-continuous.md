# Unipotent Gauss corrections are continuous

- **Stage:** 2-fully-proven
- **Parent:** [Triangular root coefficients](../1-in-progress/triangular-root-coefficients-unfold-arithmetic-cells.md).
- **Statement:** Upper and lower Gauss coefficients of an actual unipotent
  product equal the current input coefficients plus a continuous correction
  depending only on the two strict free-coefficient prefixes.

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
`unipotentUpperGauss_product_eq_correction`, its lower counterpart, and
`continuous_unipotentUpperGaussCorrection` with its lower counterpart.
Direct audit pending.
