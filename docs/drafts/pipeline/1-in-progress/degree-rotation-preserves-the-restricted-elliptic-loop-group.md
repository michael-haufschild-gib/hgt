# Degree rotation preserves the restricted elliptic loop group

- **Stage:** 1-in-progress
- **Parent:** [Elliptic unfolding](finite-field-eisenstein-unfolding.md).
- **Statement:** Every actual idele acts by degree rotation on the restricted
  central loop group. Positive Borel and both intrinsic Borel torus
  coordinates are preserved. No arithmetic-group invariance is asserted.

## Local mechanism

For a valuation-unit scalar `q`, power-series rotation multiplies coefficient
`n` by `qⁿ`, preserving every coefficient-integrality condition. At the
adjacent vertex, rotation equals the backward shift applied to the rotated
positive matrix with its two off-diagonal entries rescaled by `q⁻¹` and `q`.
Four-root generation proves this equality for the actual central lifts.
Both integral vertices, hence their generated integral group, are preserved.

An idele is a valuation unit outside finitely many finite places. Intersecting
this set with a loop's integral-place set proves restrictedness of its
rotation. Rotation by the inverse idele supplies the inverse map.

## Established inputs

[Positive splitting and Borel-coordinate compatibility](../3-formalized/degree-rotation-preserves-positive-loop-spectral-coordinates.md)
passed direct Lean and axiom audits. Ring diagonal rescaling is written;
its direct check and the full integral-vertex proof remain.
