# Elliptic idele Haar modulus is the global magnitude

- **Stage:** 1-in-progress
- **Parent:** [Arithmetic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** For every actual idele `u`, its additive Haar modulus on the
  elliptic adeles equals `ideleMagnitude u`.

## Reduction

Choose a finite set `S` containing every finite place where `u` has nonunit
valuation. Both `u` and `u⁻¹` preserve each integral local ball outside `S`.
Hence `u·O_A` lies in the finite cylinder for `S`. Under its audited Haar
coordinates, this image is the product of `u_v·O_v` for `v∈S`, the whole
compact integral tail, and `u_∞·O_∞`.

The audited local Haar modulus formula gives these factors their normalized
local magnitudes. Their product is the actual idele magnitude because every
omitted factor is one. Since `O_A` has Haar mass one, the Haar-character
ratio formula identifies the global modulus with this product.

## Remaining proof obligations

Formalize the scaled-box coordinate identity and its finite-product measure.
No new product formula or quotient normalization is assumed.
