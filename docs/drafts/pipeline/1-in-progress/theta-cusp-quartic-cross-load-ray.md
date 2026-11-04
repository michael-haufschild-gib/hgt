# Quartic cross-load reserve from scale eight

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** For `q=π exp(2x)≥8`, the complete matrix
  `H(x)−(3/20)K(x)q⁴B` is positive definite, where
  `K=4q² exp(x−2q)` and `B=loadMapᵀ paidSevenSchur loadMap`.

At `q=8`, the existing lower comparison has coefficient `g(8)/2<−(3/20)8⁴`,
so its certified positive reserve supplies the endpoint.
The proposed ray certificate must retain the unequal atom pair and control
the complete-source remainder; positivity at the endpoint does not imply the ray.

Candidate certificate: bound the pair weight between zero and
`exp(−24)(8/q)¹⁵`, using its proved rational upper enclosure. Clear denominators
by `q²³`, then certify both affine endpoint matrices through their coefficient
matrices in `q−8`. Subtract the actual cross-load and the existing `147/4000`
complete-source remainder allowance before testing coefficient signs.

The unit quartic profile is
[excluded at scale thirty-two](../../../../formal/GaloisForLFunctions/ThetaCuspSections/FifthEvenPolynomialCrossObstruction.lean).
The truncated quartic has a proved scalar comparison on `q≥8`, `x²≤1/2`:
`G_P(x)>−(3/20)K(x)q⁴`
(`FifthPolynomialCross.compensation_compact_quartic_lower`, Lean, standard
axioms). Thus this matrix reserve would pay its entire retained branch from
scale eight. The matrix ray itself remains unproved.
