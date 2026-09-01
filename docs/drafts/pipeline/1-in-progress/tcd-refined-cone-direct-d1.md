# TCD refined-cone direct D1

- **ID:** TCD-RC-D1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · TCD finite rank-three gate
- **Statement:** Every source-positive state in `StrictSourcePositiveRefinedParabolicClockCone` has strictly positive `modularThetaSourcePositiveReflectedEighthPolynomial`.

## Goal

Discharge actual missing-interval rank-three D1: physical theta states lie in refined cone, so conjecture gives `D1 > 0` on `0 < x < 137/2000`; seam and established far half-line give global D1. This closes finite TCD/S6F gate. Theta-specific cofinal source–divisor landing remains; generic sign-only landing is false.

## Gates

- [x] 0 → 1 in-progress: exact corpus predicate, source-pure, decisive proof chain, hostile computation only selected geometry
- [ ] 1 → 2 fully-proven: computation-free paper proof
- [ ] 2 → 3 formalized: unconditional Lean theorem, targeted build and axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Use determinant geometry, not coefficient certificates. Prove scale-Loewner increase from source `sl₂` Cartan variation; at scale floor prove clock-square concavity; reduce to seam and outer face; prove outer-face decrease and corner positivity by analytic identities. Failure of any step pivots to singular-face Lie derivative modulo D1.

## No-go closure

- **Killed shortcuts:** static chamber without scale floor; scalar/matrix/operator contravariant carriers; raw matrix-Bernstein Gram; global wall monotonicity; higher alternating clock derivatives.
- **Strongest positive survivor:** refined cone itself remains diagnostic-positive for D1; scale velocity is the Cartan derivative of signed Hankel matrix.
- **Status:** conjecture only. No computational coefficient, value, factorization, or certificate is admissible in proof.

