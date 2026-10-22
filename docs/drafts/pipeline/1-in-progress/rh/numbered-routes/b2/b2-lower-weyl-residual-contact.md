# B2 lower Weyl residual/contact test

- **ID:** B2-LWR
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; source coefficient algebra on paper, Lean open
- **Source:** `CapAngularFluxCusp.constantCoefficient`, `LiteralCyclicPeierlsAffineCuspIncidence.lowerWeylFaceCoefficient`, `MixedRadialOverlap.bulkOverlapCoefficient_eq`, `LiteralCyclicPeierlsSelfInverseSquarePhysical.self_overlapInverseSquare_ne_zero`.
- **Statement:** At any left-half Xi copy, the square-reader plus cyclic-cap residual has a nonzero lower Weyl coefficient on at least one of the physical radial fibres `R=2,3`; an additional ordered lift contribution is required for B2 cancellation. This is a B2 constraint, not progress on PW-B's normalized cap/lift-defect magnitude identity.

## Goal

Retired HB/B2 chain: full-circle CTP source → ordered Einstein current with lift defect and contact → coefficientwise cap/cusp boundary equality. This tests a local boundary obstruction; it does not address the surviving PW-B chain `Schwarz-critical CTP cancellation → normalized cap/lift-defect magnitude → fixed-grade PW imbalance → RH`.

## Gates

- [x] 0 → 1: literal source functions and physical radial fibres identified.
- [ ] 1 → 2: audit all cap-family and Fourier-tail contributions in the full residual.
- [ ] 2 → 3: closed Lean theorem and targeted module audit.

## Approach

Write `ρ=q.1`, `s=physicalRate q branch`, `w=physicalFundamentalFrequency q side`, `L=lowerWeylFaceCoefficient q`. Direct expansion of the source definitions gives
`constantCoefficient (center q) (physicalAngularParameter q) false false false = -(ρ-1)(3ρ-2)L`.
The exact radial formulas give `Ω/C = (overlapConstant s w + overlapInverseSquare s w/R²)/2`, where `C` is the radial cap-current coefficient. Hence the lower Weyl coefficient of the residual, divided by `C`, is
`L * ((overlapConstant s w + overlapInverseSquare s w/R²)/2 - s(s-1)(ρ-1)(3ρ-2)/4)`.
For `Re ρ<1/2`, `L≠0`; the inverse-square coefficient is nonzero for every physical branch/side. The two literal fibres therefore cannot both cancel. Prove the displayed source identity in Lean, then identify it with the full cusp-family coefficient and verify the final physical-face statement. No claim about a finite-part contact cancellation follows from this local obstruction.

## Status

Paper algebra checked against the named source definitions. The cap coefficient identity passed in a two-import Lean scratch check; the full three-import no-go did not complete within bounded foreground checks. No formal module is claimed. This local B2 constraint is not a PW-B result.
