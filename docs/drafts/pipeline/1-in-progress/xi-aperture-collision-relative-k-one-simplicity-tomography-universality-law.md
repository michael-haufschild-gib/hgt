# Xi aperture-collision relative-K1 simplicity-tomography universality law

- **ID:** xi-aperture-collision-relative-k-one-simplicity-tomography-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `xiCompletedApertureRegularizedResonantTwoPointDet_zero`,
  `xiLocalJordanNormal_iff_multiplicity_one`,
  `localDivisorJetInfinitesimalUnit_eq_one_iff`,
  `localDivisorJetLogUnit_eq_zero_iff`, and
  `xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`
- **Statement:** At an Xi divisor support point, the filled resonant aperture determinant has
  value `-4` exactly when the local Hedenmalm block is normal, the canonical relative-`K₁` unit
  is trivial, and its logarithmic regulator vanishes. Globally, uniform collision value `-4` is
  equivalent to Xi simplicity and to the complete Hedenmalm certificate.

## Goal

Convert the quantitative aperture collision tomography `-4m²` into an exact simplicity atlas and
connect it to relative local-divisor algebra.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `xiCompletedApertureRegularizedResonantTwoPointDet_zero`
- `xiSupportMultiplicity_pos`
- `xiLocalJordanNormal_iff_multiplicity_one`
- `localDivisorJetInfinitesimalUnit_eq_one_iff`
- `localDivisorJetLogUnit_eq_zero_iff`
- `all_xiLocalJordanNormal_iff_simple`
- `xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`

## Proof

**[PROVED HERE]** At support point `ρ`, set `m = xiSupportMultiplicity ρ`. The filled resonant
determinant is exactly `-4m²`. Since `m` is a positive natural number, this value equals `-4`
exactly when `m = 1`. The local Jordan, relative-unit, and logarithmic-regulator classifications
each identify their respective condition with that same equation `m = 1`, proving the pointwise
four-chart equivalence.

After quantifying over all support points, uniform collision value `-4` is equivalent to normality
of every local Hedenmalm block, hence to global Xi simplicity. The established Hedenmalm
universality theorem then identifies it with the full eight-chart certificate. No computation is
used. ∎

## Strict gain over corpus endpoints

The aperture module recovered multiplicity quantitatively but did not identify its distinguished
simple-zero collision value or connect to local algebra. The relative-`K₁` law classified
simplicity but had no aperture-determinant observable. This closure makes `-4` a universal scalar
readout for all local and global simplicity charts.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiApertureCollisionRelativeKOneSimplicityTomographyUniversalityLaw`
- Main theorem:
  `xiApertureCollision_completeRelativeKOneSimplicityTomographyUniversality`
- Pointwise theorem:
  `xiCompletedApertureCollision_neg_four_iff_completeLocalSimplicity`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/XiApertureCollisionRelativeKOneSimplicityTomographyUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for resonant two-point determinants, analytic-zero multiplicity tomography, Hedenmalm quotients,
and local relative `K₁` found no exact collision. Closest primary sources:

- M. Katori and T. Shirai, *Zeros of the i.i.d. Gaussian Laurent series on an annulus: weighted
  Szegő kernels and permanental-determinantal point processes*,
  <https://arxiv.org/abs/2008.04177>, studies determinant kernels and analytic zero processes,
  not a filled resonant determinant equal to a squared local multiplicity.
- M. Kontsevich and S. Vishik, *Determinants of elliptic pseudo-differential operators*,
  <https://arxiv.org/abs/hep-th/9404046>, develops zeta-regularized determinants and their
  anomalies, not Xi aperture kernels or a relative-`K₁` simplicity readout.
- L. Hesselholt, *The tower of K-theory of truncated polynomial algebras*,
  <https://arxiv.org/abs/math/0702877>, treats relative `K`-groups of truncated polynomial
  rings, with no analytic aperture determinant or Hedenmalm certificate.

## Log

- 2026-07-23 — fresh aperture/multiplicity terminal scan exposed the `-4` simplicity atlas.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
