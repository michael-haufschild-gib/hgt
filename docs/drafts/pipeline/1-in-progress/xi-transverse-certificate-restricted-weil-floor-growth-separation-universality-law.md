# Xi transverse-certificate/restricted-Weil floor growth-separation universality law

- **ID:** xi-transverse-certificate-restricted-weil-floor-growth-separation-universality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the full transverse certificate threshold and the
  restricted-Weil sampled/continuous growth lower bounds
- **Statement:** Under false RH, failure of the full transverse certificate at a positive
  aperture `alpha` forces the associated restricted-Weil floor's sampled exponent, continuous
  exponent, and absolute-convergence abscissa strictly beyond `alpha`.

## Goal

Eliminate `xiRightTransverseSup` between the complete eighteen-chart aperture law and three
restricted-Weil floor growth laws. The resulting statement must transfer failure of one
geometric/analytic certificate into strict quantitative growth of a different observable.

## Gates

- [x] 0 → 1 in-progress: low-frequency shared-invariant edge, complete source read, corpus
  research search, well-posed source-pure statement
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check and RHTower umbrella import
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `hedenmalmGaussianHankelTailCone_iff_transverseUniversalCertificate`
- `hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound`
- `xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le`
- `xiRectangularWeilTailPowerLower_iff_transverseSup_le_global`
- `restrictedWeilFloor_abscissa_lower_of_not_rh`
- `transverseSup_le_sampledUpperLogPowerExponent_of_false_rh`
- `transverseSup_le_apertureUpperLogGrowthExponent_of_false_rh`

## Proof

**[PROVED HERE]** Fix positive `tau`, width `L`, and aperture `alpha`, with one admissible
negative-channel split and one nonnegative restricted-Weil floor envelope.

The Hedenmalm tail-cone equivalence, Xi half-plane-bound equivalence, and rectangular-Weil
transverse equivalence identify the full transverse certificate at `alpha` with

`xiRightTransverseSup ≤ alpha`.

If the certificate fails, therefore `alpha < xiRightTransverseSup`.

Under false RH, the restricted-Weil growth theorems give

`ofReal xiRightTransverseSup ≤ sampled upper logarithmic exponent`,

`ofReal xiRightTransverseSup ≤ continuous aperture upper logarithmic exponent`,

and

`1 + xiRightTransverseSup ≤ absolute-convergence abscissa`.

Strict monotonicity of the real embeddings into `ENNReal` and `EReal`, followed by transitivity,
replaces the intermediate transverse supremum by `alpha` in all three bounds. ∎

## Strict gain over corpus endpoints

No existing theorem sends failure of the full eighteen-chart certificate into strict growth of a
restricted-Weil floor. Existing endpoints only compare both mechanisms separately with the latent
transverse supremum. The new result removes that latent quantity and produces strict observable
bounds.

## Lean formalization

- Main theorem:
  `xiTransverseCertificate_failure_forces_restrictedWeilFloor_strictGrowth`
- Module:
  `GaloisForLFunctions.RHTower.XiTransverseCertificateRestrictedWeilFloorGrowthSeparationUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/XiTransverseCertificateRestrictedWeilFloorGrowthSeparationUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof searches found classical Weil positivity, Riesz/Hardy--Littlewood growth criteria,
Li-type inequalities, and standard abscissa theory. They did not find a result transferring
failure of a complete transverse Xi certificate into simultaneous strict sampled, continuous,
and Dirichlet-abscissa growth of a restricted-Weil floor. Relevant comparison points:

- Weil's explicit-formula positivity criterion:
  `https://en.wikipedia.org/wiki/Weil%27s_criterion`
- Agarwal--Garg--Maji, “Riesz-type criteria for the Riemann hypothesis”:
  `https://arxiv.org/abs/2202.00637`
- Garg--Maji, “Equivalent criteria for the Riemann hypothesis for a general class of
  L-functions”: `https://arxiv.org/abs/2409.17708`

Novelty remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — generated from the post-LAW439 low-frequency terminal pair between full
  transverse-aperture spectrum and restricted-Weil floor growth.
- 2026-07-23 — dependency-closed proof completed before Lean implementation and literature search.
- 2026-07-23 — exact Lean theorem passed without warnings and was wired into the RHTower umbrella.
- 2026-07-23 — post-proof literature audit found no exact or equivalent law.
