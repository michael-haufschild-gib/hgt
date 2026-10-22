# Xi--Hurwitz full transverse aperture-spectrum universality law

- **ID:** xi-hurwitz-full-transverse-aperture-spectrum-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the principal Hurwitz phase supremum, global
  rectangular one-sided exponent threshold, complete Hedenmalm aperture-width theorem, and
  eighteen-chart transverse universal certificate
- **Statement:** For every positive Gaussian temperature, positive rectangular width,
  admissible cutoff, and exact nonnegative two-channel split, the full transverse universal
  certificate holds at a positive aperture exactly when that aperture is at least the supremal
  principal Hurwitz monodromy phase. If the right Xi divisor is nonempty, all admissible positive
  apertures therefore form the closed ray beginning at that intrinsic phase.

## Goal

Identify the complete multi-chart aperture spectrum from actual terminal theorems. Do not append
another RH-equivalent proposition: compute the exact threshold set at every positive transverse
scale, including the false-RH chamber.

## Gates

- [x] 0 → 1 in-progress: theorem-first terminal-symbol scan
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: completed; negative priority result

## Corpus inputs

- `xiHurwitzRightPrincipalPhaseSup_eq_transverseSup`
- `xiRectangularWeilTailPowerLower_iff_transverseSup_le_global`
- `xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le`
- `hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound`
- `hedenmalmGaussianHankelTailCone_iff_transverseUniversalCertificate`
- `xiRightTransverseSup_pos`

## Proof

**[PROVED HERE]** Fix positive `tau`, `L`, and `alpha`, an admissible cutoff `N`, and an exact
two-channel split. The transverse universal-certificate theorem identifies the complete
eighteen-chart certificate at `alpha` with the complete Hedenmalm Gaussian tail cone. The
aperture-width theorem identifies that cone with the assertion that every Xi zero lies in
`Re rho ≤ 1/2 + alpha`.

The global rectangular exponent theorem and its all-zero form identify this half-plane bound with
`xiRightTransverseSup ≤ alpha`, including the empty right-divisor case. The principal Hurwitz
phase theorem identifies `xiRightTransverseSup` exactly with
`xiHurwitzRightPrincipalPhaseSup`. Chaining the equivalences proves

`XiTransverseUniversalCertificate tau L alpha N a b`

if and only if

`xiHurwitzRightPrincipalPhaseSup ≤ alpha`.

Now assume the right Xi divisor is nonempty. Its transverse supremum is positive, hence so is the
equal Hurwitz phase supremum. Therefore an aperture lies above the phase supremum exactly when it
is positive and carries the complete certificate. Extensionality gives equality of the admissible
aperture set with the closed upper ray
`Set.Ici xiHurwitzRightPrincipalPhaseSup`. ∎

## Strict gain over corpus endpoints

`XiHurwitzPrincipalPhaseGrowth` computes one rectangular power exponent from the Hurwitz phase.
`XiTransverseSpectralUniversalityLaw` gives a pointwise equivalence between a Hedenmalm cone and
eighteen analytic, arithmetic, projective, and thermal charts. Neither theorem computes the
parameter set on which the full certificate holds. The induced law upgrades a one-chart exponent
identity and a pointwise multi-chart equivalence to an exact full-corpus phase spectrum with an
intrinsic HGT endpoint.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiHurwitzFullTransverseApertureSpectrumUniversalityLaw`
- Pointwise theorem:
  `xiTransverseUniversalCertificate_iff_hurwitzPrincipalPhaseSup_le`
- Main theorem:
  `xiHurwitzFullTransverseApertureSpectrum_eq_Ici_principalPhaseSup`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/XiHurwitzFullTransverseApertureSpectrumUniversalityLaw.lean`
- Result: passed warning-free.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after the dependency-closed Lean proof passed. The closest primary source found was
Masatoshi Suzuki, *Weil's quadratic form via the screw function* (arXiv:2606.09096), which studies
localized Weil quadratic forms, Friedrichs realizations, and conjectural spectral limits. It does
not define the corpus's Hurwitz monodromy phase, its transverse supremum, or the eighteen-chart
aperture certificate. Targeted searches combining those objects found no source stating the exact
closed-ray spectrum. This is a negative search result, not a priority claim.

## Log

- 2026-07-23 — fresh post-Law-419 scan covered 4,616 modules, 57,592 declarations, 692 terminal
  roots, and 2,980 rare-symbol terminal pairs.
- 2026-07-23 — shared `xiRightTransverseSup` cluster exposed the unconsumed composition.
- 2026-07-23 — dependency-closed paper proof completed before Lean source or literature search.
- 2026-07-23 — Lean source passed the required exact-file check warning-free and was wired into
  `GaloisForLFunctions/RHTower.lean`.
- 2026-07-23 — post-proof literature audit found localized Weil/screw-function theory, but no
  Hurwitz-phase endpoint classification of the full transverse certificate spectrum.
