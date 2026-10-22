# Thermal/de Sitter--zeta quarter cross-center Gamma-separation universality law

- **ID:** thermal-desitter-zeta-quarter-cross-center-gamma-separation-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare`,
  `centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth`,
  `hypertranscendentalOver_gammaOrbitProductMero`, and
  differential-algebraic gauge invariance
- **Statement:** At every Coulomb partial wave and every thermal exponential gauge, the quotient
  of the thermal/de Sitter reconstructed positive Gamma square by the centered-zeta
  phase--intensity reconstructed positive Gamma fourth power is hypertranscendental over
  `ℂ(z)`. Consequently no differentially algebraic multiplicative calibration converts one
  reconstructed channel into the other.

## Goal

Compare two independently reconstructed oriented Gamma amplitudes at their actual affine
centers and expose the noninteger-orbit separation invisible inside either tomography theorem
alone.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean check and final global axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof collision audit pending

## Corpus inputs

- `thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare`
- `centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth`
- `hypertranscendentalOver_gammaOrbitProductMero`
- `differentialAlgebraicOver_physicalExponentialMero`
- `physicalExponentialMero_ne_zero`
- `HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff`

## Proof

**[PROVED HERE]** For a partial wave `ℓ`, thermal/de Sitter tomography gives

`T = Γ(z + ℓ + 1)^2 exp(λz)`.

Centered-zeta phase--intensity tomography gives

`Z = Γ(z + 1/4)^4`.

Their quotient is therefore the signed two-orbit Gamma product with charges `2` and `-4`,
multiplied by the nonzero differentially algebraic exponential gauge:

`T/Z = Γ(z + ℓ + 1)^2 Γ(z + 1/4)^(-4) exp(λz)`.

The two affine centers are never integer translates. Indeed,

`1/4 - (ℓ + 1) ∉ ℤ`,

because multiplying a hypothetical equality by four would equate an integer congruent to one
modulo four with a multiple of four. The finite signed Gamma-orbit theorem therefore makes the
two-orbit factor hypertranscendental over `ℂ(z)`. Multiplication by the nonzero
differentially algebraic exponential preserves hypertranscendence, proving the quotient law.

If a differentially algebraic calibration `g` satisfied `T = gZ`, then nonvanishing of
`Z = Γ(z+1/4)^4` would give `T/Z = g`, contradicting quotient hypertranscendence. No computation
is used. ∎

## Strict gain over corpus endpoints

Thermal/de Sitter tomography reconstructed an oriented Gamma square only at integral Coulomb
centers. Centered-zeta tomography reconstructed a positive Gamma fourth power only at the
quarter center. Neither compared the two outputs. Their closure detects a permanent
noninteger-orbit charge separation and rules out every differentially algebraic calibration
between the reconstructed physical channels.

## Lean certificate

- Planned module:
  `GaloisForLFunctions.RHTower.ThermalDeSitterZetaQuarterCrossCenterGammaSeparationUniversalityLaw`
- Planned main theorem:
  `thermalDeSitter_centeredZetaQuarter_crossCenterGammaSeparationUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/ThermalDeSitterZetaQuarterCrossCenterGammaSeparationUniversalityLaw.lean`
  pending.
- Umbrella:
  pending import by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Deferred until dependency-closed paper proof has a checked Lean realization.

## Log

- 2026-07-23 — fresh cross-folder terminal scan exposed the integral-Coulomb/quarter-zeta center
  mismatch between two oriented Gamma reconstruction theorems.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
