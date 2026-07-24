# Thermal/beta-QED/zeta three-Gamma-orbit superselection law

- **ID:** thermal-beta-qed-zeta-three-gamma-orbit-superselection
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare`,
  `constantMagneticQEDSpinStatisticsRatioMero_eq_gauge_mul_scaledEulerBeta`,
  `scaledBetaDirichletJacobiQED_spinGaugeUniversality`,
  `centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth`,
  `gammaShiftMero_add_nat`, and the finite Gamma-orbit charge theorem
- **Statement:** Thermal/de Sitter positive reconstruction, the common scaled-beta/Dirichlet/
  Jacobi-MANOVA/QED spin class, and centered-zeta quarter reconstruction form three pairwise
  distinct nonzero differential-algebraic multiplicative gauge classes.

## Goal

Classify three previously separate physical/statistical reconstruction mechanisms by their
surviving Gamma translation-orbit charges.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean check pending
- [ ] 3 → 4 publication-ready: literature audit forbidden until Lean proof

## Corpus inputs

- `thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare`
- `constantMagneticQEDSpinStatisticsRatioMero`
- `constantMagneticQEDCombinedGammaCarrierMero`
- `constantMagneticQEDSpinStatisticsRatioMero_eq_gauge_mul_scaledEulerBeta`
- `scaledBetaDirichletJacobiQED_spinGaugeUniversality`
- `centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth`
- `hypertranscendentalOver_thermalDeSitterCenteredZetaPositiveCrossRatioMero`
- `gammaShiftMero_add_nat`
- `hypertranscendentalOver_gammaPositiveShiftPairMero`
- `hypertranscendentalOver_gammaOrbitProductMero`
- `DifferentialAlgebraicGaugeEquivalent`

## Proof

**[PROVED HERE]** Let `T_{ell,lambda}` be the thermal-CFT response times its matched de Sitter
zero-mode carrier, `B` the QED spin-statistics ratio (hence also the Law407 scaled-beta class),
and `Z` the centered-zeta positive reconstruction.

Existing tomography identities give

`T_{ell,lambda} = Gamma(z+ell+1)^2 E_lambda`,

`B = Gamma(z+1) / Gamma(z+1/2)`,

`Z = Gamma(z+1/4)^4`,

where `E_lambda` is nonzero and differentially algebraic. Gamma recurrence gives
`Gamma(z+ell+1)=P_ell(z) Gamma(z+1)` with nonzero rational `P_ell`. Therefore

`T_{ell,lambda}/B =
  P_ell(z)^2 E_lambda Gamma(z+1) Gamma(z+1/2)`.

The last two Gamma factors have equal positive charge, so their product is
hypertranscendental even if presented on colliding translation orbits; multiplying by the
nonzero DA gauge preserves hypertranscendence.

Next,

`B/Z = Gamma(z+1)^1 Gamma(z+1/2)^(-1) Gamma(z+1/4)^(-4)`.

The shifts `1`, `1/2`, and `1/4` lie on three distinct integer-translation orbits and all three
charges are nonzero. The finite Gamma-orbit theorem therefore makes this quotient
hypertranscendental. The existing thermal/zeta cross-center theorem already proves
`T_{ell,lambda}/Z` hypertranscendental.

If two nonzero carriers were related by a nonzero DA multiplicative gauge, their quotient would
equal that gauge and be differentially algebraic. Each of the three hypertranscendental
quotients contradicts such an equivalence. Law407 identifies `B` by a nonzero DA gauge with the
unit-slope scaled Euler beta, reciprocal binary Dirichlet normalizer, and the one-channel
Jacobi/MANOVA-to-Gaussian quotient. Hence these are exactly three pairwise distinct gauge
classes, with the full four-domain family occupying the middle class. No computation is used. ∎

## Strict gain over corpus endpoints

The thermal/zeta theorem separates only integral and quarter reconstructions. Law407 constructs
the beta/QED half-orbit class but compares it to neither reconstruction. Their theorem-generated
closure supplies both missing pairwise obstructions and upgrades two disconnected results to a
three-class superselection theorem spanning HTGeometry and RHTower.

## Lean certificate

- Planned module:
  `GaloisForLFunctions.RHTower.ThermalBetaQEDZetaThreeGammaOrbitSuperselectionLaw`
- Planned main theorem:
  `thermalBetaQEDZeta_threeGammaOrbitSuperselectionUniversality`
- Required exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/ThermalBetaQEDZetaThreeGammaOrbitSuperselectionLaw.lean`
- Required umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Forbidden until dependency-closed Lean proof passes.

## Log

- 2026-07-23 — theorem-terminal scan exposed integral, half, and quarter Gamma charge sectors.
- 2026-07-23 — corpus research found the two-class thermal/zeta theorem and four-domain
  beta/QED equivalence, but no theorem closing them into three pairwise separated classes.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
