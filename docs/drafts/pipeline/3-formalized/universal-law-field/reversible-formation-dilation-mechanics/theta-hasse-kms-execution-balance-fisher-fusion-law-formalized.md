# Theta--Hasse--KMS execution balance — Lean formalization certificate

- **Source card:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/reversible-formation-dilation-mechanics/theta-hasse-kms-execution-balance-fisher-fusion-law.md`
- **Lean modules:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveThetaHasseKMSExecutionBalance.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ThetaHasseKMSContinuousAssembly.lean`
- **Stage:** 3-formalized
- **Completed:** 2026-08-28

## Certified declarations

1. `tsum_geometricLayerMass_eq_one` proves exact normalization of the countable geometric
   Hasse/KMS packet.
2. `geometricLayerMass_succ_div` proves adjacent-depth recovery of the packet parameter.
3. `tsum_sq_geometricLayerMass` computes exact packet purity.
4. `geometricExecutionTV_eq_one_sub_purity` proves collision/reset loss equals KMS linear entropy.
5. `tsum_geometricLayerShannonTerm` proves packet Shannon entropy equals the closed KMS entropy
   formula.
6. `strictMono_thetaHasseRatio` proves source-scale reconstruction is strict.
7. `strictMono_thetaHasseExecutionTV` and `strictMono_thetaHasseExecutionEntropy` prove both
   execution defects strictly increase with source scale.
8. `symmetricSourceTiltMean_reflection_gap_eq_zero_iff` proves unique central balance in every
   nondegenerate even two-point source fibre.
9. `thetaHasseExecutionTV_balance_eq_zero_iff` and
   `thetaHasseExecutionEntropy_balance_eq_zero_iff` instantiate that selection law for both KMS
   mixedness statistics.
10. `finiteWeightedCovariance_sq_le_variance_mul_variance` proves finite Fisher-response control
    by weighted Cauchy--Schwarz.

11. `ThetaHasseKMSContinuousAssembly.lean` adds literal theta-law averages, continuous covariance
    differentiation and strict response, reflected half-line balance, unique central fibre,
    intrinsic-image homeomorphism/properness, exact Popoviciu Fisher constants, common-recovery
    composition, source-averaged purity/Shannon conservation, and normalized Fourier/Xi
    reconstruction.

## Exact certification boundary

Lean certifies the full dependency-closed paper surface: geometric normalization, marked
reconstruction, purity/entropy conservation, literal continuous theta-source averages,
differentiation under the tilted integral, strict covariance response, exact reflected half-line
balance, properness onto the intrinsic image, Fourier/Xi reconstruction, exact Fisher constants,
and common-recovery composition. ULF-RFDM-2 has no remaining formal assembly obligation.

## Audit

- Direct check:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveThetaHasseKMSExecutionBalance.lean`
- Final build:
  `lake build GaloisForLFunctions.HTGeometry.ThetaHasseKMSContinuousAssembly`
- Umbrella imports: `GaloisForLFunctions.HTGeometry.UniversalLawField`,
  `GaloisForLFunctions.HTGeometry`
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- Formal lint: new module is umbrella-reachable and contains no forbidden declaration; current
  repository lint reports unrelated concurrently added unreachable modules.
