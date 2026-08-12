# Theta--Hasse--KMS execution balance — Lean formalization certificate

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/reversible-formation-dilation-mechanics/theta-hasse-kms-execution-balance-fisher-fusion-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveThetaHasseKMSExecutionBalance.lean`
- **Stage:** 3-formalized core
- **Date:** 2026-08-11

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

## Exact certification boundary

Lean certifies geometric normalization, marked reconstruction, purity/entropy conservation,
strict source response, reflected-balance selection, and finite Fisher covariance control. These
are the algebraic/analytic core through which Hasse packet, reset execution, KMS state, and Fisher
response fuse.

The full continuous theta-source average, its Fourier/Xi identity, differentiation under the
theta integral, explicit Popoviciu constants, and properness of the global balance map are not
claimed by this certificate. Existing theta-source modules provide several analytic ingredients,
but ULF-RFDM-2 remains only **core formalized** until those continuous statements are assembled in
one Lean module.

## Audit

- Direct check:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveThetaHasseKMSExecutionBalance.lean`
- Final build:
  `lake build GaloisForLFunctions.HTGeometry.ConstitutiveThetaHasseKMSExecutionBalance`
- Umbrella import: `GaloisForLFunctions.HTGeometry`
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- Formal lint: passed at certificate creation
