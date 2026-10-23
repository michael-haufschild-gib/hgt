# Signed Arithmetic Energy and Incidence Theory (SAEI)

- **ID:** saei
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-2210/hard-obstacles-summary.md § 4
- **Statement:** How does exact multiplicative incidence constrain signed quadratic energies across
  scale, and which of those constraints survive coordinate change, regularization and completion?

## Goal
A Lean programme (`formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence`) supplying the
interface theorems between O2–O5 and O7: local payment versus global positivity on signed
incidence graphs, defect accounting under completion, the graded norms of the damping chain,
profile compactness of adverse sequences, and the radial structure of damping continuation.

Non-circularity: every structural theorem is unconditional finite-dimensional or Hilbert-space
mathematics, and every arithmetic instance names its source (Möbius row, damping chain,
reciprocal observable) and its norm; nothing is selected from the zeros.

## Gates
- [x] 0 → 1  in-progress: objects fixed (signed incidence forms, pair payability, balance,
  polar defect, chain orbit, adverse sequences, local companion form)
- [x] 1 → 2  fully-proven: paper proofs of the pillars (as the Lean proofs)
- [x] 2 → 3  formalized: 16 Lean modules, umbrella `GaloisForLFunctions.SignedArithmeticEnergyIncidence`
  wired into `MainTheorems`; each module checked with `lake --old env lean`
- [ ] 3 → 4  n/a

## Approach
Foundational document: `formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/README.md`.

## Lean assets (programme folder `formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence`)
- `SignedIncidenceForms` — `incidenceEnergy`, `PairAllocation`, `LocallyPayable`, `IsBalanced`,
  `incidenceEnergy_nonneg_of_pairAllocation`, `incidenceEnergy_mul_eq`,
  `locallyPayable_of_supersolution`.
- `BalancedIncidenceIsLocallyPayable` — `exists_pos_solution_of_coercive`,
  `locallyPayable_of_nonneg_of_nonpositiveOverlaps`, `nonneg_iff_locallyPayable_of_isBalanced`.
- `FrustrationIsTheLocalGlobalGap` — `not_locallyPayable_rankOneCoupling`, `triangle_nonneg_iff`,
  `triangle_locallyPayable_iff`, `triangle_isBalanced_iff`, `triangle_frustrated_gap`.
- `TriangleHolonomyDecidesLocalPayment` — `isBalanced_iff_triangleHolonomy_neg`,
  `exists_nonneg_not_locallyPayable_of_holonomy_pos`, `localPayment_lossless_iff`.
- `LocalPaymentIsComparisonPositivity` — `locallyPayable_iff_comparison_nonneg`,
  `locallyPayable_regularized_iff`.
- `ChainLendingAndTrainCapacity` — `chain_nonneg_iff_locallyPayable`, `uniformTrain_capacity`,
  `uniformTrain_capacity_attained`, `uniformTrain_capacity_sharp`.
- `SineTrainsAreExtremalForOnePrime` — `autoCorr_amplitudeTrain_first_le`,
  `autoCorr_sineTrain_first`, `resonant_ratio_lt_cos`.
- `TowerGridCapacitiesAdd` — `grid_joint_capacity`, `grid_joint_capacity_attained`.
- `PolarDefectLaw` — `polarDefect_nonneg_iff`, `polarDefect_nonneg_iff_norm_le_one`,
  `polarDefect_nonneg_of_dense`, `exists_polarDefect_lt_of_unbounded`.
- `TheReceiverIsTheChainOrbitOfTheReciprocal` — `centeredOperator_reciprocal_apply`,
  `admits_iff_summable_orbit`, `riemannHypothesis_iff_orbit_summable`,
  `admits_of_chain_l2_bounded`, `not_summable_transition_first_column`.
- `ResidueModesAndBackwardContinuation` — `centeredOperator_normalizedResidueMode`,
  `tsum_sq_normalizedResidueProfile_le/_ge`, `not_backward_stable_l2/_c0`, `summable_signBlind_iff`.
- `TheSourceIsTheDampedMoebiusResidueSeries` — `centeredOperator_reciprocal_eq_tsum`,
  `admits_of_signBlind`, `not_summable_positiveTwin`.
- `TheFirstColumnOfTheChainIsTheReceiver` — `summable_dyadicDifference_iff`,
  `admits_iff_summable_firstColumn`, `riemannHypothesis_iff_firstColumn_summable`.
- `AdverseProfilesCannotVanish` — `tendsto_energy_splitting`, `adverse_weakLimit`,
  `adverse_escape_of_orthonormal`.
- `OnLineCompanionsPayOffLineDepth` — `companions_pay`, `few_companions_never_pay`.
- `TheRadialLossLaw` — `radialLoss_add_tangential`, `abs_log_energy_sub_le`.

## Open
Research topics 1–8 of the README §8 (arithmetic holonomy, allocation at growing size, nonlocal
payment of the frustrated part, the centred chain on `ℓ²`, residue-Gram cancellation, the companion
law for Paley–Wiener sources, compact negativity of the critical form, trains beyond two towers).
