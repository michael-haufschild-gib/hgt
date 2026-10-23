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
- [x] 2 → 3  formalized: 33 Lean modules, umbrella `GaloisForLFunctions.SignedArithmeticEnergyIncidence`
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
  `exists_nonneg_not_locallyPayable_of_holonomy_pos`, `localPayment_lossless_iff`,
  `switchingEquivalent_iff_triangleHolonomy_eq`.
- `CycleHolonomyDecidesBalance` — `walkHolonomy_switch`, `isBalanced_iff_alignedCycles`,
  `isBalanced_iff_walkHolonomy_eq`, `nonneg_iff_locallyPayable_of_alignedCycles`,
  `walkHolonomy_triangle`.
- `FrustratedCyclesSpoilLocalPayment` — `frustratedCycle_poincare`,
  `frustratedCycle_energy_nonneg`, `exists_nodup_frustrated`, `cycleWitness_not_locallyPayable`,
  `localPayment_lossless_iff_isBalanced`, `localPayment_lossless_iff_alignedCycles`.
- `TheFrustratedCycleIsPaidAlongItsPath` — `antiperiodic_le_of_certificate`, `halfSine_telescope`,
  `frustratedCycle_capacity`, `frustratedCycle_capacity_attained`, `frustratedCycle_nonneg_iff`,
  `cycleWitness_locallyPayable_iff`, `cycleWitness_nonneg_iff`, `cycleWitness_window`.
- `FrustrationIsPaidAlongCanonicalPaths` — `PathCertificate`, `antiTerm_le_pathEnergy`,
  `incidenceEnergy_nonneg_of_pathCertificate`.
- `OddFoldingIsTheSourceOfFrustration` — `incidenceEnergy_mirror_odd`, `evenFold_lossless`,
  `oddFold_pos_iff`, `oddFold_lossless_of_antitone`, `oddFold_primeTriangle_not_isBalanced`,
  `exists_unpayable_odd_primeTriangle`, `evenFold_prime_lossless`.
- `TheOddWeilLedgerIsFrustratedOnlyByPrimes` — `weilKernel_antitone`, `oddFold_pos_imp_primeSum`,
  `frustrated_walk_has_primeSum`, `oddWeilLedger_lossless_of_no_primeSum`,
  `exists_weight_oddWeilLedger_primeTriangle_not_isBalanced`.
- `PositivityIsDecidedOnTheFrustrationTerminals` — `HarmonicFrame`, `incidenceEnergy_eq_reduced_add`,
  `nonneg_iff_interior_payable_and_reduced`, `nonneg_iff_two_terminal`, `exists_harmonicFrame`.
- `OnTheSimplexTwoTowersDoNotAdd` — `simplex_joint_capacity`, `simplex_joint_capacity_attained`,
  `simplex_capacities_do_not_add`.
- `LocalPaymentIsComparisonPositivity` — `locallyPayable_iff_comparison_nonneg`,
  `locallyPayable_regularized_iff`, `not_locallyPayable_iff_exists_overload`.
- `SignChangesNeedAntiAlignedOverlaps` — `polarForm_abs_le`, `exists_nonneg_polarSolution`,
  `polarForm_nonneg_iff_polarSolution`, `signChange_beats_abs`.
- `CartesianProductsAddGroundEnergies` — `incidenceEnergy_cartesian`, `cartesian_lower_bound`,
  `cartesian_attained`.
- `ChainLendingAndTrainCapacity` — `chain_nonneg_iff_locallyPayable`, `uniformTrain_capacity`,
  `uniformTrain_capacity_attained`, `uniformTrain_capacity_sharp`.
- `SineTrainsAreExtremalForOnePrime` — `autoCorr_amplitudeTrain_first_le`,
  `autoCorr_sineTrain_first`, `resonant_ratio_lt_cos`.
- `TowerGridCapacitiesAdd` — `grid_joint_capacity`, `grid_joint_capacity_attained`.
- `PolarDefectLaw` — `polarDefect_nonneg_iff`, `polarDefect_nonneg_iff_norm_le_one`,
  `polarDefect_nonneg_of_dense`, `exists_polarDefect_lt_of_unbounded`.
- `TheReceiverIsTheChainOrbitOfTheReciprocal` — `centeredOperator_reciprocal_apply`,
  `admits_iff_summable_orbit`, `riemannHypothesis_iff_orbit_summable`,
  `tendsto_truncation_partialEnergy`, `not_summable_transition_first_column`.
- `TheChainIsHilbertSchmidtAboveDampingOne` — `abs_centeredPrefix_le`, `centeredRow_eq`,
  `abs_centeredRow_le`, `entrance_le`, `sum_sq_centeredRow_le`, `centeredOperator_l2_le`.
- `FloorJumpsAboveTheSquareRootAreSparse` — `div_sub_div_succ_le_one`, `floorJump_injOn`,
  `sum_floorJump_le`.
- `TheChainIsHilbertSchmidtAboveInverseRootTwo` — `abs_centeredPrefix_le_rpow`,
  `abs_centeredPrefix_sub_le`, `abs_centeredRow_le_majorant`, `sq_centeredRow_le_majorant`,
  `sum_chainMajorant_le`, `centeredOperator_l2_le_of_inverseRootTwo`, `abs_centeredRow_le_jump`.
- `ShortIntervalSumsOfTheDampedDivisorCoefficients` — `centeredPrefix_sub_eq`, `fiber_card_le`,
  `sum_large_divisors_le`, `abs_moebiusTail_le`, `abs_centeredPrefix_sub_le_short`.
- `TheChainIsHilbertSchmidtAboveTheGoldenThreshold` — `abs_jump_le_belowSqrt`,
  `regionA_golden_sq_le`, `goldenExp_bounds`, `sum_belowSqrt_rpow_le`,
  `sq_centeredRow_le_goldenMajorant`, `centeredOperator_l2_le_of_goldenThreshold`.
- `TheColumnsOfTheChainInMellinCoordinates` — `centeredRow_eq_columnProfile`,
  `sum_sq_centeredRow_le_integral`, `sourceProfile_eq_tsum`, `mellin_fractSeries`,
  `integral_sq_div_sq_eq_mellin`, `mellin_columnProfile_eq`.
- `TheChainIsHilbertSchmidtAboveHalfDamping` — `sum_sum_sq_centeredRow_le_halfDamping`,
  `centeredOperator_l2_le_of_halfDamping`, `not_bounded_sum_sum_sq_centeredRow_of_le_half`.
- `TheSourceOnTheCriticalLineIsZetaOverZeta` — `tsum_sourceCoeff_cpow`, `mellin_sourceProfile_eq`,
  `exists_norm_mellin_sourceProfile_sq_le`.
- `TheChainIsBoundedAtHalfDamping` — `centeredOperator_apply_eq_combinedProfile`,
  `mellin_combinedProfile_eq`, `integral_norm_sq_dilationSymbol_shell_le`,
  `exists_centeredOperator_l2_le_uniform`, `exists_centeredOperator_l2_le_half`.
- `TwoTowersAddExactlyOnBoxes` — `uniformTrain_eq_zero_of_capacity_eq`, `grid_eq_zero_of_capacity_eq`,
  `joint_capacity_lt_iff_not_box`, `slanted_capacities_do_not_add`.
- `ResidueModesAndBackwardContinuation` — `centeredOperator_normalizedResidueMode`,
  `tsum_sq_normalizedResidueProfile_le/_ge`, `not_backward_stable_l2/_c0`, `summable_signBlind_iff`.
- `DampingIsStronglyContinuousWithUnboundedGenerator` — `tendsto_dampingFlow`,
  `tendsto_of_dense_of_bounded`, `one_le_norm_dampingFlow_sub_id`,
  `tendsto_generator_residueMode`, `not_exists_bounded_generator`.
- `TheSourceIsTheDampedMoebiusResidueSeries` — `centeredOperator_reciprocal_eq_tsum`,
  `admits_of_signBlind`, `not_summable_positiveTwin`.
- `ThePositiveTwinIsTheExtremalSignPattern` — `abs_residueSeries_le_abs_positiveTwin`,
  `sq_orbit_le_sq_positiveTwin`, `signBlind_admission_iff`.
- `TheFirstColumnOfTheChainIsTheReceiver` — `summable_dyadicDifference_iff`,
  `admits_iff_summable_firstColumn`, `riemannHypothesis_iff_firstColumn_summable`.
- `AdverseProfilesCannotVanish` — `tendsto_energy_splitting`, `adverse_weakLimit`,
  `eventually_energy_remainder_ge`, `eventually_energy_ge_weakLimit`,
  `adverse_escape_of_orthonormal`.
- `TheRestrictedWeilFormIsCompactlyNegative` — `tendsto_of_weakConvC`,
  `compactPerturbation_adverse_weakLimit`, `ccmRestrictedWeilForm_adverse_weakLimit`.
- `OnLineCompanionsPayOffLineDepth` — `companions_pay`, `few_companions_never_pay`,
  `companions_pay_up_to_error`.
- `SmoothSourcesPayAtTheTaylorPrice` — `taylorPoly_derivative_eval`, `abs_sub_taylorSum_le`,
  `companions_pay_up_to_taylor`, `abs_trigSourceDeriv_le`, `companions_pay_aperture`,
  `lagrangePrice_le_of_separated`, `companions_pay_aperture_explicit`.
- `TheRadialLossLaw` — `radialLoss_add_tangential`, `abs_log_energy_sub_le`.

## Open
Research topics 1–8 of the README §9 (arithmetic holonomy, allocation at growing size, nonlocal
payment of the frustrated part, the centred chain on `ℓ²`, residue-Gram cancellation, the companion
law for Paley–Wiener sources, compact negativity uniform in the aperture, trains not aligned with the
towers).

Gap (not a Lean statement): a uniform `ℓ²` bound for the centred chain `C_η` on finitely supported
sequences would admit `η`, via `tendsto_truncation_partialEnergy` and `admits_iff_summable_orbit`.
The chain is Hilbert–Schmidt exactly for `½ < η < 1` (`sum_sum_sq_centeredRow_le_halfDamping`,
`not_bounded_sum_sum_sq_centeredRow_of_le_half`) and bounded at `η = ½`
(`exists_centeredOperator_l2_le_half`); below half damping boundedness is unproved (RH-strength at
cofinally small `η`).
