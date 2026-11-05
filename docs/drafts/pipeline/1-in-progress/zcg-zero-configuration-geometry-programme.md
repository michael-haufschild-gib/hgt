# Zero Configuration Geometry (ZCG) programme

- **ID:** zcg
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0311/fable-zero-configuration-geometry.md
- **Statement:** The explicit formula as a camera: identification, mimicry, deformation and selectivity of
  zero configurations, without positivity, spectra, counts or Hodge index as the decisive step.

## Goal
Develop the field of the brief: answer Q1–Q6 where tools can be built, formalize the pillars in
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/`, write the foundational README.

## Gates
- [x] 0 → 1  in-progress
- [ ] 2 → 3  formalized: all pillar modules checked with `lake --old env lean`, umbrella wired

## Approach
Pillars (module — main theorems), all checked with `lake --old env lean`, umbrella
`ZeroConfigurationGeometry.lean` wired into `MainTheorems.lean`:
- TheCameraAndTheTilt — `paperFT_gammaOf`, `Gsummand_eq_tilted`, `paperFT_add_add_sub`, `depthSignal_eq`,
  `norm_depthSignal_le`, `exists_depthSignal_ge`
- TheSquaredGapIsReadAtSecondOrder — `norm_pairSignal_add_sq_mul_secondMoment_le`,
  `norm_realPair_sub_tiltedPair_le`, `deriv_deriv_paperFT_eq_neg_secondMoment`
- FiniteModificationsAreSeenAtEveryAperture — `eq_of_weil_eq_on_aperture_of_finite`,
  `infinite_modification_of_mimic`, `zeta_finite_modification_seen`
- DifferentialWindowsInvertTheCamera — `paperFT_annihilate`, `exists_annihilating_window`,
  `exists_window_sum_eq_coeff_mul_gaps`, `exists_windows_W_sub_W_eq`
- TheInverseWindowsAreStable — `exists_annihilating_window_bound`, `norm_multDiff_mul_gaps_le`,
  `multDiff_eq_zero_of_precision`, `norm_multDiff_mul_gaps_le_at_height`
- TheArithmeticPinningIsStable — `norm_weilFullFunctional_sub_le`,
  `norm_multDiff_mul_gaps_le_of_arithmetic`, `multDiff_eq_zero_of_arithmetic_precision`
- TheHeightCurvatureOfThePrimeChannel — `weilTest_modulate`, `primeChannel_modulate`,
  `deriv_deriv_primeChannel_modulate`
- HidingNeedsNearCollisions — `exists_near_pair_of_onLine_mimic`
- TiltedInghamInequality — `tiltedKernel_eq`, `norm_tiltedKernel_le`, `tilted_ingham_inequality`,
  `pairGap_pos`, `block_ingham_inequality`, `eq_zero_of_pairSum_eq_zero`
- ThePrimesPinEveryFinitePieceOfZeta — `arithmeticImage_congr_of_eq_below`,
  `eq_zeta_of_arithmeticImage_of_finite`
- IdentificationIsCheaperThanSign — `spectrum_eq_of_powerSum_eq`, `spectrum_eq_of_weil_eq_on_aperture`,
  `curveConfig_weil_eq_iff_trace_eq`, `identification_threshold_sharp`, `pure_iff_of_weil_eq_on_aperture`
- RamanujanIsRealityOfAnEulerColumn — `localFactor_zero_depth`, `localFactor_zero_re_eq_half_iff`,
  `norm_eq_one_iff_tracePoint`, `localFactor_eulerColumnCoeff_eq_zero_iff`,
  `eulerColumn_mimics_onLineLattice`, `no_bounded_aperture_excludes_eulerColumns`
- EulerColumnsAreSeenJustAboveTheirPrime — `offLineLattice_separated_above_nyquist`,
  `offLineLattice_mimic_iff`, `eulerColumn_mimic_iff`
- TheSquareRootThresholdIdentifiesColumns — `rvmLattice_mimic_iff`
- HeatTimeSpreadsTheConfiguration — `coeff_heatFlow_sub_two`, `sum_sq_roots_heatFlow`,
  `spread_roots_heatFlow`, `exists_nonreal_root_heatFlow`
- LaguerreStepsNeverDeepenTheConfiguration — `rootsInStrip_add_smul_derivative`, `rootsInStrip_heatStep`,
  `heatStep_keeps_triple_edge_root`
- ShiftAveragesContractTheDepth — `pairFactor_lt`, `im_eq_zero_or_sq_add_sq_le_of_shiftAverage`,
  `im_eq_zero_of_shiftAverage`, `roots_shiftAvgList_im_sq_le`
- RealityLeavesOnlyThroughCollision — `eventually_splits_of_simple`, `isClosed_splits`,
  `exists_first_collision`
- WindowsBlindToALattice — `paperFT_shift`, `exists_window_blind_to_lattice`
- ShallowPairsAreNearCollisions — `eq_of_weil_eq_of_pairSeparated`, `pairGap_ge`, `tiltB_le`,
  `exists_near_pair_or_shallow_pair_of_mimic`, `pairWeight_modScaledBump_eq_sq`,
  `not_inDarkSector_of_bright`, `exists_near_pair_or_dim_shallow_pair_of_mimic`
- PerturbedLatticeProducts — `summable_norm_pertFactor_sub_one`, `norm_sin_mul_prod_pertFactor_le`
- BlindWindowsForPerturbedLattices — `exists_blind_limit_window`, `exists_window_blind_to_perturbed_lattice`,
  `exists_window_blind_to_perturbed_lattices`
- PaleyWienerWindows — `exists_smooth_source_of_entire`, `exists_window_of_entire`, `blind_windows_iff_entire`
- BlindWindowsAtTheUniformDensity — `exists_injective_near_int`, `exists_window_blind_of_count_le`,
  `exists_window_blind_of_density_le`, `exists_window_blind_of_separated`
- ShallowConfigurationsAreResolvedAtTheInghamScale — `remainder_upper`, `inghamConst_mul_normSq_le`,
  `eq_of_weil_eq_of_shallow`, `exists_depth_resolving_at_ingham_scale`,
  `not_exists_depth_resolving_at_ingham_threshold`
- SparseClustersNeverCancel — `exists_window_blind_of_injOn_near_complex_lattice`, `eq_of_mimic_of_count_le`
- SparseOnLineClustersNeverCancel — `eq_of_mimic_of_onLine_count_le`, `exists_onLine_mimic_at_density`
- IsolatingWindows — `exists_window_div`, `exists_isolating_window`,
  `exists_window_isolating_lattice_point`
- ResolutionIsUniformInDepth — `uniform_block_inequality`, `eq_of_weil_eq_of_heightSeparated`,
  `exists_near_pair_of_mimic`, `exists_near_pair_of_mimic_of_le`
- HeatStepsNeverShrinkTheMesh — `meshGe_add_smul_derivative`, `nodup_roots_add_smul_derivative`,
  `meshGe_heatStep`, `iterate_heatStep`
- BlindWindowsAtTheDensityAperture — `apertureWindow_expPoly`, `exists_window_blind_to_expPoly_zeros`,
  `exists_window_blind_to_lattices`, `exists_window_blind_to_lattice_iff`,
  `exists_window_blind_to_densityTransform_zeros`
- TheCosineCameraHasOnlyRealKernelZeros — `cosineWindowTransform_closed_form`,
  `im_eq_zero_of_cosineWindowTransform_eq_zero`, `no_complex_additive_zero_triple`
- ProductsOverPerturbedLatticesOnTheStrip — `norm_sin_mul_prod_pertFactor_le_strip`,
  `isoConst_le_norm_pertFactor`, `norm_prod_pertFactor_ge_strip`
- FarZerosAreFaintInTheLocalCamera — `paperFT_localWindow`, `norm_tsum_far_le`, `tsum_far_multDiff_le`,
  `tsum_far_zeta_le`
- IsolatedPointsAreSeenByTheLocalCamera — `exists_bump_one_le_norm_paperFT_I_mul`,
  `exists_uniform_isolating_window`, `one_add_pow_le_of_isolated_cancellation`
- ZetaZerosHaveTheSharpLocalDensity — `ncount_le_of_goodHeight`, `exists_card_le_sharp_centred`
- TheLocalCameraConstantIsQuasiPolynomial, TheLocalCameraFixesTheIsolatedZerosOfZeta —
  `log_inv_windowFloor_le_of_le_one`, `multDiff_zeta_eq_zero_of_nearly_isolated`,
  `exists_near_coincidence_of_zeta_mimic`
- SplineBumpsDecayAtAnExplicitRate, ShallowConfigurationsAreResolvedLocally —
  `exists_explicit_bump`, `eq_of_locally_shallow_at_ingham_scale`
- DeepColumnsHideOnlyBelowTheInghamScale — `W_shiftedLatticeConfig_lagFormula`, `deepColumn_mimic_iff`
- NearCoincidencesAreReadThroughTheirMoments, IsolatingWindowsVarySlowlyAtTheirTarget —
  `norm_discMoment_le`, `core_window_slow`, `norm_discMoment_rvm_le`, `pair_centre_and_gap_rvm`,
  `dipole_collapse_rvm` (B51 uniformly in height)
- TheImageHankelReadsTheSquaredGap — `pair_hankel_rvm`, `pair_type_of_hankel` (B44 in image form)
- TheImageReadsTheDiscriminantOfACluster, TheImageLocatesTheClusterPoints — `cluster_discriminant_rvm`,
  `cluster_location_rvm`
- ConfigurationsOfOneDepthAreResolvedAtTheInghamScale — `tsum_averaged_lag_eq_zero`, `eq_of_mimic_of_oneDepth`
- MixedDepthsHideBeyondTheInghamScale — `mixedDepth_mimics_beyond_ingham`, `not_eq_of_mimic_at_ingham_scale`
- SymmetricHalvesArePhaseLattices, FiniteCarriersAreRealAboveTheirHorizon, TiltsCostPrimeWeight —
  `ncard_sym_zeros`, `carrier_ne_zero_near_line`, `eulerDepth_ne_zero_near_line`,
  `twin_tilt_costs_weight`, `exists_twin_tilt_beyond_every_weight`

## Open core
The route to RH is on its own card (`zcg-rh-route.md`). Steps 1–5 of the heat descent are proved
([L], [P]); the camera fixes the configuration of `ζ` outside near-coincidence clusters and is
killed as a producer. Open: (a) reality inside near-coincidence clusters below `X^{−M}` (B44),
(b) a Hermite–Biehler half of the heat source below `½/log X` (B49), both cancellation statements for
the Euler product inside the strip. B51 is proved uniformly in height. Depth thresholds: one depth
is resolved at the Ingham scale (`eq_of_mimic_of_oneDepth`), and mixed depths hide up to `2π/(3g)`
(`not_eq_of_mimic_at_ingham_scale`). Internal open question: the sharp mixed-depth threshold in
`[2π/(3g), π/g]`.

## Log
- 2026-11-04 — created; forty pillar modules checked; README written.
