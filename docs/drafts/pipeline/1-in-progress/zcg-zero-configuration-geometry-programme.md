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

## Open core
The route to RH is on its own card (`zcg-rh-route.md`). It runs from archimedean domination of the
heat flow above `2π e^{(2/3+ε)/t}`, through a collision-free descent, to `ζ`. Open: O1 domination
below the mean spacing; O2 the local camera at height `X` (programme-internal, next target); O3
reality of the coalescent near-collisions in the last stretch. Internal open tools: the depth range
of the Ingham scale between `π/(2a)` and `π/a`, and the Beurling–Malliavin radius.

## Log
- 2026-11-04 — created; forty pillar modules checked; README written.
