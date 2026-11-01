# Renormalized intersection theory of the scaling surface (programme)

- **ID:** rit-programme
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — programme of pillar theorems
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.6
- **Statement:** The renormalized intersection pairing of scaling correspondences on the scaling surface: product-formula gluing of local poles, renormalized Hodge index on the pole-orthogonal hyperplane, Castelnuovo–Severi, Künneth square, selection by the glued index.

## Goal
Answer the questions of §2.6 with unconditional theorems (equivalences, classifications, no-gos).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/RenormalizedIntersectionTheory` (umbrella `RenormalizedIntersectionTheory.lean`)

## Lean declarations
- Gluing: `negIndex_sumPole`, `negIndex_tensorPole`, `negIndex_weightPairs`, `negIndex_extremalPair`,
  `archBoost_sUnit_eq_weightChar_empty`, `archPole_sUnit_eq_extremalPair`, `exists_cpow_weightChar_iff`.
- Infinite product: `infTensorPole_sUnit`, `negIndex_infTensorPole_eq_top`, `infTensorPole_sUnit_eq_arch_add`.
- Density: `irrational_log_div_log`, `dense_exponents_pair`, `not_dense_exponents_single`.
- Hodge index: `renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one`, `boostPolarIndex_ratCorr`,
  `riemannHypothesis_iff_renormalizedHodgeIndex`, `riemannHypothesis_iff_hyperplane_nonneg`,
  `eventually_completeWeil_floor_on_poleHyperplane`, `boostMassU_integerSlopes_eq_inner`.
- Künneth: `negIndex_tensorKernel_le`, `hermIndex_kronecker_le_negIndex_tensor`,
  `negIndex_tensorKernel_self_eq_zero_or_top`, `riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero`,
  `kunnethZeta_eq_tsum`, `zetaKernel_sq_eq_tsum`.
- Castelnuovo–Severi: `riemannHypothesis_of_norm_zetaKernel_le`, `riemannHypothesis_iff_castelnuovoSeveri`.
- Selection: `gluedTestIndex_vonMangoldt`, `gluedTestIndex_finiteFlip_eq_top`,
  `riemannHypothesis_iff_gluedTestIndex_eq_one`; atomic Hodge index:
  `hodgeSeparates_iff_not_hasHyperplaneGap`, `hodgeSeparates_liouville`,
  `hodgeSeparates_of_harmonicSum_small`, `hodgeSeparates_primeFlip_iff`, `not_hodgeSeparates_of_correlation`,
  `hodgeSeparates_primeSetFlip_iff`, `hodgeSeparates_cofiniteFlip`, `hodgeSeparatesFrom_iff`,
  `hodgeSeparates_or_probe_primeSetFlip`, `hodgeSeparates_liouville_mul_primeSetFlip`.
- Hadamard powers: `isPosDefKernel_mul`, `isPosDefKernel_pow`,
  `riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow`, `negIndex_zetaKernel_le_negIndex_kunnethZeta`,
  `lindelof_of_negIndex_kunnethZeta_lt_top`, `quasiRH_of_negIndex_kunnethZeta_lt_top`,
  `negIndex_zetaKernel_le_posIndex`, `sq_negIndex_zetaKernel_le_negIndex_kunnethZeta`.
- Positive squares: `criticalSeen_infinite`, `posIndex_orbitKernel_onLine_eq_top`,
  `posIndex_zetaKernel_eq_top_of_finite`, `riemannHypothesis_or_negIndex_kunnethZeta_eq_top`.
- Growing overlap: `eventually_completeWeil_hodgeIndex_iteratedLog`,
  `riemannHypothesis_iff_completeWeil_hodgeIndex_log`, `riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log`,
  `eventually_completeWeil_hodgeIndex_packet_root`, `exists_growing_packet_hodgeIndex_root`,
  `poleHyperplane_markov_nonneg_iff_hodgeIndex`, `eigenvalues_nonneg_or_of_nonneg_on_orthogonal`.
- Heat flow: `boostPolarIndex_heatDilationKernel`, `boostPolarIndex_heat_eq_sum_collisionPairs`,
  `antitoneOn_boostPolarIndex_heat`, `exists_left_boostPolarIndex_heat_eq_add_collisionPairs`,
  `riemannHypothesis_iff_forall_renormalizedHodgeIndex_heat`, `boostPolarIndex_ratCorr_lt_top_iff_bdd_heat`.
- Riemann–Roch: `renormalizedHodgeIndex_ratCorr_iff_scalingSurface_hodgeIndex`,
  `renormalizedHodgeIndex_ratCorr_iff_exists_serreDual_h0`.
- Loop Eisenstein: `boostPolarIndex_ratCorr_eq_encard_reflectionPoles`,
  `riemannHypothesis_iff_reflectionPoles_eq_empty`.
- Density: `not_dense_exponents_of_quantized` (commensurable place sizes, `𝔽_q[T]`).
- Wirsing for twins: `exists_abs_wirsing_equation_le`, `exists_abs_gaugeHarmonicSum_le_rpow`,
  `exists_abs_gaugeHarmonicSum_sub_rpow_le`, `exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le`,
  `hodgeSeparates_primeSetFlip_of_primeSetLogMass`, `hodgeSeparates_residueClassFlip`,
  `hodgeSeparates_primeSetFlip_one_mod_four`, `hodgeSeparates_primeSetFlip_three_mod_four`.
- Conductor series: `hodgeSeparates_primeSetFlip_of_packet`, `hodgeSeparates_primeSetFlip_iff_secular_pos`,
  `exists_packet_gt_of_lowerLogDensity`, `hodgeSeparates_primeSetFlip_of_lowerLogDensity`,
  `hodgeSeparates_residueClassFlip_of_totient_le_four`, `hodgeSeparates_primeSetFlip_one_mod_five`.
- Spectral weight at precision `c_N²`: `eventually_inner_sq_le_conductorSeries`,
  `primeSetFlip_hasHyperplaneGap_of_conductorSeries`, `hodgeSeparates_primeSetFlip_iff_packet`,
  `exists_abs_gaugeHarmonicSum_roughGauge_le`, `exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip`,
  `eventually_fixedScaleDefect_le`, `exists_abs_inner_twin_sub_starProjection_le`,
  `eventually_excitedResolvent_finiteFlip_le`.
- Resolvent asymptotic: `eventually_packet_le_excitedResolvent`,
  `eventually_abs_excitedResolvent_div_sub_conductorSeries_le`, `summable_conductorSeries`,
  `eventually_inner_sq_le_tsum_conductorSeries`, `hodgeSeparates_primeSetFlip_iff_conductorSeries`.
- Power-regular densities: `exists_abs_gaugeHarmonicSum_sub_rpow_le_rpow`,
  `exists_abs_sub_rpow_le_of_wirsing_rpow`, `not_le_rpow_gaugeHarmonicSum`,
  `exists_primeSum_rpow_ge_rpow`, `le_of_sharp_wirsing`, `defect_error_le`.

## Open
Hodge index on schedules between `(log log N)^{<1/16}` (proved) and `(log N)^{α}`, every `α > 0` (= RH); positive index of `K_ζ` on the infinite stratum;
infinite flip sets of maximal margin (invisible to the atomic Hodge index, not finite flips);
prime-set twins whose relative logarithmic density is regular only to `o(log n)` without a power saving below `1 − 2κ` (with such a saving, separation is exactly `W_P(s) > 1/s`); which side the unit class mod `7` without `2` falls on.

## Log
- 2026-10-31 — created; formalized pillars listed above
