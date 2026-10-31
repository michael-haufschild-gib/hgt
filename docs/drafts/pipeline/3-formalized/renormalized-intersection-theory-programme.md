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
  `hodgeSeparates_or_probe_primeSetFlip`.
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

## Open
Hodge index on schedules between `(log log N)^{<1/16}` (proved) and `(log N)^{α}`, every `α > 0` (= RH); positive index of `K_ζ` on the infinite stratum;
infinite flip sets of maximal margin (invisible to the atomic Hodge index, not finite flips).

## Log
- 2026-10-31 — created; formalized pillars listed above
