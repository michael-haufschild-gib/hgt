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
  `riemannHypothesis_iff_gluedTestIndex_eq_one`.

## Open
Positive index of `K_ζ` (all-or-nothing Künneth square for ζ); Hadamard-power index laws; hyperplane
positivity at growing overlap; heat flow as a homotopy of glued states; Liouville-type twins.

## Log
- 2026-10-31 — created; formalized pillars listed above
