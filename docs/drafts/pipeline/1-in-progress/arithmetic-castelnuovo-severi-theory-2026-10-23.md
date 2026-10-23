# Arithmetic Castelnuovo–Severi Theory (ACS): programme card

- **ID:** acs-2026-10-23
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/review-2210/fable.md §4.3 (the opening), §5 (the field)
- **Statement:** Develop the intersection theory of the scaling surface of ℤ in which the cycles are
  Weil tests, the pairing is the explicit formula, the pole plane `e^{±u/2}` is the hyperbolic plane
  `⟨H, V⟩`, the Frobenius graphs are the scaling (Hecke) graphs, and the Hodge index theorem is Weil
  positivity. Lean in `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/`, umbrella
  `GaloisForLFunctions.ArithmeticCastelnuovoSeveri` (registered in `MainTheorems.lean`).

## Goal
Make each ingredient of Weil's proof an exact object with a theorem, calibrated over `F_q`, and
decide each research topic of review §5.9 by a theorem (positive, or a no-go with its positive
survivor).

## Gates
- [x] 0 → 1 folder, umbrella, registration, modules compiled with `lake --old env lean`
- [x] README written (`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md`)
- [x] topics of §5.9 each addressed by a Lean theorem or recorded as an open problem in the README

## Plan (modules)
1. Abstract Castelnuovo–Severi algebra: hyperbolic plane, Hodge index ⇔ CS ⇔ defect PSD; Weil's
   discriminant step; adjunction threshold law; graded adjunction.
2. Frobenius-span calibration: CS defect of `Σ d_k Γ̃_k` = Toeplitz power-sum form; Hodge index on
   the span ⇔ RH of the curve datum.
3. Fake curves: span data (point counts, FE) without Hodge index; finite-window hiding.
4. Arithmetic intersection form for ζ: Weil form = CS defect; signature law
   `posIndex = 1 + negIndex(W)` (Haynsworth); RH ⇔ one positive square.
5. Pontryagin index of zero configurations.
6. Adjunction conjecture of §4.3: mean-field obstruction and survivor.
7. Section count: Hodge index from Riemann–Roch skeleton; arithmetic effectivity candidates.
8. Kronecker rank, Witt integrality, metrology integration.

## Outcomes
- `PolarSurfaceHodgeIndex`: `hodgeIndex_tfae`, `defect_sq_le_of_hodgeIndex`, `hodgeIndex_iff_no_positive_plane`.
- `AdjunctionThresholdLaw`: `realizable_iff` (classification), `realizable_adjunction_iff` (Hasse–Weil),
  `realizable_of_free_selfIntersection` (without `Γ²` no bound), `sq_le_of_realizable_of_selfIntersection_ge`.
- `FrobeniusSpanCalibration`, `FrobeniusSpanHodgeIndexIsRH`: span defect = Toeplitz power-sum form
  (`spanDefect_eq_toeplitz`); `hodgeIndexOnSpan_iff_unitary`.
- `FakeCurvesAndTheWindowLaw`: golden fake curve over `𝔽₅` violates Hodge index with integral point
  counts; `two_mul_genus_ge_of_window`, `exists_hidden_on_window` (calibrated finite-window wall).
- `SpanContactLaw`: `toeplitz_pos_on_window_iff` (first degenerate window = number of eigenvalues).
- `HodgeIndexFromEffectivity`: `exists_effectivity_iff_hodgeIndex` (RR + ample axioms ⟺ Hodge index).
- `TheScalingSurface`: `scalingSurface_hodgeIndex_iff` (Hodge index of ℤ's scaling surface ⟺ RH),
  `posTestCone_not_riemannRoch`.
- `ArithmeticHodgeIndexSignatureLaw`: `posIndex_intersectionGram`, `riemannHypothesis_iff_one_positive_square`,
  `one_positive_square_iff_vonMangoldt`, `negIndex_weilGram_le_offLineCount` (Pontryagin bound).
- `InfiniteGenusLaw`: `riemannHypothesis_iff_weil_positive_definite`.
- `ResonatorKroneckerLaw`, `HeckeIncidenceCartesianLaw`: Kronecker/Cartesian law (no cross-prime prime
  coupling), additive Euler envelopes, `heckeIncidence_succ`.
- `TheAdjunctionConjectureMeanField`: `not_exists_polynomial_adjunction_bound` — the review's §4.3
  adjunction conjecture is false in its quantitative form (mean field `S² ≍ N`); survivor: Cartesian law.

## No-go closure (adjunction conjecture of review §4.3)
- **Exact killing theorem:** `not_exists_polynomial_adjunction_bound`.
- **Strongest positive survivor:** the Cartesian law (`heckeIncidence_eq_towerWeight`,
  `heckeIncidence_eq_zero`): the true prime self-intersection of lattice cycles has no cross-prime
  terms; the aggregate is a Cauchy–Schwarz shadow of mean-field size.
- **New insight:** the adjunction formula is present (lag-zero Lefschetz / archimedean term); the
  missing ingredient is the Hodge index, i.e. an effectivity with the Riemann–Roch axiom
  (`riemannHypothesis_iff_exists_effectivity`).
- **Status:** Lean, all modules compiled unconditionally.
