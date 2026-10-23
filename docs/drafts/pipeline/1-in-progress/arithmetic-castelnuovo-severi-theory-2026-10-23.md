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
- `WittIntegralityIsNotPurity`: `zetaSeries_hasGhost` (ghost components = Lefschetz numbers),
  `eq_of_hasGhost`, `witt_integral_not_pure` (golden datum integral, impure),
  `pureDatum_pointCount_one_not_int` (pure, non-integral).
- `SpanContactLaw`: `toeplitz_pos_on_window_iff` (first degenerate window = number of eigenvalues).
- `HodgeIndexFromEffectivity`: `exists_effectivity_iff_hodgeIndex` (RR + ample axioms ⟺ Hodge index);
  `effectivity_iff` (all effectivities of nonnegative degree: open positive cone ⊆ E ⊆ positive
  half-space ∪ radical).
- `TheScalingSurface`: `scalingSurface_hodgeIndex_iff` (Hodge index of ℤ's scaling surface ⟺ RH),
  `posTestCone_not_riemannRoch`.
- `ArithmeticHodgeIndexSignatureLaw`: `posIndex_intersectionGram`, `riemannHypothesis_iff_one_positive_square`,
  `one_positive_square_iff_vonMangoldt`, `negIndex_weilGram_le_offLineCount` (Pontryagin bound).
- `FiniteConfigurationPontryaginLaw`: `exists_test_interpolating`; `pontryagin_law_finite` (finite
  configurations: max negative index = #distinct zeros right of the line).
- `TemperedConfigurationPontryaginLaw`: `summable_Wsummand`, `negIndex_zeroGram_le_of_tempered`,
  `pontryagin_law_of_tempered` (tempered configurations with finitely many right zeros: exact law,
  via dual tests and translated pairs); `weilGram_eq_zeroGram` for `ζ`.
- `TheHodgeDefectCountsTheRightZeros`: `pontryagin_law` (every tempered configuration: max negative
  index = #{Re ρ > ½} in ℕ∞, via density of zero-side coordinates in ℓ²);
  `zeta_hodgeDefect_iff`, `zeta_rightZeros_infinite_iff` (Hodge defect of ℤ's scaling surface =
  #zeros right of the line; unconditional); `periodic_pontryagin_dichotomy` (rank one: defect 0 or ∞).
- `InfiniteGenusLaw`: `riemannHypothesis_iff_weil_positive_definite`.
- `ResonatorKroneckerLaw`, `HeckeIncidenceCartesianLaw`: Kronecker/Cartesian law (no cross-prime prime
  coupling), additive Euler envelopes, `heckeIncidence_succ`.
- `TheResonatorRemainderIsNegative`: `resonatorRemainder_neg` (review topic 1 decided: the
  prime-side remainder is negative definite on resonators).
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
- **Status:** Lean, all modules compiled unconditionally; main theorems depend only on
  `propext, Classical.choice, Quot.sound`.

- `TheDegreeFiltrationOfTheHodgeDefect`: `iSup_hodgeDefectAt` (degree filtration exhausts the right
  zeros), `zeta_hodgeDefectAt_eq_zero` (nothing visible below degree 3/10).

- `TheReflectionSectorsOfTheHodgeDefect`: `sector_pontryagin_law` (even defect = #{Re>½, Im>0}, odd =
  #{Re>½, Im≥0}); `zeta_sector_hodgeDefect_iff` (each sector of ζ carries half).

- `TheKroneckerRankDichotomy`: `recurrent_pontryagin_dichotomy` (recurrent configurations: defect 0 or ∞).

- `ThePronicWeightIsThePoleMassOfTheSuccessorCell`: `integral_successorCell`, `successorCell_functionField`.

- `TheGoldenCurveIsABeurlingSystem`: `goldenDatum_beurling_not_pure` (rank-one Beurling system with
  positive integral prime counts, integral zeta, FE, violating purity).

- `TheFrobeniusSpanDefectCountsTheOuterEigenvalues`: `pontryagin_law_curve` (Pontryagin law over
  `𝔽_q`: span defect = #distinct `|β| > 1`, exact at window `≥ #{β}`),
  `unitary_iff_negIndex_spanGram_eq_zero`, `goldenDatum_negIndex_spanGram`.

- `TheScalingSurfaceOfACurve`: `curve_hodgeIndex_tfae` (RH ⟺ span Hodge index at window `2g` ⟺
  scaling-surface Hodge index for the zero configuration of a curve datum),
  `curveConfig_rightZeros_infinite_iff` (scaling defect `0` or `∞`).

- `TheVisibilityDegreeOfAnIsolatedPair`: `hodgeDefectAt_eq_zero_iff` (degree-`a` Hodge index =
  Weil positivity at aperture `a`), `hodgeDefectAt_isolatedPair` (exact degree law `0 → 1` at
  `sinh(2δa)/δ = 2L + 2a`), `exists_hidden_at_degree` (no finite degree certifies all
  configurations).

- `TheZerosOfAnExponentialPolynomialRecur`: `expPoly_zero_recurs`, `expPoly_pontryagin_dichotomy`
  (configurations cut out by exponential polynomials of any finite rank have defect `0` or `∞`).

- `DistinctEffectiveCyclesMeetNonnegatively`: `re_archCross_eq` (collar of two cycles in Lévy
  jump form), `localPair_eq_of_disjoint`, `localPair_nonneg` (Bézout positivity: distinct
  effective cycles meet nonnegatively; Riemann–Roch is the only missing input).

- `TheSuccessorCollar`: `collar_bounds`, `successor_localPair_bounds` (consecutive Hecke cycles
  meet through the collar alone, `ω(log(1 + 1/k)) = (k+1)√(k(k+1))/(2k+1)` per unit mass).

- `TheTwoThirdsConstantIsPairCorrelation`: `rtrace_spanGram`, `frobSq_spanGram_eq_diag_add_offDiag`
  (`𝔽_q` calibration of trace and Frobenius norm into adjunction diagonal + Lefschetz pair
  correlation), `parabola_secant_identity`, `offLine_sub_doubleZero_weight`,
  `paramDeficit_nonneg_and_eq_zero_iff` (`c = 2` is the unique rank–trace parameter matching
  off-line pair weight `c²` and double-zero weight `k_c(2)`), `blockA_coalescedPair_eq_doubleZero`
  (coalescence indistinguishability: a double critical zero and a coalescing off-line pair produce
  the identical Gram matrix `blockA`), `unitary_calibration_full_simple` (`κ = 1 ⟹ 100%` simple
  critical zeros), `fake_curve_frobSq_lower_bound`, `goldenDatum_rankTrace_barrier` (`s₁ = 0 ⟹ κ ≥ 2`),
  `rankTrace_tight_at_two_thirds`, `universal_matrix_functional_barrier`,
  `universal_matrix_functional_barrier_at_two_thirds` (no matrix functional `Φ(blockA, Ncount)`
  can certify more than `(2 − κ)N`, or `(2/3)N` at `κ = 4/3`), `subthreshold_two_thirds_deficit`,
  `subthreshold_cert_le_two_thirds`, `two_thirds_and_pair_correlation_escape`, `tendsto_certOpt_atTop`
  (`2/3` is the exact `λ = 1` pair-correlation threshold `2 − (1/λ + λ/3)`, and every finite
  pair-correlation bound `F ≤ B` beyond `1` yields `2/3 + 1/(3(3B − 2)) > 2/3`).

- `BreakingTheCoalescenceBlindSpotAndThreeQuarters`: `onSlack_of_posSemidef_eq`,
  `rank_trace_add_onSlack_of_posSemidef_eq_rank`, `onSlack_doubleZeroBlockData_eq` (exact on-line
  Parseval identity `onSlack(P, Q, c) = ‖P‖_F² − c tr P + (c²/4) rank P` for `Q ⪰ 0`, recovering
  `rank P` identically at `c = 2` and raising `doubleZeroBlockData s₁ d₂` from `s₁` to `s₁ + d₂ = (5/6)N > (3/4)N`),
  `negPart_credit_pos_iff_not_posSemidef` (`0 < 2 tr(Q₋) ↔ ¬ Q.PosSemidef`),
  `jointRankTrace23_at_four_thirds`, `three_quarters_of_broken_blind_spot_at_four_thirds`,
  `zeta_three_quarters_of_spectralSlack` (joint `(c = 2, c = 3)` functional `(14 tr Â − 3‖Â‖_F² − 7N)/4`
  equals `(3/4)N` at `κ = 4/3`, certifying `≥ 75%` critical-line zeros whenever `p ≤ d₂` or
  `zeroSideSlack ≥ (3/4 − H(λ))N(T, 2T)`), `kappa_five_fourths_iff_three_quarters`,
  `zeta_three_quarters_from_prime_surplus_and_double_window` (`κ ≤ 5/4 ⟺ 2 − κ ≥ 3/4`, unconditional
  bandwidth-`4/3` diagonal constant `43/36 = 5/4 − 1/18` and prime–pole cross bound `O(T^{5/6} log² T)`,
  and double-window minimum-aperture prime-pair bound `norm_doubleWindow_primeFreq_offDiag_le`).

- `RiemannRochForZAndTheReflectedPrimePolarLedger`: `PolarSurface.positiveCone_riemannRoch`,
  `PolarSurface.openPositiveCone_ample`, `PolarSurface.openPositiveCone_riemannRoch_iff_hodgeIndex`
  (duality of `positiveCone` and `openPositiveCone`: `openPositiveCone` satisfies `AmpleAxiom`
  unconditionally without assuming the sign of `W`, reducing `HodgeIndex` to `RiemannRochAxiom`),
  `strictCoupledArithmeticCone`, `strictCoupledArithmeticCone_ample`,
  `strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex`, `mem_strictCoupledArithmeticCone_odd_iff`,
  `weilPair_self_eq_fullZeroForm`, `two_mul_poleB_mul_poleA_eq_lorentz_moments`,
  `poleCharge_eq_two_mul_poleA_sq_of_odd`, `localPair_self_eq_neg_poleCharge_sub_fullZeroForm_of_odd`
  (`poleCharge F = 2 A(F)²` is the negative self-intersection of the polar projection `A(F)(H − V)` on
  `scalingSurface`), `scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger`,
  `scalingSubsurface_odd_defect_eq_chebyshevDefectLedger`,
  `scalingSubsurface_odd_primitive_self_eq_reflectedPrimePolarLedger`,
  `scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp`,
  `scalingSubsurface_odd_primitive_self_le_seventy_eight_mul_exp`,
  `exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp`,
  `exists_scalingSubsurface_odd_primitive_self_le_eight_add_eps_mul_exp` (unconditional all-aperture
  rate-`1/2` bound `δ(x, x) ≥ −78 e^r ∫ f²` and sharp PNT bound `δ(x, x) ≥ −((8 + ε) e^r + C) ∫ f²`),
  `scalingSubsurface_odd_defect_eq_criticalScalePrefixLedger` (second-order critical-scale receiver
  ledger), `zetaZeroWidth_le_of_scalingSubsurface_odd_defect_floor`,
  `rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor`,
  `rightZeros_zeta_eq_empty_iff_bddBelow_scalingSubsurface_odd_defect`,
  `rightZeros_zeta_eq_empty_of_subexponential_reflectedPrimePolarCost`,
  `rightZeros_zeta_eq_empty_of_subexponential_chebyshevTwoPoleDefect_integral` (graded zero-width
  law and self-improving bootstrap from subexponential/constant defect floors to exact `δ(x, x) ≥ 0`),
  `riemannHypothesis_iff_rightZeros_zeta_eq_empty`,
  `rightZeros_zeta_eq_empty_iff_forall_odd_strictCoupled_riemannRoch`,
  `rightZeros_zeta_eq_empty_iff_forall_odd_reflectedPrimePolarAllocation`,
  `rightZeros_zeta_eq_empty_iff_forall_odd_chebyshevDefectAllocation`,
  `rightZeros_zeta_eq_empty_iff_forall_odd_criticalScalePrefixAllocation`,
  `strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths` (unconditional
  `RiemannRochAxiom`, `AmpleAxiom`, and `BezoutAxiom` past the first prime `r ≤ 181/500`).

## Open: aperture of the Pontryagin law
The exact count is proved unconditionally (`pontryagin_law`, `zeta_hodgeDefect_iff`); the density
proof gives no aperture. Explicit apertures exist only for finitely many right zeros (translated
pairs).

## Open core
The scaling-surface Hodge index is RH-equivalent (`scalingSurface_hodgeIndex_iff`,
`riemannHypothesis_iff_exists_effectivity`). On `scalingSubsurface (oddRealTestsAt r)`,
`strictCoupledArithmeticCone` satisfies `AmpleAxiom` unconditionally at every degree `r > 0` without
assuming the sign of `W` (`strictCoupledArithmeticCone_ample`), and its `RiemannRochAxiom` is
unconditionally equivalent to the two-pole Chebyshev-defect allocation
`∫_{(0, 2r]} E(s) · 2 e^{-s/2} (A_f'(s) - ½ A_f(s)) ds ≤ surplusPool + crossingPotentialTerm + gaugeRemainder`
(`rightZeros_zeta_eq_empty_iff_forall_odd_chebyshevDefectAllocation`), proved unconditionally through
`r ≤ 181/500` past the first prime (`strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths`)
and bounded unconditionally across all `r > 0` at rate `σ = 1/2` (`δ(x, x) ≥ −78 e^r ∫ f²`,
`scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp`). Closing the gap from `−78 e^r ∫ f²`
to `0` across unbounded apertures `r → ∞` is the exact open core of the Riemann Hypothesis.
