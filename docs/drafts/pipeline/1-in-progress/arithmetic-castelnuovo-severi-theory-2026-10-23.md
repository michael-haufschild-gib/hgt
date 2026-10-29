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

- `CoalescenceDoesNotRequireOrthogonality`: `blockA_coalescedPairFrame_eq_doubleZeroFrame`,
  `counts_doubleZeroFrameData`, `counts_coalescedPairFrameData` (full Gram equality and equal
  total multiplicity, with different fixed-label counts, on arbitrary real families),
  `nonorthogonal_coalescence_example` (unit vectors with inner product `3/5`, trace `4`,
  Frobenius square `232/25`). The orthogonal coordinate examples establish abstract sharpness,
  not arithmetic realizability. See [scope audit](../3-formalized/rank-trace-orthogonality-scope-audit.md).

- `TheTwoThirdsConstantIsPairCorrelation`: `rtrace_spanGram`, `frobSq_spanGram_eq_diag_add_offDiag`
  (`𝔽_q` calibration of trace and Frobenius norm into adjunction diagonal + Lefschetz pair
  correlation), `parabola_secant_identity`, `offLine_sub_doubleZero_weight`,
  `paramDeficit_nonneg_and_eq_zero_iff` (`c = 2` is the unique rank–trace parameter matching
  off-line pair weight `c²` and double-zero weight `k_c(2)`), `blockA_coalescedPair_eq_doubleZero`
  (abstract coalescence indistinguishability: a double fixed label and a reflected pair sharing a
  real vector produce identical `blockA`), `unitary_calibration_full_simple` (coordinate model
  with `N` simple fixed labels has `κ = 1`), `fake_curve_frobSq_lower_bound`,
  `goldenDatum_rankTrace_barrier` (`s₁ = 0 ⟹ κ ≥ 2`),
  `rankTrace_tight_at_two_thirds`, `universal_matrix_functional_barrier`,
  `universal_matrix_functional_barrier_at_two_thirds` (a bound valid on **all** normalized abstract
  blocks cannot exceed `(2 − κ)N` at the coordinate extremizer, or `(2/3)N` at its `κ = 4/3`
  specialization; these results supply no arithmetic-realization theorem transferring sharpness to zeta),
  `subthreshold_two_thirds_deficit`,
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

- `SpectralSlackConservationAndTheHyperbolicDisplacementThreshold`: `totalSlack`, `couplingDefect`,
  `couplingDefect_nonneg`, `rank_trace_add_totalSlack_eq`, `zeroside_rank_core_slack_exact`,
  `zeroside_rank_core_slack_le_rank` (exact spectral-slack conservation law: adding `totalSlack(P, Q, 2)`
  cancels the prime-side quadratic functional `4 tr Â − ‖Â‖_F²` identically, leaving
  `rank P − 2(N − tr P − 2 n₊(Q)) − Δ₂(P, Q) ≤ rank P`), `rank_hatP_le_d`, `seamA_spectralSlack_le_d`,
  `thmA_abstract_err_spectralSlack_le_d`, `zeroSideSlack_eventually_le_lam_sub_Hfun`,
  `not_three_quarters_zeroSideSlack_of_lt_three_quarters` (unconditional grid-dimension ceiling
  `rank P̂(T) ≤ d(T) ≤ λ N(T, 2T) + o(N)`, forcing `zeroSideSlack(λ, T) ≤ (λ − H(λ) + ε)N(T, 2T)` and
  refuting `zeroSideSlack ≥ (3/4 − H(λ))N` for every `λ ∈ (0, 3/4)`), `posSlack_mul_ge_sq_of_rtrace`,
  `offLine_slack_ge_of_rtrace_hermNegPart` (universal Cauchy–Schwarz bound `posSlack(Q, 2) ≥ 4η²b` and
  total off-line slack `2 tr(Q₋) + posSlack(Q, 2) ≥ 4bη(1 + η)`), `displacedPairBlockData`,
  `blockA_displacedPairBlockData`, `blockQ_one_displacedPairBlockData`,
  `negPart_credit_pos_displacedPairQDiag`, `displacedPairBlockData_below_three_quarters`,
  `macroscopic_displacedPair_counterexample_at_four_thirds`,
  `hyperbolic_displacedPair_three_thresholds_at_four_thirds` (hyperbolic displaced-pair block calculus
  with `α² − β² = 1`: strictly positive negative-part credit `2 tr(Q₋) = 4pη > 0` does not suffice for
  `75%` at `κ = 4/3`, refuted unconditionally by `(s₁ = 179, p = 32, α = √(17/16), β = 1/4, N = 243)`,
  along with the three exact thresholds `(1 + 2η)² ≥ 4/3`, `η ≥ 1/6`, and `(1 + 2η)² ≥ 2`).

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

- `TheHodgeDefectIsCyclic`: `cyclic_pontryagin_law` (one Hecke orbit of a spectrally generic test
  carries the whole Hodge defect), `riemannHypothesis_iff_ratHecke_negIndex_eq_zero`,
  `riemannHypothesis_iff_twoPrime_negIndex_eq_zero`.

- `TheHeckeTowerOfAPrimeIsThePeriodQuotient`: `tower_pontryagin_law` (a single prime tower counts the
  outer Frobenius eigenvalues `p^{ρ−½}` of nonzero weight), `negIndex_towerGram_le`.

- `AlmostEveryPrimeSeesEveryRightZero`, `TheTowerDefectCountsTheFrobeniusEigenvalues`: finitely many
  right zeros ⟹ all but finitely many prime towers carry the whole defect; one test whose tower at
  every prime has defect = #distinct `p^{ρ−½}`.

- `TheFrobeniusSpanIsTheTowerOfTheScalingSurface`: `W_curveConfig` (explicit formula of a curve),
  `curve_towerGram_eq_smul_spanGram`.

- `TheDegreeFiltrationOfACurveIsItsWindowFiltration`: `hodgeDefectAt_curveConfig` (degree-`a` defect
  of a curve is `0` or `∞` by the window `⌈2a/log q⌉`).

- `OnePrimeSeesEveryWellFoundedLevel`: `tower_pontryagin_law_of_wellFounded` (one prime tower counts
  all visible eigenvalues when real parts have no increasing sequence), `almost_every_prime_sees_the_top`.
  Open: real parts increasing to their sup (two-sided Wolff annihilators?).

- `TheFirstNegativeLagOfACurve`: lag tests read point counts; purity ⟺ lag positivity; Turán-located
  first negative lag (calibration of SRT `zeta_attained_top_first_negative_lag`).

- `TheGenusIsTheApertureOfTheRadical`: `exists_radical_test_iff` (curve radical = P(T_q)(tests), opens at
  aperture d log q/2; calibration of `InfiniteGenusLaw`).

- `NumericalEquivalenceOnACurveIsTheFrobeniusIdeal`: `radical_iff_eq_frobPolyTest` (radical = P(T_q)·tests).

- `TheHodgeDefectOfZetaIsFiniteAtEveryDegree`: `hodgeDefectAt_zeta_le` (ζ's degree defect is finite,
  doubly exponential bound; curves and lag lattices are 0 or ∞ per degree).
- `TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies`: `re_W_zeta_nonneg_of_lowGrid` (Weil positivity at
  every aperture on tests blind to an explicit low-frequency grid); golden curve: no finite divisor works.
- `TheNearRadicalOfZetaIsFiniteDimensional`: `zeta_near_radical_finrank_le` (near radical finite-dim,
  doubly exponential upper half of Landau–Widom); `curve_radical_finrank_ge` (curve radical infinite-dim).
- `SourceRiemannRochAwayFromTheLowFrequencyDivisor`: `lowBlindTests_effectivity` (L² source cone is an
  effectivity with RR, ampleness, Hodge index on the low-frequency-blind subsurface at every degree).

## Open: aperture of the Pontryagin law
The exact count is proved unconditionally (`pontryagin_law`, `zeta_hodgeDefect_iff`); the density
proof gives no aperture. Explicit apertures exist only for finitely many right zeros (translated
pairs).

## Open core
Homogeneous coarse recovery is now formalized:
`Γ(g)+Γ(h)≤CΓ(g+h)` uniformly in all complete-pair horizons, with no additive
coarse-mass error. The paid even-power plus odd-detail form retains a positive
multiple of `Γ(g)+Σ log(1/w_a)M_a d_a²` after a fixed detail head.
See [paper proof and Lean validation](../3-formalized/acs-homogeneous-gamma-coarse-recovery.md).
The actual Gamma coupling `B=Γ(g+h)-Γ(g)-Γ(h)` also satisfies
`B²≤128 exp(1/2) Γ(g)∫h²`. For every `ε>0`, one fixed detail cutoff gives
`|B(q,d,X)-B(q,d_head,X)|≤εΓ(g+h)` for every horizon and all signed coefficients.
See [lower-order coupling and uniform finite heads](../3-formalized/acs-gamma-mixed-block-lower-order.md).
The square mixed block now has a uniform physical tail bound:
`|B₂(q,d_tail,X)|≤εΓ(completePairProfile q d X)` for one fixed detail cutoff
and every q,d,X. The controlling source is the original untruncated profile.
The proof combines the sublogarithmic ζ′/ζ bound on Re s=1 with a centred
low-frequency Gamma floor, exact mean and mass corrections, and BV smoothing.
See [the mixed-square card](../3-formalized/acs-square-mixed-source-lower-order.md).
The full Haar Weil diagonal can consequently be paid together with Gamma
coupling and every mixed prime exponent at least two. Writing
`Q=Γ(g+h)-Γ(h)+W(h)` and `D=Σ log(1/w_a)M_a d_a²`, one fixed detail head gives
`Q-B₂-Bodd≥(1-ε)Γ(g)+(1-1/sqrt(2))D/4+∫h²` for every ε>0.
This literal subform has uniformly bounded negative dimension at every horizon.
Its diagonal includes first primes, archimedean mass and the actual Haar pole
product. Even powers and odd powers at least three occur once each.
See [joint payment and Lean check](../3-formalized/acs-joint-nonfirst-mixed-payment.md).
The [full-pole extension](../3-formalized/acs-full-polar-nonfirst-payment.md)
replaces the Haar pole by the actual complete-profile pole P(F). For
`R=Q−B₂−Bodd−P(h)+P(F)`, one fixed detail head gives
`R+2 sinhHalfMoment(F)² ≥ (1−ε)Γ(g)+(κ/8)D+∫h²+2 coshHalfMoment(F)²`.
The complete polar self and cross terms therefore cost only the single
actual sinh moment beyond the detail head: negative dimension is at most A+1.
The [full Haar prime finite-head theorem](../3-formalized/acs-full-haar-prime-source-finite-heads.md)
now controls the entire prime diagonal, including first powers, within
`εΓ(F)` after one coefficient head, uniformly over all original profiles
and horizons. Exact divisor incidence makes the large-multiplier part
small, and bounded multipliers cannot connect a low source to an arbitrarily
high target. Together with the disjoint mixed higher powers and detail mass,
this gives `|R−(Γ(F)+P(F))|≤εΓ(F)` after one fixed detail head. Thus R
retains `(1−ε)Γ(F)` and the positive cosh square, including the original
complete Gamma coupling. Three direct Lean source checks passed; no axiom
checks were run. First-prime mixing and coarse signed payment remain open.
The [joint whole-square payment](../3-formalized/acs-joint-whole-square-polar-payment.md)
then spends only retained coarse Gamma on the missing coarse even-power
source. For `U=R−S₂(g)`, one fixed head and c>0 give
`U+2 sinhHalfMoment(F)²+(1/2)(∫F)² ≥
 c Γ(g)+(γ_E/2)∫g²+(κ/8)D+∫h²+2 coshHalfMoment(F)²`.
The complete square source occurs exactly once in U. Uniform negative
dimension is at most A+2, read by the head and the two original moments.
Coarse first-prime and odd higher-power sources, coarse archimedean mass,
first-prime mixing, and the head/sinh/mean index costs remain unpaid.
Full signed payment remains open; low-generator translation orbits remain
noncompact.

The [full prime–polar residual](../3-formalized/acs-prime-polar-cancellation-in-gamma-norm.md)
now satisfies `|primeSum(f)−P(f)|≤ε exp(R)(Γ(f)+∫f²)` uniformly over
every real BV profile supported in [−R,R], for all sufficiently large R.
All actual prime powers and both pole moments remain. This closes the
derivative-to-Gamma norm transfer for relative cancellation on complete
cells. The exp(R) factor remains; full-source sign and uniform index are open.

The complete-cell source has a further unconditional payment:
`ArithmeticIndexDescent.OddHigherPrimePowersPayTheirWholeDetailBlock` proves
that the full even-power source and every odd higher-power term involving
details share one Gamma reserve, with uniform negative dimension at most
`A+1`. The exact term is `P_odd(F)-P_odd(g)`, so the coarse odd source remains.
See [paper proof and Lean validation](../3-formalized/acs-odd-higher-detail-payment.md).
This removes the odd higher-power detail diagonal from the unpaid blocks;
it does not give a full Weil index bound.

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
