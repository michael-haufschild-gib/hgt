# Floor-Free Arithmetic (FFA) programme

- **ID:** ffa-programme
- **Stage:** 1-in-progress
- **Type:** PROGRAMME
- **Source:** docs/reports/review-1011/obstacles-summary.md §4 (items A121, A123–A131, B170–B173)
- **Statement:** theory of mechanisms without a floor: floors of mechanisms, the four floor-free
  kinds of inequality, AAL as non-attainment, and the search for a producer.

## Goal
Folder `formal/GaloisForLFunctions/FloorFreeArithmetic/`, umbrella `FloorFreeArithmetic.lean`,
foundational README. Deliver the first theorems of the six tracks of §4.5, drive each track to its
kill or its survivor, and record what a producer must be.

## Corpus facts the programme starts from (do not redo)
- Finite top layer: `SurfaceOfSpecZ.ScaleLocality.exists_finite_top_of_not_abscissaLaw`,
  `positiveTopSupport`, `topTrace_eq_positive_sum`, `tendsto_normTrace_sub_topTrace`,
  `zeta_finite_top_negative_windows` (one-sided, length `(k+1)π/67`),
  `asymptoticAbscissaLaw_of_lengthDependent_floors` (N2).
- Vandermonde window bound: `InfiniteRankWeilTheory.exists_pos_forall_window_le_norm_expSum`,
  `exists_pos_forall_window_le_norm_pointSum`.
- Positivity floor (A124): `MultiplicativePositivityGeometry` — `multiFrequency_purchase_le_two`,
  `interior_zero_invisible`, `siegel_member_zero`, `exclusion_iff`.
- Feasibility receiver: `ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_feasible_at_every_aperture`,
  `not_riemannHypothesis_iff_empty_aperture`.
- Projection to the line: `ZeroConfigurationGeometry.criticalProjectionConfig` (counts preserved).
- Local moments: `SurfaceOfSpecZ.ScaleLocality.localPrimeTraceMoment`,
  `riemannHypothesis_iff_localPrimeTraceMoments`.
- Exceptional layer filters (integrality): `ExceptionalLayerTheory` (`LocalFiltersRecoverTheTopDivisor`,
  `DampingFiltersReadTheExceptionalDivisor`).
- Index exit: `ArithmeticOrientationGeometry.riemannHypothesis_iff_encard_rightZeros_lt_two`.

## Tracks, items of §4, state
| Track | Item | Result | State |
|---|---|---|---|
| 1 | A121 N1 | finite top layer ⇒ two-sided attainment on every late window of every length; window non-attainment ⇒ AAL, for the spline trace, for `ψ(x) − x`, at the primes, and for every tempered conjugation-symmetric configuration without real right zeros | Lean |
| 1 | A121 N3 | window moments of a finite layer have rate `2k·b`; one exponent for all orders ⇒ AAL; a moment of one order of smaller order than its own rate ⇒ AAL (mean-square N1) | Lean |
| 1 | A125 N4 | AAL ⇔ every line has at most one or infinitely many zeros to its right | Lean |
| 1 | A127 | tangent datum = Bohr coefficients of the top trace; trace `o(e^{bu})` ⇔ empty top line; the trace determines the layer; dichotomy; one window length leaves the top line empty or infinite; integrality `e = 2m B̂²` and the unit gap of a multiplicity | Lean |
| 1 | A127 tautology | every finite datum (depth in `(0, ½]`, positive ordinates, multiplicities) is the top layer of a finite configuration with both symmetries; mechanisms true on all tempered symmetric configurations have models at every depth | Lean (kill) |
| 1 | mechanisms (ii), (iii) | positivity: for every `Θ < 1` and every finite datum a nonnegative density with Laplace transform `1/(s−1) − Σ m_j(1/(s−ρ_j)+1/(s−ρ̄_j)) + entire` (continuous primes, simple pole); Euler products: for every `½ < Θ < 1` and every finite datum natural norms `q_k ≥ 2` with `∏(1−q_k^{−s})^{−1} = Σ a_n n^{−s} = G(s)/(s−1)`, `a_n ∈ ℕ`, `G` holomorphic on `Re s > ½` vanishing exactly on the datum, linear counting; integrality gives the quantum of a multiplicity and no a priori bound below it; the property `EulerSymmetric` of a configuration (tempered, both symmetries, right zeros = divisor of a natural-norm Euler product) holds for `ζ` and has floor `½`; positivity on `Re s = 1` is the count `2M ≤ A`; a system that only adds primes has `E(σ_c) = 0` when `E` is holomorphic at its real abscissa | Lean (kill) |
| 1 | mechanism (i) replication | bounded phase return ⇒ replication is `ArithmeticAuxiliaryDynamics.TheMissingInputOfTransport`; here: along every phase return the sup of the translates over a domain joining a zero of a finite layer to `Re s > 1` tends to infinity, a bounded normalization has `c_j → 0`, every locally uniform limit of normalized translates is `0` | Lean (kill) |
| 2 | A128 | feasibility at an aperture ⇔ spectral kernels positive definite on intervals; tapered kernels `K_f·(φ⋆φ̃)` are positive definite on the line, hence characteristic functions of finite positive measures (corpus Bochner), and one such measure with `φ ≠ 0` gives the sign on `f`: the feasible set as positive measures, without Krein's extension theorem; a null vector makes its spectral kernel vanish on the whole interval (boundary systems); rigidity: every family of certificates converges to `Λ` | Lean |
| 2 | A129 | first coefficient test: `c + R` with `‖R(σ)‖ = B^{−σ}g(σ)`, `g → 0` more slowly than every exponential, is the L-series of no sequence. Pencil at every shift `h > 0`: amplitude `≍ σ^{−h}` (log-convexity of `Γ`), exact `2π(s−2)/(s(s+1))·ζ(s−1)/ζ(s+1)` at `h = 1`; cleared Eisenstein constant term at every height `Y > 0`: `B = Y²`, amplitude `≍ σ^{−1/2}`. Neither is a Dirichlet series over its dominant half. Symmetric completions; the statement on a window: not done | Lean (kill) |
| 3 | A126 | Hurwitz transfer of bounded counts; tower `Λ(s)/Λ(s+N)` keeps the count (kill); index-`κ` realization bounds right zeros by `κ`; clock: `E_r ≤ E_s ≤ W`, negative directions of `W` are negative at every cutoff, sign or floor at one cutoff per aperture ⇒ RH (kill: no unit gap before the limit); heat flow (regulator from the good side, unitary for `t ≥ 1/8`): `N(t) ≤ 1` on times tending to `0` ⇒ RH, and `¬RH ⇒ N(t) ≥ 2` for all small `t` (with the corpus: `N(t)` = count of `Ξ` at small times) | Lean |
| 4 | A130 | prime side of a projected pair; second-order law and converse; no convergent linear statistic is monotone (kill); heat statistic monotone exactly below `(2t)^{−1/2}`; additive functionals of the depths = mixtures of counts / inner masses (kill of the additive class); differentiable functions of finitely many linear statistics are monotone only where the gradient symbol vanishes on the line | Lean |
| 5 | A131 | moment law on fixed windows; a `2k`-th moment bound `Ce^{AT}` on a window gives `\|2Re S\|^{2k+1} ≤ 2^{2k+1}GCe^{(A+1)T}` there (Lipschitz rate `e^{R/2}` of the trace); moments of all orders with one exponent ⇔ sup powers with one exponent ⇐ two-sided `C_ε e^{εT}` (kill: amplification on windows = RH-quality bound on some late windows; one order = a half-plane). The trivial bound has slope 1 in the order | Lean |
| 6 | A123, A124 | floor calculus; floors: tempered class `½`, exponent-`σ` floors exactly `σ`, count laws `½`, one-length window floors admit finite strata; A124 = MPG, A123 = `RHTower.fixed_slot_boundary` | Lean + citation |
| — | B170 | N1 for `ζ`: open, of AAL strength. Excluded as sources: identities of the explicit formula, both symmetries, positivity below `Re s = 1`, Euler products with natural norms or over the rational primes, normal families of translates | open |
| — | B171, B117 | a form of index one with the zeros as symmetric spectrum; approximants with at most one right zero: open, of RH strength. The form of B171 is in the corpus: archimedean minus primes has a negative vector unconditionally and no negative plane exactly under RH (`RHTower.riemannHypothesis_iff_not_exists_negDef_markovPlane`). The tower, the clock and the heat flow do not supply the count | open |
| — | B172 | no linear statistic; every additive functional of the depths is a mixture of inner masses. What remains is a minimality principle for `ζ` (equality case of Jensen: kind c) | answered in the additive class; remainder open |
| — | B173 | on windows: equivalent to a two-sided bound `C_ε e^{εT}` on arbitrarily late windows; one order reaches the depth `A/2k` only | identified; open |
| — | producer | none found | open |

## Mathematics (every item is in Lean; the modules are named)
1. **Uniform badness (N1).** Top trace of a finite layer: `P(u)=Re Σ_{z∈S} 2e_z e^{iγ_z u}` =
   exponential sum with the `2|S|` distinct frequencies `±γ_z`. Sample at `u=(M+1+m)h`, nodes
   `e^{±iγ_z h}` distinct for `h<π/max γ`; the inverse Vandermonde bound gives `|P|≥ε` at one of
   `2|S|` consecutive samples, so on every window of length `L≥(2|S|+1)h`. Lower layers die out
   (`FiniteTopLayersAreSeenOnEveryWindow`).
2. **Positivity in tangent form.** Positivity of the prime measure admits every finite layer
   below `Re s = 1` and is a count on that line. Below the line, for every finite datum:
   density `e^u − Σ2m_j e^{Θu}cos γ_j u + 2M e^u 1_{u≤u₀} ≥ 0`, `u₀=log(2M+2)/(1−Θ)`, transform
   `1/(s−1)−Σm_j(1/(s−ρ_j)+1/(s−ρ̄_j))+entire` (`PositivityAdmitsEveryFiniteDatum`). With a pole
   of weight `A ≥ 2M` no compensator is needed and the transform is the rational function
   `A/(s−1)−Σm_j(1/(s−ρ_j)+1/(s−ρ̄_j))`. On `Re s = 1` the density is eventually nonnegative
   exactly when `2M ≤ A` (value of the normalized density at a simultaneous return of the
   phases, corpus `RHTower.exists_simultaneous_phase_recurrence`); with a simple pole only for
   the empty layer (`PositivityOnTheLineOfThePole`).

3. **Track 4 kill.** Reflection pair of depth `δ`, ordinate `ξ` ↔ spectral points `ξ∓iδ`.
   Split increment of `Σ_ρ F(ξ_ρ)`: `Re F(ξ+iδ)+Re F(ξ−iδ)−2Re F(ξ) = −δ² Re F''(ξ)+O(δ⁴)`.
   Monotone at all ordinates and small depths ⇒ `Re F` concave on `ℝ` ⇒ (bounded) constant ⇒
   (decaying) zero. So no convergent explicit-formula statistic is monotone under projection
   (`LinearStatisticsAreNotMonotoneUnderProjection`). For a differentiable function `φ` of
   finitely many statistics: `Δ = −δ² Re F''(ξ) + o(δ²)`, so `φ(S+Δ) − φ(S) =
   −δ² Σ ∂_iφ(S) Re F_i''(ξ) + o(δ²)`; monotone at every ordinate ⇒ the real part of the
   gradient symbol `Σ ∂_iφ(S) F_i` is concave on the line ⇒ zero there when it decays
   (`TheGradientLawOfProjection`).
   Heat statistic `e^{−tξ²}`: `Re F'' = (4t²ξ²−2t)e^{−tξ²}`, monotone exactly below the height
   `(2t)^{−1/2}`: a floor in the height. Survivors are non-analytic in the zeros (Jensen,
   Littlewood): mixtures of inner masses `I_σ`.
4. **B171 receiver.** Zeros right of the line that are eigenvalues, at the spectral points
   `i(ρ−½)`, of an operator symmetric for a form with `κ` negative squares number at most `κ`
   (`AnIndexOneRealizationIsAUnitGap`, with `HTGeometry.card_upper_eigenvalues_le`). The form
   itself is in the corpus: `arch − primes` (no pole term) has a negative vector
   unconditionally and no negative definite plane exactly under RH
   (`RHTower.exists_markovEnergy_neg`, `RHTower.riemannHypothesis_iff_not_exists_negDef_markovPlane`).

5. **Integer norms at every depth (in Lean).** Density of a layer in the logarithmic coordinate:
   `w(t) = (e^t − Σ2m_j e^{Θt}cos γ_j t)/t` for `t ≥ A`, `0` below, `A` one beyond the domination
   length. Laplace transform `= −Φ_A(s−1) + Σ m_j(Φ_A(s−ρ_j)+Φ_A(s−ρ̄_j))` with the cut-off
   Frullani logarithm of the corpus, so the continuous zeta function is
   `∏(F_A(s−ρ_j)F_A(s−ρ̄_j))^{m_j}/F_A(s−1)`, `F_A` entire with the single zero `0`. Quantiles
   `W(t_k) = k+1` (`|N − W| ≤ 1`), rounding `q_k = ⌈e^{t_k}⌉`: Euler logarithm
   `= ∫e^{−su}w + sΛ(s) + primeCorrection + R(s)`, the last three holomorphic on `Re s > ½`.
   Rounding to the next rational prime: displacement `≤ p^{−(1−α)}` for `α > 17/30` (corpus
   prime-gap theorem), prime correction holomorphic on `Re s > 17/30`: Euler product over the
   rational primes with natural exponents and any finite layer at `17/30 < Θ < 1`
   (`QuantileDiscretizationOfAPrimeDensity`, `FiniteLayersInDiscreteEulerProducts`,
   `FiniteLayersInIntegerNormEulerProducts`, `FiniteLayersInEulerProductsOverTheRationalPrimes`,
   `FiniteLayersAreRealizedWithTheirMultiplicities`).

6. **The configuration does not see the Euler product.** `EulerDivisor Z`: the zeros of `Z`
   right of the line with multiplicities are the divisor on `Re s > ½` of `G`, `G(s)/(s−1)` an
   Euler product over natural norms and the Dirichlet series of its natural coefficients, with
   linear counting. It holds for `ζ` (rational primes, `G = (s−1)ζ`) and for the configuration
   of every finite datum of depth `< ½`; with temperedness and both symmetries the floor is `½`
   (`TheZeroConfigurationDoesNotSeeTheEulerProduct`).

7. **One-sided systems.** `E = exp D`, `D` a nonnegative general Dirichlet series with real
   abscissa `σ_c`. If `E` were holomorphic and free of zeros on a disc at `σ_c`, its logarithm
   on the disc (corpus `HTGeometry.exists_log_on_ball`) would differ from `D` by a constant on
   the right half (zero derivative on a convex set) and continue `D`, against Landau. So a
   holomorphic `E` has a zero in every disc at `σ_c`, hence `E(σ_c) = 0`
   (`SystemsThatOnlyAddPrimesVanishAtTheirRealAbscissa`).

## Modules (folder `FloorFreeArithmetic/`) — all checked with `lake --old env lean`, clean
| Module | Content |
|---|---|
| `TheFloorOfAMechanism` | `Mechanism`, `ExcludesBeyond`, `HasModelAt`, `HasFiniteStratumModel`, `floor`, `FloorFree`; floor calculus; `floor_temperedConfig`; `ExponentialFloor`, `floor_exponentialFloor`; `CountInvariant`, `floor_eq_half_of_countInvariant` |
| `FloorsOnWindowsOfOneLengthHaveModels` | `WindowFloor L`, `topTrace_isolatedPair`, `hasFiniteStratumModel_windowFloor` |
| `FiniteTopLayersAreSeenOnEveryWindow` | `exists_pos_forall_window_le_norm_realExpSum`, `finite_top_seen_on_every_window`, `WindowNonAttainment`, `not_windowNonAttainment_of_finite_top` |
| `NonAttainmentGivesTheAbscissaLaw` | N1: `uniform_attainment_of_not_asymptoticAbscissaLaw`, `asymptoticAbscissaLaw_of_windowNonAttainment`; N4: `even_card_rightOf_zeta`, `asymptoticAbscissaLaw_iff_encard_rightOf_le_one` |
| `QuantileDiscretizationOfAPrimeDensity` | `PrimeDensity` (density, cut, floor), `W`, `atom`, `atomCount_eq`, `abs_discrepancy_le`, `summable_exp_atom`, `discreteZeta_eq_tprod`, `correction`, `differentiableOn_correction`, `eulerLog_eq`, `discreteZeta_eq` |
| `FiniteLayersInDiscreteEulerProducts` | `layerNumer`, `layerCut`, `layerLogDensity`, `layerPrimeDensity`, `integral_cexp_mul_layerLogDensity`, `frullaniUnit`, `layerRegular`, `layerRegular_eq_zero_iff`, `cexp_layer_eq`, `exists_discrete_euler_product_with_layer` |
| `FiniteLayersInIntegerNormEulerProducts` | `PrimeDensity.primeNorm`, `roundedAtom`, `roundedCorrection`, `differentiableOn_roundedCorrection`, `genEulerLog_primeNorm_eq`, `exists_integer_norm_euler_product_with_layer` |
| `FiniteLayersInEulerProductsOverTheRationalPrimes` | `PrimeDensity.rationalPrime`, `primeAtom`, `eventually_primeAtom_sub_le`, `summable_displacement`, `primeRoundedCorrection`, `tsum_neg_log_primeAtom_eq`, `exists_rational_prime_euler_product_with_layer` |
| `FiniteLayersAreRealizedWithTheirMultiplicities` | `layerCofactor`, `layerRegular_eq_pow_mul_cofactor`, `analyticOrderAt_layerRegular`, `analyticOrderAt_layerRegular_conj`, `exists_integer_norm_euler_product_with_divisor` (orders `m_j` at `Θ ± iγ_j` for distinct positive ordinates) |
| `TheZeroConfigurationDoesNotSeeTheEulerProduct` | `EulerDivisor`, `EulerSymmetric`, `nthPrime`, `hasProd_nthPrime`, `eulerDivisor_zetaZeroConfig`, `eulerSymmetric_zetaZeroConfig`, `eulerDivisor_layerConfig`, `hasModelAt_eulerSymmetric`, `floor_eulerSymmetric`, `not_forall_abscissaLaw_of_eulerSymmetric` |
| `PositivityOnTheLineOfThePole` | `poleDensity`, `poleDensity_nonneg`, `laplace_poleDensity`, `two_mul_sum_le_of_eventually_nonneg`, `eventually_nonneg_poleDensity_one_iff`, `eventually_nonneg_poleDensity_simple_iff` |
| `SystemsThatOnlyAddPrimesVanishAtTheirRealAbscissa` | `exists_zero_of_eulerFactor_differentiableOn`, `eulerFactor_abscissa_eq_zero` |
| `TheGradientLawOfProjection` | `splitIncrement_sub_quadratic`, `abs_splitIncrement_add_le`, `clm_apply_eq_sum`, `sum_gradient_mul_re_deriv2_nonpos`, `concaveOn_re_gradientSymbol`, `re_gradientSymbol_eq_zero` |
| `TheSplineTraceClassificationAtTheZeroAbscissa` | another agent's module in this folder (card `3-formalized/ffa-spline-trace-classification-at-zero-abscissa.md`); wired by them |
| `PositivityAdmitsEveryFiniteDatum` | `dominationLength`, `layerDensity`, `layerCorrection`, `layerDensity_nonneg`, `laplace_layerDensity`, `exists_nonneg_density_with_layer` |
| `TheTangentOrdersOfMobiusAndLiouville` | `analyticAt_zeta_two_mul`, `meromorphicOrderAt_mobius`, `meromorphicOrderAt_liouville`, `meromorphicOrderAt_zeta_two_mul_pow_div_pow` |
| `EveryFiniteDatumIsATopLayer` | `layerConfig`, `mem_positiveTopSupport_layerConfig`, `exists_config_with_top_layer`, `not_abscissaLaw_layerConfig`, `hasModelAt_of_forall_tempered_symmetric` |
| `NonAttainmentIsALawOfConfigurations` | `exists_finite_top_of_not_abscissaLawAt_config` (top layer beyond the depth `h`), `exists_finite_top_of_not_abscissaLaw_config`, `abscissaLaw_of_windowNonAttainment_config` |
| `ThePrimeNumberTheoremIsNotAttainedOnWindows` | `psi_attained_on_every_window_of_not_asymptoticAbscissaLaw`, `asymptoticAbscissaLaw_of_psi_window_nonAttainment` |
| `ThePrimesAttainTheTopRateOnEveryWindow` | `finite_top_seen_at_primes_on_every_window`, `asymptoticAbscissaLaw_of_prime_window_nonAttainment` |
| `TheOrderOfAMomentIsTheDepthItReaches` | `false_of_frequently_exp_le`, `abscissaLawAt_of_window_moment` (order `2k`, exponent `A` ⇒ abscissa law at every depth `h ≥ A/2k`) |
| `MomentBoundsOfAllOrdersAreSupBounds` | `norm_cexp_I_mul_sub_le`, `exists_lipschitz_two_re_lagStructure`, `pow_mul_min_le_integral_pow`, `topDepth_half`, `abs_two_re_lagStructure_le`, `exists_abs_trace_pow_le_of_moment_le`, `WindowMomentsBounded`, `WindowSupPowersBounded`, `windowMomentsBounded_iff_windowSupPowersBounded`, `windowSupPowersBounded_of_subexponential`, `asymptoticAbscissaLaw_of_windowSupPowersBounded` |
| `MomentsOnWindowsAmplifyTheDepth` | `abs_topTrace_sub_le`, `finite_top_moment_lower_bound`, `finite_top_moment_upper_bound`, `asymptoticAbscissaLaw_of_window_moments`, `asymptoticAbscissaLaw_of_moment_window_nonAttainment` |
| `TheTopTraceDeterminesTheTopLayer` | `bohrCoefficient_topTraceC`, `tendsto_normTrace_zero_iff`, `topCoeff_eq_of_tendsto_normTrace_sub`, `tendsto_normTrace_zero_or_attained`, `windowNonAttainment_forall_iff_tendsto`, `tendsto_normTrace_zeta_zero_iff`, `zeta_top_line_empty_or_infinite_of_windowNonAttainment` |
| `TheMultiplicityIsAMeanOfTheTrace` | `tendsto_windowAverage_normTrace_bohrChar`, `evenCoeff_zeta_eq`, `not_mem_zetaZeroConfig_of_mean_lt_quantum` |
| `UnitGapsPassToTheLimit` | `eventually_exists_zero_near`, `card_zeros_le_of_tendstoLocallyUniformlyOn`, `riemannHypothesis_of_unit_gap_limit`, `forall_re_le_of_unit_gap_limit`, `card_rightZeros_le_of_bounded_index_limit`, `towerQuotient_unit_gap_iff` |
| `AnIndexOneRealizationIsAUnitGap` | `card_rightZeros_le_of_realization`, `encard_rightZeros_le_of_realization`, `riemannHypothesis_of_indexOne_realization` |
| `FeasibleSystemsArePositiveDefiniteOnIntervals` | `PositiveDefiniteOnNodes`, `sum_spectralKernel_eq_weilFullFunctional`, `aperturePositive_iff_spectralKernel_positiveDefiniteOnNodes`, `eq_zero_of_positiveDefiniteOnNodes_of_zero`, `spectralKernel_eq_zero_of_null` |
| `ReflectedHalvesAreNotDirichletSeries` | `not_lSeries_of_slow_amplitude`, `rpow_mul_gamma_le`, `gamma_le_rpow_mul_gamma`, `tendsto_gamma_quotient_zero`, `tendsto_exp_mul_gamma_quotient`, `norm_xi_shift_quotient`, `tendsto_shiftCoefficient`, `not_exists_lSeries_pencil_shift`, `norm_constantTerm_quotient`, `not_exists_lSeries_constantTerm` |
| `ThePencilAtShiftOneIsNotADirichletSeries` | `xi_eq_zeta_mul_gammaR`, `xi_ne_zero_of_one_lt_re`, `xi_sub_one_div_xi_add_one`, `tendsto_mul_xi_sub_one_div_xi_add_one`, `not_exists_lSeries_pencil` |
| `TaperedKernelsOfAFeasibleSystemAreTransformsOfPositiveMeasures` | `weilTest_self_zero`, `positiveDefiniteOnReal_mul_weilTest`, `exists_measure_charFun_eq_taperedKernel`, `re_weilFullFunctional_nonneg_of_charFun_taperedKernel` |
| `CertificatesConvergeToThePrimes` | `exists_bound_of_aperturePositive`, `exists_re_weilFullFunctional_eq_finite`, `tendsto_weight_of_aperturePositive_seq`, `exists_aperture_forall_abs_weight_sub_le` |
| `TranslatesAtAFiniteLayerHaveOnlyTheZeroLimit` | `isPhaseReturn_comp`, `translatesBoundedOn_of_eventually`, `NormalizedTranslatesBoundedOn`, `forall_eventually_exists_lt_norm_translate`, `tendsto_normalization_zero`, `eqOn_zero_of_tendstoLocallyUniformlyOn_normalized`, `asymptoticAbscissaLaw_of_boundedNormalizedReturns` |
| `AdditiveFunctionalsOfTheDepthsAreMixturesOfInnerMasses` | `layerCount`, `layerInnerMass`, `sum_profile_sub_eq_integral_count`, `sum_profile_sub_nonneg`, `sum_profile_sub_eq_innerMass`, `sum_profile_sub_eq_of_innerMass_eq`, `rightZeros_profile_drop_eq_integral_count` |
| `TheHeatFlowHasTheCountOfItsLimit` | `eventually_two_le_nonrealZeroCount`, `riemannHypothesis_of_frequently_nonrealZeroCount_le_one` |
| `TheClockRegulatorLiesBelowWeilsForm` | `greenWeilEnergy_mono`, `greenWeilEnergy_le_form`, `greenWeilEnergy_neg_of_form_neg`, `riemannHypothesis_of_greenWeilEnergy_floor`, `riemannHypothesis_of_greenWeilEnergy_nonneg` |
| `LinearStatisticsAreNotMonotoneUnderProjection` | `splitIncrement`, second-order law and converse, `concaveOn_re_of_splitIncrement_nonneg`, `exists_splitIncrement_neg_and_pos`, `heatSymbol_splitIncrement_sign`, `splitIncrement_fourierSymbol` |

Umbrella `FloorFreeArithmetic.lean` (imported in `MainTheorems.lean`); README written.
Oleans built for own modules imported by other own modules (`TheFloorOfAMechanism`,
`FiniteTopLayersAreSeenOnEveryWindow`, `MomentsOnWindowsAmplifyTheDepth`,
`TheTopTraceDeterminesTheTopLayer`, `NonAttainmentIsALawOfConfigurations`,
`PositivityAdmitsEveryFiniteDatum`, `QuantileDiscretizationOfAPrimeDensity`,
`FiniteLayersInDiscreteEulerProducts`, `FiniteLayersInIntegerNormEulerProducts`,
`FeasibleSystemsArePositiveDefiniteOnIntervals`, `ThePencilAtShiftOneIsNotADirichletSeries`,
`EveryFiniteDatumIsATopLayer`, `FiniteLayersAreRealizedWithTheirMultiplicities`,
`LinearStatisticsAreNotMonotoneUnderProjection`) and for three missing dependencies
(`SurfaceOfSpecZ/ScaleLocality/{FiniteTopLayersNeedNoSeparation,LengthDependentFloorsGiveTheAbscissaLaw}`,
`SelectiveArithmetic/TheFirstSelectiveWindowOfZeta`).

## Not done
- The extreme points of a feasible set as discrete objects (A128, second half): only the
  annihilation by a null vector is in Lean.
- B117: a regulator unitary at every cutoff with limit `ξ`. The heat flow is unitary from
  `t = 1/8` on and approaches from the good side, but unitarity at every `t > 0` is RH
  (`Λ ≤ 0`). Whether the clock at a fixed cutoff is negative on some packet at large aperture
  under RH is not decided (no proof written).
- Prime side of symmetric completions of zero-free Dirichlet polynomials; the prime side of a
  reflected half on a window (the first coefficient test is a statement on the whole axis).
- Top traces of `μ`, `λ` and twisted multiplicative functions in world I on windows. In Lean:
  the orders of their Dirichlet series; in the corpus: `M(x) ≠ o(x^Θ (log x)^{m−1})` at a zero
  of order `m` on an attained frontier (`RHTower.not_mertens_littleO_zetaZeroAbscissa_of_le_order`)
  — do not redo.
- One-sided modifications of the primes are rigid in the corpus
  (`RHTower.landau_relative_rigidity`: a new zero of `ζ·E`, `E` a positive perturbation, costs a
  real singularity at or beyond it) — do not redo.
- A model with an Euler product and a functional equation and a finite non-real top layer: none
  exists among discrete prime systems with the completed functional equation (corpus rigidity:
  such a system is the rational primes).
- A producer: none found; B170, B171, B173 are of AAL/RH strength.

## Log
- 2026-11-10 — created; corpus survey done.
- 2026-11-11 — 36 modules clean (plus one of another agent); README written; every paper item
  of this card is in Lean; no producer. Paused by the user.
