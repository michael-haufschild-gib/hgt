# Selective Positivity and Threshold Laws (SPTL)

Namespace `GaloisForLFunctions.SelectivePositivityAndThresholdLaws`; umbrella `SelectivePositivityAndThresholdLaws.lean`; 12 modules (including `SemilocalPrimeTwoTrace/*`).
Everything is unconditional; RH appears only inside proved equivalences.

## 1. Motivation

A Weil window of half-width A reads the prime atoms n with log n ≤ 2A. Below ½log2 it reads none, so positivity there holds
for every weight w (blind). SPTL asks what happens just past each threshold: which atoms become visible, whether
positivity then depends on the arithmetic weight (selective), and which global square-root obstructions (escaped Möbius
saving, large-sieve sections, parity-blind dispersion, continuum towers) mark the same boundary. Each face is proved
as a boundary law plus a refutation witness on a battery of fake weights.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weighted Weil form | `weilFullFunctional w (EF.weilTest f f)` | Re W_w(f⋆f̃) for any weight w : ℕ → ℝ |
| Battery weights | `liouvilleTwistedVonMangoldt`, `flippedTwoVonMangoldt`, `shiftedPairVonMangoldt a`, `scaleTwistedVonMangoldt σ`, `ordinateTwistedVonMangoldt γ` | λΛ; w(2) = −log2 only; w(2) = (2^a+2^{−a})log2; n^σΛ; cos(γ log n)Λ |
| Even envelope | `evenEnvW` | 32-piece degree-8 rational upper envelope on [0,69/2] for 577/800 − (γ(r) − √2log2·cos(r log2)) |
| Legendre coefficients | `evenLegCoeff F k` | projection of F(Au) on P_{2k}, A = 181/500, k < 23 |
| Certified matrix | `hEx`, `mEx`, `vPoleEx`, `diagMultFast` | 23×23 quadratic form 2π v vᵀ − M + diagonal Bessel credit |
| Liouville ground energy | `liouvilleWindowGroundEigenvalue r` | inf Re W_{λΛ}/∫F² on C²_c([−r,r]) |
| Escaped Möbius laws | `GrowingEndpointEscapedMoebiusLaw θ`, `DyadicEscapedMoebiusLaw θ`, `moebiusHarmonicTail` | Σ_{M<j≤N} μ(j)/j = O(M^{−θ+ε}); R(N) = −Σ_{n≤N}μ(n)/n |
| Theta box cohomology | `thetaBoxH0 w s`, `thetaBoxH1 w s` | log Σ_n exp(−πn²e^{∓2E_w(s)}), E_w(s) = e^s + s − 1 − Σ_{k≤e^s}w(k) |
| Polar-box cohomology | `surfaceBoxH0`, `surfaceBoxH1` | max(0, χ₀ + (polar − Φ − D·K)/2) on the polar quadrant; h¹(D) = h⁰(K−D) |
| Jacobi–Hurwitz packet | `JacobiHurwitzTorsionPacket`, `jacobiHurwitzHeight`, `jacobiHurwitzQuad` | h_P = Σ w_i log θ_i, Tate quadratic q_P = Σ w_i πJ_i²/t_i |
| Asymptotic RI | `AsymptoticRiemannInequality`, `SingleRayDegreeZeroSubquadratic`, `UnsignedLargeSieveMajorant` | Riemann inequality up to −εn²; degree-zero growth o(n²); unsigned |x·(x−κ)| majorant |
| Selberg parity weights | `selbergEvenVonMangoldt`, `selbergOddVonMangoldt` | Λ ± λΛ |
| Parity adversary | `parityAdversaryCorrelation` | worst correlation inside a parity bracket C₀ ± κS |
| Ramanujan packet | `ramanujanStabilizerPacket Q h`, `stabilizerDivisorWeight` | truncated singular series, divisor expansion |
| Escape symbol | `escapeLaplaceSymbol ε s` | ζ(s)(ζ(s+ε)⁻¹ − Re ζ(1+ε)⁻¹)/s |
| Catalan separators | `catalanSuccessorSquareForm`, `catalanKroneckerTwistDefect` | w(2)w(4); squared phase deviation on {2,3} |
| Continuum tower test | `edgeTowerBump A`, `dyadicH1NormSq` | odd narrow bumps near ±(A−1); ∫F² + ∫F'² |
| Valuation-shell log operator | `primeValuationLogOperator p m`, `primeTwoLogOperator m` | `(log p)(P_{ℤ_p} − U^m P_{ℤ_p} U^{−m})` on `ℓ²(ℤ)` with `opTrace = m log p` |
| Single-prime semilocal family | `primeSingleSemilocalFamily p` | CCM remainder family retaining only prime powers `p^m` (`m ≥ 1`) |
| Polar Krein split | `ccmPolarEvenOperator a`, `ccmPolarOddOperator a` | `ccmPolarOperator a = 2|c₊⟩⟨c₊| − 2|c₋⟩⟨c₋|` on `suzukiApertureHilbert a` |
| Weighted / multi-prime semilocal families | `weightedPrimeFamily w`, `primeSetSemilocalFamily P`, `finitePrimeSetSemilocalFamily S` | Arbitrary-weight and `{∞} ∪ P` / `{∞} ∪ S` aperture-compatible CCM remainder families |
| Finite-prime collapse constants | `finitePrimeCollapseConst r`, `finitePrimeCollapseCoeff r`, `finitePrimeZeroCrossingCeiling r` | Cardinality-only constants for `energy A ≤ C_r − c_r e^A` (`A ≥ 4`) and zero-crossing ceiling |

## 3. Language

- **Blind / selective**: a window statement is blind if it holds for every weight, selective if it reads specific w(n).
- **Exposed atoms**: n with log n ≤ 2A; [−181/500,181/500] exposes only n = 2 (2A = 0.724 ∈ (log2, log3)).
- **Battery**: the fixed set of fake weights against which every positivity claim is tested.
- **Escaped start** M = (N−b)/a: the scale in which escaped Möbius saving must be measured.
- **Degree zero / short cycle**: classes with z·A = 0; quadratic inflation there is the Hodge-index failure signal.
- **Pole neutralization**: removing the rank-one s = 1 Chebyshev term before asking for Sobolev floors.

## 4. Mechanisms

**A. Window certificates past ½log2 (A = 181/500)**
1. Atom-two identity: if 2A < log 3 and w, w' agree off n = 2, Re W_w − Re W_{w'} = (w(2) − w'(2))/√2 · 2acorr(log2). For λΛ: Re W_{λΛ} = Re W_Λ + 2√2log2·acorr(log2).
2. Even sector: π·fullZeroForm ≥ 2π·pole² + (577/800)π∫F² − ∫₀^{69/2}(∫F cos(rx))²·W(r) for any envelope W; the cosine transform is replaced by its degree-44 Taylor polynomial (|rx| ≤ 25/2, error 23·10⁻⁶∫F²), moments ∫F x^{2m} are exact linear forms in 23 even Legendre coefficients, and the residual is a 23×23 form hEx proved PSD by exact rational LDLᵀ plus per-row Gershgorin dominance under interval bounds. Bessel converts the diagonal credit 2.2652·2A/(4k+1)c_k² into ∫F².
3. Envelope pieces: γ(r) ≥ Gauss sum of 8 terms + log term (digamma telescoping), each term → quartic in Δ = r² − s0 with Taylor remainder, trig via mid·log2 = kπ/2 + u0 and Maclaurin; coefficients rounded to rationals with Σ|c_i − d_i|δ^i slack; tail r ≥ 69/2 by 577/800 ≤ γ − √2log2.
4. Odd sector is imported (Schur lending, ArithmeticIncidencePositivity); even + odd parts combine.

**B. Refutation witnesses**
5. Odd spline: 9-knot balanced odd clamp combination with closed-form cubic autocorrelation; acorr(log2) ≤ −14807/2·10⁻⁸ makes the +2√2log2·acorr(log2) term negative enough; Lévy, polar, γ(0) terms bracketed exactly; mollification keeps oddness and support.
6. Shifted pair: one even bump with K2 > 0 at log2; w(2) = log2(2^N + 2^{−N}) drives Re W below −(1/5000)∫F².
7. Cubic–quintic witness u³(R² − u²), R = 27/50 (still single-atom: 2R < log3): Re W_ζ > (1/25)∫F² while Re W_{λΛ} < −(3/10)∫F².

**C. Square-root boundary laws**
8. Escaped Möbius: adjacent multipliers N, N+1 differ by the unit cell μ(1) = 1; dyadic escaped pairing = R(n) − R(2n), telescoping + R → 0 gives tail bounds; exact Abel identity M(N) = −(N+1)R(N) + ΣR(n); summation by parts reverses it.
9. Theta log-volumes: Poisson gives h⁰ − h¹ = E_w(s) for every w; strict monotonicity of thetaH0 0 turns termwise weight excess into strict separation.
10. Generalized Weil argument: asymptotic Riemann inequality + degree-zero subquadratic growth ⇒ Hodge index (a nef class with x·x > 0 forces (x·x/4)n²).
11. Jacobi–Hurwitz: |h_P − q_P| ≤ B_P (evenKernel ∈ [e^{−πt/4}, evenKernel 0]); q_P is either ≡ 0 on degree zero (blind) or inflates quadratically.
12. Parity lobe: Λ± average to Λ with prime-pair correlations 0 vs 4 log p log p'; a bracket of half-width κ lets the adversary align signs with the cosine transform, gaining κ s_min K₁/2 · cosTransform Ω 0 on the inner lobe, i.e. ≳ T^{1+δ} ≫ N(T,2T) log²T.
13. Character averaging over d ≤ Q with Möbius-inverted stabilizer weights reconstructs the singular-series packet; non-congruent residues have zero character mean.
14. Continuum edge bumps: width ½ < log2 kills all same-side ratio correlations; off-lattice reflected crossings at primes with log p ≈ 2A − 2 sum (Chebyshev θ(x) ~ x) to ≤ −c₀e^A with bounded H¹ norm.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Even sector: fullZeroForm F ≥ (1/5000)∫F², even F on [−181/500,181/500] | `fullZeroForm_ge_of_even_support_le_threeHundredSixtyTwoThousandths` | proved |
| All parities, complex tests, windowed W, ground energy ≥ 1/5000 for A ≤ 181/500 | `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`, `zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths`, `re_windowedW_zetaZeroConfig_nonneg_of_threeHundredSixtyTwoThousandths`, `one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths` | proved |
| Every w with w(2) = log2 is coercively positive on the window | `re_weilFullFunctional_ge_of_full_window_of_atom_two_eq` | proved |
| Odd F: Re W_ζ ≥ (1/1000)∫F², Re W_{λΛ} < −(1/1000)∫F² (also flippedTwo) | `exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`, `exists_odd_smooth_threeHundredSixtyTwoThousandths_flippedTwo_neg` | proved |
| Even F: ζ-positive, shifted pair negative | `exists_even_smooth_threeHundredSixtyTwoThousandths_zeta_pos_shiftedPair_neg` | proved |
| Selectivity battery at 181/500 | `threeHundredSixtyTwoThousandths_selectivity_battery` | proved |
| λΛ ground energy < −3/10 for every r > 27/50 (incl. 23/40); bounded below | `liouvilleWindowGroundEigenvalue_lt_neg_threeTenths_of_gt_twentySevenFiftieths`, `liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`, `bddBelow_liouvilleWindowRayleighSet` | proved |
| Catalan {2,3,4} separation of Λ from scale/ordinate/Liouville twists | `catalan_finite_gauge_separation` | proved |
| Escaped Möbius: growing-endpoint ⇔ dyadic ⇔ abscissa ≤ 1 − θ (0 < θ ≤ ½); RH ⇔ θ = ½ | `growingEndpointEscapedMoebiusLaw_tfae`, `riemannHypothesis_iff_growingEndpointEscapedMoebiusLaw_half` | proved |
| No saving θ > ½; no uniform bound over all multipliers | `not_dyadic_escapedPairing_rpow_of_half_lt`, `not_uniform_all_multipliers_escapedPairing_rpow` | proved |
| Theta box RR/Serre duality; strict shifted-pair selectivity for s ≥ log2 | `thetaBox_riemannRoch_and_serreDuality`, `thetaBox_strict_selectivity_shiftedPair` | proved |
| Box cohomology: curve calibration, golden-datum RR failure | `curve_frobMass_cohomology_calibration`, `goldenDatum_frobMass_cohomology_refutes_riemannRoch` | proved |
| Sections beyond large sieve ⇔ zetaZeroWidth ≤ σ; Serre-dual section growth ⇔ HodgeIndex ⇔ RH | `sections_beyond_largeSieve_iff_zetaZeroWidth_le`, `serreDual_section_growth_iff_riemannHypothesis` | proved |
| Asymptotic RI + subquadratic degree zero ⇒ HodgeIndex | `hodgeIndex_of_asymptoticRiemannInequality` | proved |
| Jacobi–Hurwitz dichotomy; large-sieve inflation q_P(z) ≥ ½|z·z| | `jacobiHurwitzHeight_dichotomy`, `jacobiHurwitz_largeSieve_inflation_ge_half_abs` | proved |
| Short-cycle subquadratic height for r ≤ (log2 + 1/50)/2; global version ⇔ RH | `shortCycle_subquadratic_height_exists_primeTwo`, `riemannHypothesis_iff_exists_asymptotic_subquadratic_height` | proved |
| Parity-blind dispersion diverges for every λ > 1; refutes Bδ²/(1+δ)² and 5/36 at 4/3 | `parityBlind_dispersion_diverges_above_threshold`, `parityBlind_refutes_quadratic_and_fourThirds_budgets` | proved |
| Surplus ⇒ critical-line proportion (29/36 − β; >2/3 if β < 5/36; 3/4 if β ≤ 1/18) | `coalescent_surplus_battery_laws`, `oddEvenShift_singleProfile_certifies_proportion` | proved (inputs open) |
| Multi-modulus Ramanujan split of primeCoalSum | `multiModulus_ramanujan_primeCoalSum_split` | proved |
| Escape symbol pole split; RH ⇔ positive (⇔ full) gauge mass of every escape state | `escapeLaplaceSymbol_pole_and_visibility_laws` | proved |
| No sub-exponential H¹ floor (σ < ½) on continuum towers; pole-neutralized floor ⇔ width | `not_continuumPrimeTower_subexponential_dyadicH1`, `continuum_poleNeutralized_width_equivalence` | proved |
| Positive `2`-adic logarithmic trace (`opTrace = m log 2`) and exact `{∞, 2}` trace identity on `(0, ½log3]` | `primeTwoLogOperator_isPositive`, `opTrace_primeTwoLogOperator`, `ccmRestrictedWeilSourceQuadratic_eq_semilocalPrimeTwoTrace_of_le_halfLogThree`, `primeSingleSemilocalFamily_two_energy_eq_literal_of_le_halfLogThree` | proved |
| Semilocal `{∞, 2}` positivity obstructions: unglued Sonin non-positivity, bilateral prime-`2` indefiniteness, multiplicative tensor no-go, half-integer lattice collapse & forced zero crossing, no positive `{∞, 2}` operator-trace carrier | `not_isPositive_ccmSoninGenericPartAt_one`, `neither_sign_isPositive_ccmFinitePrimeOperator_primeTwo_window`, `no_multiplicative_tensor_factorization_primeTwo_window`, `exists_aperture_primeFree_and_singleSemilocal_energy_lt`, `exists_primeTwoSemilocal_zero_crossing`, `no_positive_operator_trace_carrier_for_primeTwoSemilocal` | proved |
| Intrinsic operator-trace equivalence, unconditional positivity through `181/500 > ½log2`, upgraded `zetaContactAperture` / all-profile Hodge / Künneth / `l2SourceCone` RR, and `½log3` equivalence (`question_Q6_complete_resolution`) | `ccmPolarOperator_eq_even_sub_odd`, `isPositive_ccmRestrictedWeilZeroFormOperator_iff_opTrace_nonneg`, `isPositive_ccmRestrictedWeilZeroFormOperator_of_le_threeHundredSixtyTwoThousandths`, `threeHundredSixtyTwoThousandths_le_zetaContactAperture`, `scalingSubsurface_all_hodgeIndex_of_le_threeHundredSixtyTwoThousandths`, `kunneth_effectivity_realTestsAt_of_le_threeHundredSixtyTwoThousandths`, `l2SourceCone_realTestsAt_riemannRoch_of_le_threeHundredSixtyTwoThousandths`, `question_Q6_complete_resolution` | proved |
| Arbitrary finite-prime `{∞} ∪ S` `−Θ(e^A)` ground-energy collapse (uniform in `|S|` and arbitrary weights on `S`-prime-powers), forced zero crossings (`½log2 < a_S ≤ A_max(|S|)`, `181/500 < a_S` if `2 ∈ S`), positive-trace carrier no-go, quantitative prime lower bound `r < (visiblePrimes A).card`, `(1 + ε)` short-interval syndeticity, and infinitude of primes from bounded-below energy | `weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers`, `finitePrimeSetSemilocal_energy_le_neg_exp`, `not_exists_sublinear_exp_lower_bound_for_finitePrimeSetSemilocal`, `exists_finitePrimeSetSemilocal_zero_crossing`, `exists_finitePrimeSetSemilocal_zero_crossing_of_two_mem`, `no_positive_operator_trace_carrier_for_finitePrimeSetSemilocal`, `card_visiblePrimes_gt_of_groundEnergy_nonneg`, `eventually_exists_primePow_in_short_interval_of_primeSetSemilocal_bddBelow`, `infinite_primes_of_primeSetSemilocal_energy_bddBelow`, `finite_prime_semilocal_complete_resolution` | proved |

## 6. Tools

**Developed**
- `ldl_gershgorin_quadratic_nonneg`: PSD from exact LDLᵀ + Gershgorin on the residual (reusable for any certified Gram matrix).
- `pi_mul_fullZeroForm_even_ge_of_envelope`: even-sector reduction of fullZeroForm to an envelope W.
- Interval arithmetic kit: `abs_deg8_le`, `deg8_round_le`, `deg4_round_le`, `dot23_vec_err_le`, `mid_cos_sin_bounds`, `trig_around_mid_le_round`, `gauss_two_neg_le_delta_round`, `neg_half_log_le_delta_round`, `log_dyadic_bounds`, Padé log bounds, `gammaBracket_ge_gauss_eight_add_log`.
- Legendre kit: `legP` recurrence polynomials, exact ∫P_{2k}u^{2m}, `legP_perp_even_pow_orthog`, Bessel `integral_sq_even_ge_sum_legCoeff`, moment identity `integral_even_mul_even_pow_eq_sum_legCoeff`.
- Odd clamp splines with closed-form autocorrelation (`autocorr_oddClampCombo_eq`), Lévy quartic kernel `deltaKerFun` with closed integrals, mollification preserving parity/support.
- Abel/dyadic Möbius transfer lemmas; Jacobi–Hurwitz bounded-distance law; theta log-volume monotonicity.
- Generic Hilbert / Schatten-1 / CLM trace kit (`AbstractHilbertTraceToolkit`): `Submodule`-diamond-free `Finset` CLM evaluation (`clm_sum_apply`, `re_inner_clm_sum_left`), finite-sum self-adjointness (`isSelfAdjoint_sum`), rank-one trace characterization of `IsPositive` (`isPositive_iff_forall_opTrace_comp_rankOne_re_nonneg`), Krein polarization (`rankOne_symm_eq_two_smul_half`), and universal positive operator/Gram-trace carrier refutation (`no_positive_operator_trace_carrier_of_exists_neg`, `no_positive_gram_trace_carrier_of_exists_neg`).
- Parametric antisymmetric gap probe and `Finset` pigeonhole shift-avoidance kit (`weightedPrimeFamily_energy_le_of_log_gap`, `exists_shift_avoiding_finite_prime_powers`).

**To build**
- Envelope + LDLᵀ pipeline for windows exposing n = 3 (2A > log3), reading w(2) and w(3) jointly.
- A parity-sensitive dispersion bracket (signed stabilizer discrepancy) for the coalescent surplus.
- Selective log-volume cohomology on the full scaling surface (beyond boxes and short cycles).

## 7. Open questions

1. ζ positivity on windows past log3/2 (λΛ already fails beyond 27/50 with a single-atom witness): which weights stay positive once n = 3 is exposed?
2. Escaped Möbius saving at any θ > 0 at the growing endpoint (= any zero-free strip).
3. Subquadratic bounded-below heights on short-cycle subsurfaces with r > (log2 + 1/50)/2.
4. A prime-coalescent surplus bound β < 5/36 at λ = 4/3 by a parity-breaking method.
5. Pole-neutralized continuum tower floors at rate σ < ½ (= zetaZeroWidth ≤ σ).
6. How far does the even-sector certificate extend (61/500? log3/2?) with more Legendre modes and pieces?

## 8. Traps

| Trap | Fact |
|---|---|
| Window positivity below ½log2 says something about ζ | It is blind: holds for every weight |
| Positivity past ½log2 is selective in general | It reads only exposed atoms; on 181/500 exactly w(2) |
| The 23/40 failure of λΛ is a two-prime effect | The witness lives in [−27/50,27/50], 2R < log3: single atom n = 2 |
| Rank-based h⁰ separates Λ from shifted pairs | Ranks read support only; log-volumes separate |
| A uniform escaped Möbius bound over all multipliers | False: adjacent multipliers isolate μ(1) = 1 |
| Escaped saving beyond θ = ½ | Impossible unconditionally |
| Parity-blind dispersion reaches the 4/3 budget | Diverges on the inner cosine lobe for every λ > 1 |
| Lattice tower bounds transfer to the continuum | Edge bumps give −c₀e^A at bounded H¹; neutralize the pole first |
| Large-sieve majorants yield subquadratic heights | They force inflation q_P(z) ≥ ½|z·z| |
| Box cohomology satisfies RR on the positive cone | Fails on goldenDatum: h⁰ + h¹ = 0 while χ = n² |
| The certificate constants are tight analysis | 577/800, 1/5000, 23·10⁻⁶ are certificate margins, not sharp |
| Finite-prime `{∞} ∪ S` semilocal truncations approximate RH as `|S|` grows | Every finite `S` (and arbitrary weights on `S`-prime-powers) collapses at the full uncompensated pole rate `−Θ(e^A)` and crosses zero; bounded-below energy requires infinitely many primes with `(1 + ε)` short-interval prime-power density |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 6 (blind node-two certificate, shifted zeta pair, Möbius–Mertens, pole self-energy, Euler–Mascheroni bounds, Suzuki) |
| ArithmeticEffectivityTheory | 5 (theta surface, effectivity calculus, base does not extend) |
| SquareRootThreshold | 4 (window certificates, atom-two identity, aperture 3/10, odd window) |
| ArithmeticOrientationTheory | 4 (continuum tower, width dictionary, coset Toeplitz) |
| ArithmeticCorrelationGeometry | 3 (escaped pairing, coalescent stabilizers, escape visibility) |
| ArithmeticCastelnuovoSeveri | 3 (short cycles, Hodge-index failure, determinantal sections) |
| TransThresholdPairCorrelation, ArithmeticCorrespondencePositivity, arithmetic-positivity-theory | 2 each |
| PNTPlus, BiarithmeticGaugeGeometry, BezoutValuationIncidence | 1 each |

| Used by | Module |
|---|---|
| BezoutValuationIncidence | UnconditionalEscapedMoebiusDecayAndCrossRouteBridge (escaped Möbius law) |
| ArithmeticIncidencePositivity | AnExplicitLargerApertureRetainsAWeilFloor (181/500 certificate), NineModulusCollarSelectivityAndPolarLedger (Catalan/tower) |
| SpacingScaleHarmonicAnalysis | TheGaugeBecomesVisibleAtTheCriticalExponent (Catalan/tower) |
| MainTheorems | umbrella |

| Neighbour | Relation |
|---|---|
| SquareRootThreshold | supplies window certificates and blindness below ½log2; SPTL is its first selective step |
| ArithmeticIncidencePositivity | odd window at 181/500 (Schur lending); consumes SPTL's even sector |
| ArithmeticCastelnuovoSeveri / ArithmeticEffectivityTheory | Hodge index, effectivity, theta surface; SPTL adds real-valued Serre-dual cohomology and heights |
| TransThresholdPairCorrelation / ArithmeticCorrelationGeometry | coalescent surplus programme; SPTL proves the parity barrier and the stabilizer split |
| ArithmeticOrientationTheory | continuum prime tower; SPTL shows the lattice bound does not transfer without pole neutralization |
| BezoutValuationIncidence | escaped Möbius cross-route bridge consumes the boundary law |

## 10. Big picture

Positivity of Weil's form on short windows is not evidence about ζ until the window is long enough to see a prime, and
the first prime it sees is read only through its weight. SPTL proves that the first selective step is real: past ½log2
the form is positive exactly for weights with the right value at 2, and fake weights are caught by explicit tests. This
makes each additional exposed prime a separate, certifiable event, and shows that window-by-window positivity is a
sequence of finite arithmetic checks rather than a single analytic inequality; it does not by itself approach RH.

On the global side, every face of the square-root threshold reproduces the same picture: escaped Möbius saving,
sections beyond the large sieve, subquadratic heights, gauge visibility and pole-neutralized tower floors are each
exactly equivalent to a zero-free strip or to RH, while the methods that ignore sign or parity (unsigned large-sieve
averaging, parity-blind dispersion, unneutralized continuum towers) provably fail. The lesson for the RH programme:
any successful route must carry sign and parity information through the threshold; blind methods stop exactly at it.
