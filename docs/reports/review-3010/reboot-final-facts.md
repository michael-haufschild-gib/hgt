# Reboot-final: mathematical facts read from the Lean corpus

Facts only. Each entry names its Lean anchor (path relative to `formal/GaloisForLFunctions/`).
[S] = statement and proof read. [D] = statement and module docstring read. [T] = module title only. [X] = the corpus states
this about a pinned external dependency (`Zeta23`, `lakefile.toml`), whose source lies outside
`formal/GaloisForLFunctions` and was not read.

## G1. The Weil cone uniqueness theorem: what it actually uses

- `WeilPositiveFull lam` := for every `C²` compactly supported `f`, `0 ≤ Re weilFullFunctional lam (f ⋆ f̃)`,
  where the functional is `k̂(i/2) + k̂(−i/2) − Σ_{n≥2} lam(n)n^{−1/2}(k(log n) + k(−log n)) + (1/2π)∫k̂·gammaBracket`.
  Pole weight is fixed to 1 and the Gamma bracket is ζ's. `RHTower/WeilFullConeRiemannKernelRigidity.lean:256–266` [S].
- `eq_vonMangoldt_of_weilPositiveFull` is proved by `eq_vonMangoldt_of_xiDivisibleBlindFamily`, which goes
  through `boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindFamily`: if `W_lam ≥ 0`, its Bochner boundary
  measure gives zero mass to `{r : ζ(½+ir) ≠ 0}`. Positivity plus one blind `Ξ`-divisible family localizes the
  spectral measure of *any* positive candidate onto the critical zeros of ζ; `lam = Λ` and RH follow
  (`riemannHypothesis_of_boundaryMeasure_criticalZeros`). `RHTower/WeilConeXiDivisibleBlindFamily.lean:540–600` [S].
- The family is built from the twisted-arc minimum principle (a theorem about the modular half-domain and
  integer Fourier moments). Its members satisfy `F̂ = Ξ·Q_j`, so they vanish at every zero of Ξ wherever it lies.
  The construction is the same whether or not RH holds. `RHTower/WeilConeUniquenessUnconditional.lean:1–20, 80–103` [S].
- Under the same hypotheses the corpus also proves `RH ↔ PrimeBlindPositive`
  (`riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindFamily`). [S]
- Node set of prime-blind positivity: `primeBlindPositiveOn_iff_weilPositiveFull_vonMangoldt_and_support`:
  positivity on a node set `S` ⇔ `W_Λ ≥ 0` and `S` contains every `n` with `Λ(n) ≠ 0`.
  `SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean:389` [D]. The "prime-free" form needs the prime
  powers as the node set; only the weights disappear.
- Degree version: `eq_smul_vonMangoldt_of_weilPositiveDegree`: with pole weight `d > 0` the only positive
  weight is `d·Λ`. `RHTower/WeilConeDegreeTwinRigidity.lean:111` [D].

## G2. Unconditional zero-proportion engine (Zeta23 + RHTower census)

- [X] The pinned dependency `Zeta23` (Alpöge–Furman) proves, for Mathlib's `riemannZeta`, unconditionally and
  with multiplicity: `N₀ˢ(T,2T) ≥ (2/3 − ε)N(T,2T)` (c = 2 rank–trace certificate) and, with the
  Montgomery–Taylor window, `N₀ˢ ≥ (HD(1) − ε)N`, `HD(1) = 2 − 1/c₁* = 3/2 − 2^{−1/2}cot 2^{−1/2} = 0.6725…`.
  As cited in `RHTower/Zeta23OffLineMultipleExclusion.lean`, `RHTower/ZetaOffLineMomentMontgomeryTaylor.lean`.
- Mechanism (docstrings of `RHTower/Zeta23TheoremASpectralSlack.lean`, `Zeta23OffLineMultipleExclusion.lean`):
  sample the Weil explicit formula at the zero ordinates to get a "hat-unit Gram matrix" `Â = P + Q`, `P ⪰ 0`
  from critical zeros, `Q` from off-line pairs `{ρ, 1−ρ̄}`. The explicit formula computes `tr Â` and `‖Â‖_F²`
  (prime side needs bandwidth `λ ≤ 1`, i.e. `X = e^L ≤ T`). A rank–trace inequality
  `2c tr Â − ‖Â‖_F² ≤ Σ_{on-line} k_c(m) + c²·p` then counts simple critical zeros. [D]
- `IncommensurableGaborPinching.simple_critical_proportion_ge_67250071`: for all large `T`,
  `(0.67250071 − ε)N(0,T) ≤ N₀ˢ(0,T)`; `beyond_HD_one_simple_critical_cumulative` gives `HD(1) + 10^{−8}`.
  `IncommensurableGaborPinching/CriticalLineZeroProportion.lean:903, 1042` [D].
- `four_fifths_critical_ordinates`: at least `(4/5 − ε)` of the distinct zero ordinates in `(T,2T]` carry a
  critical zero; `2HD(1)/(1+HD(1)) = 0.8042…` at Montgomery–Taylor. `RHTower/Zeta23CriticalOrdinateCensus.lean` [D].
- `simple_or_critical_optimal`: at least `1 − (1−HD(1))/(3/2+√2) − ε = 0.8876…` of zero copies are simple or
  critical (level `c = 2+√2` is optimal among rank–trace levels). Same for every primitive Dirichlet `L(s,χ)`.
  `RHTower/Zeta23SimpleOrCriticalOptimal.lean`, `Zeta23DirichletSimpleOrCriticalOptimal.lean` [D].
- Off-line multiple zeros: `(HD(1) − ε)N + M_off ≤ N₀ˢ`; `S_off + 2M_off ≤ (1 − HD(1) + ε)N`.
  `RHTower/Zeta23OffLineMultipleExclusionMontgomeryTaylor.lean` [D].
- Dichotomy: in every large dyadic window either `N₀ ≥ (3/4)N`, or at least `(HD(1) − 1/2 − 1/A − ε)N` simple
  off-line zeros lie within `A/log T` of the critical line. `RHTower/Zeta23SimpleOffLineNearLine.lean` [D].
- Off-line first moment: `Σ_{0<Im ρ≤V} m(ρ)(Re ρ − ½) ≤ (66/1000)V` for large `V` (Selberg mollifier length
  `U^{21/50}` plus the Montgomery–Taylor density). `RHTower/ZetaOffLineMomentMontgomeryTaylor.lean` [D].
- Spectral slack of the two-thirds certificate: the rank–trace step discards
  `S(T) = 2 tr Q₋ + Σ_{q>0}(q−2)² + Σ(p − 1 − m)²`. An isolated off-line pair at displacement
  `a = (β−½)log T` gives a block with eigenvalues `m(g+1)`, `−m(g−1)`, `g ≥ 1` growing with `a`. An on-line
  count near the bound forces a nearly orthonormal on-line frame, i.e. ordinates near a lattice of spacing
  `2π/L`. `RHTower/Zeta23TheoremASpectralSlack.lean` (`thmA_lam_spectralSlack`, `H(λ) = 2 − 1/λ − λ/3`) [D].
- Bandwidth: the validity bound `λ ≤ 1` of the window is used only on the prime side; all zero-side inputs hold
  for every `λ > 0`. `RHTower/Zeta23FamilyBandwidth.lean` [D].
- Derived: `≥ HD(1)` of the zeros of `ξ'` are critical (Rolle); Speiser deficit `≤ (1−HD(1))/2 + ε`;
  `≥ HD(1) − r²` simple critical zeros with no other zero within `r/log(T/2π)`; horizontally isolated at scale
  `5/(2 log(T/2π))`. `RHTower/XiDerivCriticalLineProportion.lean`, `SpeiserDeficitTwoThirds.lean`,
  `SeparatedSimpleZeros.lean`, `HorizontallyIsolatedSimpleZeros.lean` [D].

## G3. Where the explicit-formula census stops: bandwidth one

- TTPC: a band-limited test on `[−L, L]`, `L = λ log(T/2π)`, gives a Gram whose normalized Frobenius norm is
  `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F(α)dα`; certified proportion `2 − κ`. For `λ ≤ 1` Montgomery–Vaughan kills every
  off-diagonal prime pair and `κ = 1/λ + λ/3`, minimum `4/3` at `λ = 1`: proportion `2/3`
  (`ArithmeticCastelnuovoSeveri.subthreshold_cert_le_two_thirds`). `TransThresholdPairCorrelation/README.md` §2 [D].
- Beyond `λ = 1` the only new term is the **signed correlation of close prime pairs** `|log(n/m)| ≲ 1/T` (coalescent
  band). At `λ = 4/3`, `3/4` needs `primeSurplus ≤ (1/18 + o(1))(aL)²Tℓ₁/2π`, i.e. `∫_1^{4/3}(4/3−α)F(α)dα ≤ 1/9`
  (`frobeniusFormFactor_four_thirds_le_five_fourths_iff`). Assembled certificate:
  `N₀*(T,2T) ≥ (29/36 − ε)N − coalescentSurplus` (`zeta_coalescent_certificate_four_thirds`). [D]
- Calibration at `4/3` (`calibration_five_models_four_thirds`): Hardy–Littlewood/GUE surplus `−1/144` (meets budget,
  gives `13/16`); uncorrelated `0`; Poisson without repulsion `+1/16` (fails); unsigned additive sieves need
  `Υ ≤ 8/9` (impossible). Barriers: positive spectral majorants miss by `8/3` (`fejer_shifted_bound_gap`); higher
  moments are capped at `kλ ≤ 1` (`higherMoment_rudnick_sarnak_cap`). [D]
- Reduction of the open input: proper prime powers cost `O(T^{−1/3+η}N)`; `p = 2` has no coalescent partner;
  only odd primes at even shifts remain; the actual sum = parity-locked Ramanujan stabilizer model + **centred
  stabilizer discrepancy** (`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`). The model transfers
  to the negative Ward–Mertens repulsion `−Ω̂(0)Σ_{q odd}μ²(q)/φ(q)`. The discrepancy is the open input. [D]
- The corpus's only prime-pair inputs are upper-bound sieves (`RHTower.Sieve.sum_card_primePair_le_sharp`,
  `TransThresholdPairCorrelation` 2-adic parity halving `sum_card_primePair_le_parity_unrestricted`). [D]
- Overlap coordinates: `bandwidth X T = 1 + log(overlap X T)/log T`, `overlap = X/T`
  (`SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean:48`) [S]. The complete-Weil overlap `c = N/T` is the
  super-Nyquist factor of the same bandwidth parameter.

## G4. The complete Weil matrix: fixed overlap versus the RH schedules

- `completeWeilMatrix φ c N = normalizedFullWeilHorizonMatrix (atomDilate φ (c/N)) N`; its quadratic form is the
  literal `weilQuad` of the atomic test (`completeWeilMatrix_inner_eq_weilQuad`).
  `RenormalizedArithmeticPotentialTheory/TheCompleteWeilMatrixHasAnExactErrorDecomposition.lean:24,117` [S].
- Fixed overlap, general profile: for every `C²` profile supported in `[0,1]` whose Fourier transform has no real
  zero, and every fixed `c > 0`, the complete Weil matrix is eventually positive definite
  (`eventually_noRealZero_completeWeilMatrix_posDef`). Inputs: Gamma reserve, defect reserve, conductor floor
  `(2/M)∫_{t>c}|φ̂(2πt)|²`. `CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean` [D].
- Uniform bounded overlap: for every `K`, one horizon works for all `c ∈ (0, K]` (tilted spline,
  `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap`). [D]
- Growing overlap on fixed finite conductor packets: `c ≤ (log N)^A`, `A < 1/48`, energy `≥ (const/c⁷)Σa_m²`
  (`eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap`). [D]
- RH schedules: tilted spline `c_N = 2(log N)^α`, `α > 1/4` (`riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log`);
  general `C²` profile under `OverlapGrowthTwo` (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`) [S];
  `dcProfile r`: `c_N = (log log N)^α`, `α > 1 + 1/r` (`riemannHypothesis_iff_dcProfile_nonneg_loglog`) [D].
- Denjoy–Carleman rate: for any `C^∞` unit-mass profile vanishing off `[−1,1]` with
  `∫|φ^{(q)}| ≤ A B^q q!(log(q+3))^{2q}`, RH ⇔ for every `K ≥ 1` the atomic families at overlap
  `K·L(log L)²`, `L = log log N`, are eventually nonnegative (`riemannHypothesis_iff_forall_bounded_rate`); one
  fixed `K` already gives Weil positivity on every test supported in `[−R,R]` with
  `24 e B_φ ⌈1 + e^{2R+2}⌉ < K` (`nonneg_of_atomicFamilies_nonneg_of_rate`), window radius `≈ ½ log K`.
  `TransMetzlerWeilPositivity/ABoundedOverlapRateSeesASemilocalWindow.lean:298,439,458` [S].
- The Steklov DC profile is an iterated box average; `TheSincProductProfile.lean` builds the infinite box
  convolution (Fourier transform a product of `sinc` factors, all zeros real) with
  `∫|∂^q| ≤ 4·12^q q!(log(q+3))^{2q}` [D].
- Index along schedules: `hermNegIndex` of the atomic Gram at the DC schedule tends to `κ(K_ζ)` = number of right
  zeros (`dcProfile_atomicGram_reaches_index`, `EffectiveArithmeticHodgeTheory/TheExplicitSchedulesReachTheIndex.lean:755`) [D];
  at every fixed overlap the index is `0` unconditionally. Fixed-overlap positivity has no zero-side consequence:
  the isolated tempered pair fails at every `c` (`isolatedPairConfig_atomic_negative_every_ratio`) while ζ passes
  whatever its off-line zeros are.

## G5. Weil positivity on the nonnegative blind cone is a short-window inequality

- `WindowPositive` := `|A(0)|‖h‖² ≤ J(h) + 2P(h)` for every bounded measurable `h ≥ 0` vanishing off `(0, log 2)`
  (jump energy with `archLevyDensity`, pole energy with `cosh`). It implies Weil positivity only for nonnegative
  prime-blind tests (`weilArchRe_nonneg_of_primeBlind`); such tests have support of measure `≤ log 2`, so their
  autocorrelation never reaches a node `log n`. No corpus theorem connects this cone to RH.
  `RHTower/PrimeBlindNonnegativeConeReduction.lean:1–51, 236` [S].

## G6. Mechanisms that certify only the boundary line

- Automorphic a priori information (Godement chamber, Maass–Selberg, holomorphy on the closed positive chamber)
  certifies exactly `{Re ρ ≥ 1}` (`certified_closedChamber`); the Godement chamber `{Re ρ > 2}`. Entirety of a
  cuspidal loop Eisenstein series certifies nothing about zeros of `Ξ` (`pole_iff_zero_of_mul`). Polar confinement of
  the affine Weyl sum ⇔ the lower square-root count (`polarConfinement_iff_lowerCount`); the golden datum passes
  every other test. `RHTower/InfiniteSymmetry/*.lean` [D].
- MPG: PD + integer divisor + simple pole + isolation force `ζ(1+it) ≠ 0`; `ζ(s)Φ(s+κ)` keeps all four invariants
  and vanishes inside the strip (`interior_zero_invisible`). (opus-reboot-facts F8, statements re-located.)

## G7. Heat flow: zero margin on the zero side

- `newmanConstant_nonneg : 0 ≤ newmanConstant`; `not_real_rooted_of_neg`: for `t < 0`, `H_t` has a nonreal zero.
  `RHTower/DeBruijnNewmanConstant.lean:63`, `RHTower/DeBruijnNewmanNonnegative.lean:588` [D].
- `newmanConstant_lt_eighth` (Ki–Kim–Lee, `Λ < 1/2` in standard normalization), by a barrier-zero velocity argument.
  `RHTower/DeBruijnNewmanStrictBound.lean` [S].
- `le_newmanConstant_of_offLine_zero`: an off-line zero of depth `≥ δ₀` at height `γ ≥ t₁` gives
  `Λ ≥ kklDetectionRate δ₀ / log γ`. `newmanConstant_le_half_sq_zetaZeroWidth`: `Λ ≤ Θ²/2`. `RH ↔ Λ = 0`. [D]

## G8. Corpus census (grep over `formal/GaloisForLFunctions`)

- 53,234 Lean files, about 498,000 `theorem`/`lemma` declarations. `RHTower` holds 29,311 files (17,386 at top
  level; subfolders ThetaCusp 3,980, Sieve 3,084, Deninger 1,643, CCM 1,272, Suzuki 936, Hedenmalm 410,
  RiemannGaussian 381) and `HTGeometry` 18,918; neither has a README.
- Declarations named `*riemannHypothesis_iff*`: 1,718; named `*riemannHypothesis_of*`: 1,150.

## G9. Anatomy of the fixed-overlap positivity proof (CACT/RAPT/SAHT, proofs read)

- Assembly `exists_tiltedUnitSpline_completeWeil_eigenvalue_floor` uses exactly three inputs
  (`eventually_completeWeil_eigenvalues_ge_of_reserve_quasimodes`,
  `CriticalArithmeticCorrelationTheory/MacroscopicOverlapSpectralAssembly.lean:104`): (i) a reserve
  `a‖x‖² + β·D_N(x) ≤ W_N(x)`, `β > 0`; (ii) for each conductor `m`, `‖W_N r̂_m − E_m r̂_m‖ → 0` for the
  normalized Ramanujan vector `r̂_m`; (iii) a floor `e ≤ E_m` for every `m`. "No inequality about the size of
  `c` is used." [S]
- Capture (`exists_finite_ramanujan_approximation_of_poleDefect_le`,
  `RenormalizedArithmeticPotentialTheory/BoundedPrimeDefectHasFiniteRamanujanApproximation.lean:22`): unit vectors
  with `D_N ≤ K` lie within `η` of the span of the Ramanujan profiles indexed by the divisors of
  `primeValuationBoxModulus P L`, with prime threshold `P > exp(2C(K+1)/η)` and valuation cap
  `L > 2·tail(P)(K+1)/η`. Mechanism: variation along fibres of primes `≥ P` costs only `C/log P` times the defect;
  the conditional mean on the `P`-smooth part with bounded valuations is a gcd profile, hence a finite Ramanujan
  sum. The set is independent of `N` and of the vector. [S]
- Separated decomposition (`completeWeilMatrix_eq_decomposition`, needs `c/N < atomSpacing N`):
  `W = (log N + finitePart(φ,c) − γ + selfError)·I − P_N + center(poleShift) − crossError + poleError`,
  `P_N(m,n) = Λ(n/m)(n/m)^{−1/2}`. Through touching the literal non-ratio prime matrix is added with a negative
  sign; at width `1/N` the only non-ratio pair is the boundary star `(N, N+1)` (`small_integer_log_gap_forces_boundary`). [S]
- Quasimode residual rate (`exists_completeWeil_completedConductor_residual_horizon_bound`,
  `CriticalArithmeticCorrelationTheory/CompleteConductorResidualsRetainTheirHorizonDecay.lean:82`): for fixed `m`,
  `c ≥ 1`, `N ≥ 4(e+3)²c²`: `‖W r̂_m − E_m r̂_m‖² ≤ K_m(c⁵/log N + c¹⁰(log N/N)²)`. [S]
- Origin of the `1/log N`: the pure prime part satisfies `‖P_N r̂_m − (log N − E^adj_m) r̂_m‖² ≤ C/log N` because the
  unnormalized residual is bounded uniformly in `N` (`exists_uniform_ramanujanPrimeResidual_family_bound`,
  `SignedArithmeticHodgeTheory/TheArithmeticResidualBudgetIsUniformInTheHorizon.lean:166`). That budget is the
  Mertens remainder `A(y) − log y + γ` at `y = ⌊N/n⌋`, enveloped by `C/(1 + log y)`
  (`exists_primeMertensRemainder_log_envelope`, from the `exp(−c√log y)` Mertens deviation) and summed against a
  summable Wiener kernel. The normalization `‖r_m‖² ≍ log N` turns an `O(1)` absolute residual into the
  relative `(log N)^{−1/2}`. The budget is dominated by small `y`, i.e. rows `n` near the horizon `N`. [S]
- Replacement errors (`WeilReplacementErrorsHavePolynomialCost.lean`): pole and separated-cross errors
  `≤ C c⁴/log N`, center residual `≤ C c²/log N`, self error `≤ C c²/N²` on `r̂_m`. [D]
- Ground state (`TheCompleteWeilGroundStateIsThePole.lean`): the completed energy floor is attained at conductor 1;
  exactly one eigenvalue lies below the midpoint of the gap; its line captures the normalized pole vector. Bottom of
  spectrum → `E(c) = (2/M)Σ_{k≥1}(1/k)∫_{kc}^∞|φ̂(2πt)|²dt`, which → 0 as `c → ∞`
  (`TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean`). [D]
- Tilted spline floor `E_m(c) ≥ (2·const/M)c^{−7}` for every `m` (`tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor`);
  Gamma reserve at growing overlap `archForm ≥ (κc^{−7}log N − bc)(c/N)MΣx²` (`archForm_atomicTest_ge_growing`). [D]
- Critical overlap (`TheCriticalOverlapIsLogLogTimesLogSquared.lean`): for a log-DC profile `|φ̂(ξ)| ≤ Aμ_B(2π|ξ|)`,
  `log(1/μ_B(c)) ≍ c/(log c)²`; `c*_N` := least `c ≥ 1` with `μ_B(c)² log N ≤ 1`, so `c*_N ≍ L(log L)²`. "The tail
  energy, which is both the margin of the complete Weil form and its synthesis error, equals the Weil weight
  `1/log N` there." RH ⇔ every bounded multiple `K c*_N` is eventually nonnegative
  (`riemannHypothesis_iff_forall_critical_multiple`); one `K` gives Weil positivity on tests supported in `[−R,R]`
  when `24eB⌈1+e^{2(R+1)}⌉ < K/(32e)` (`nonneg_of_critical_multiple`). [D]
- `TheFixedProfileReachesAnIteratedLogEndpoint`: RH receiver at `L(log L)²log log L` for the Steklov profile;
  "improves the synthesis requirement; it does not prove positivity of the actual complete form". [D]

## G10. Bounded-parameter positivity versus visibility of off-line zeros

- Archimedean domination at bounded aperture (`exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq`,
  `DilutionCrystallizationPincer/ArchimedeanDominationOfDilutedVisibility.lean:83`): for every `C²` test `f`
  supported in `[−a, a]` with `∫|f|² > 0` there is `Ξ` with `∫|f|² ≤ Re W_ζ(S_ξ f)` for all `|ξ| ≥ Ξ`. The bound is
  `Re W_ζ(S_ξ f) ≥ (log(1 + π|ξ|/4) − horizonExponent(e^{2a}) − 2·pairEnergy)∫|f|² − B²/(8(1+π|ξ|))`
  (`zetaZeroConfig_re_W_heightShift_pos_of_dominance`): the Gamma density `log|ξ|` beats every prime term of a
  bounded-aperture test. No hypothesis on zeros. [S]
- Visibility of diluted off-line crystals (`exists_diluted_pattern_visibility_constants`,
  `DilutedPatternAndCrystalVisibilityLaw.lean:357`): a `P`-pair periodic off-line pattern of period `2π/ℓ` and depth
  `≤ d_max` on an on-line background of density `L/2π` makes some test supported in `[−a,a]` negative once
  `2Pℓ + 2L < cℓ e^{d_max kℓ}` with `kℓ < 2a`: visibility at aperture `a ≍ (1/2d_max) log(L/ℓ)`. For a uniform
  crystal, modes `m ∉ Pℤ` vanish identically and modes `kP` align with norm `2P cosh(δkPℓ)`
  (`patternSymbol_crystal_dichotomy`). [S/D]
- Single-height forcing (`odd_sector_nonneg_forces_offLine_companion`,
  `ArithmeticPolarization/TheForcingHalfOfEllipticLocalization.lean:63`): for an off-line zero `ρ₀` of depth `δ`,
  nonnegativity of `W` on the twisted sinh detector at aperture `a` forces another off-line zero within `R` of
  `Im ρ₀` once `384A₀ log(|γ|+3)·(2a cosh(δa)·poly(a))²(1 + e^a/(1+R)) < 2(w(wa)^{5/2} sinh²(δ(a−2w)))²`, i.e. once
  `e^{2δa}` beats `log γ` up to polynomial factors in `a`. [S]
- Krein–Langer side (HKT, proofs read): the orbit kernel `K(u) = W_Z(f, f(·−log u))` on `ℚ_{>0}` is the exponential
  sum `Σ_ρ u^{ρ−½}W_ρ(f,f)` (`W_shiftTest_shiftTest`); its index equals the number of right zeros `f` sees for any
  tempered configuration `Z` (`negIndex_orbitKernel`). The proof uses of `ℚ_{>0}` only that its log-scales are dense;
  two primes suffice because `log p/log q` is irrational (`denseShifts_twoPrimeLattice`).
  `HeckeKreinToeplitz/TheHeckeOrbitKernelOfAZeroConfiguration.lean` [S].
- "A positive part never pays a pair" (`negIndex_add_sum_pairKernel_eq`, `HyperbolicPairsAndTheIndexFormula.lean`):
  on the family `u^d, u^{N+d}` the pair terms sum to `−2Σ|ω_j||w_j|^N|a_j|²` while a positive-definite part is at most
  `p(1)(Σ|c|)²`, bounded in `N`. The lower bound is a growth argument along unbounded powers. [D]
- Finite index is Lindelöf-deep (`lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top`):
  finitely many off-line zeros ⇒ LH and a zero-free half-plane `Re s > ½ + α`, `α < ½`. `κ(K_ζ)` is even; RH ⇔ `κ ≤ 1`.
  `HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean` [S].
- Pole on a tower is one hyperbolic plane; tower index and `Arch − Prime` index differ by at most one
  (`hermNegIndex_le_add_one_of_eq_on_ker`, `ThePoleIsTheOnlyRemovableHyperbolicDirection.lean`) [D].
- Stepanov compression (`compress_pairKernel`, `isPosDefKernel_compress_iff`): compressing by `P = Σp_αδ_{y_α}`
  multiplies a pair weight by `P̂(χ)·conj P̂(χ†)`; PD iff `P̂` vanishes at one character of every pair; on `ℚ_{>0}`
  `P̂` is the Dirichlet polynomial `Σp_α y_α^s` at `s = ρ − ½`. [D]

## G11. Realizations (ART, proofs read)

- Commutative realization (disjoint loops of length `log p`): `exp Σ_n tr(L_sⁿ)/n = ζ(s)` on `Re s > 1`; eigenvalues
  `p^{−s}` of modulus `≤ 1/2` on `σ ≥ 1`; trace class iff `Re s > 1`; the pole is a nuclearity pole
  (`commutative_pole_is_nuclear`). Free realization (full shift on primes): zeta `(1 − P(σ))^{−1}`, spectral pole at a
  unique `σ* ∈ (1,2)` (`free_pole_is_spectral`). `ArithmeticResonanceTheory/TheTwoRealizationsOfThePrimes.lean` [S].
- Additive (locally constant roof) prime-length shifts: each symbol has at most one first-return word, since two
  concatenate to an orbit of exponentiated length `pq` (`firstReturn_unique`); the full shift is not prime-length
  (`not_isAdditivePrimeLength_full`). `AdditiveRealizationsAreCommutative.lean` [S].
- Hölder prime-length systems: along a cycle family `u^n v`, `p(n+1) = a·p(n)·e^{δ_n}`, `|δ_n| ≤ 2Cθ^{nL}/(1−θ)`
  (`abs_familyStep_le`); eventually prime members force `a·θ^L ≥ 1` (`one_le_mul_pow_of_cycleFamily`); at fixed points
  `θ·e^{φ(a^∞)} ≥ 1` (`one_le_exp_mul_of_isPrimeLength`). Super-conformal distortion makes `p(n+1) = a p(n)`
  eventually (composite); conformal expansions `a^n ε_n → A` give an eventual affine recurrence, which primes never
  obey (`not_eventually_prime_of_conformal_expansion`, `not_eventually_affine_recurrence`: modulo a member `ℓ`, the
  affine map is a permutation of `ZMod ℓ`, so `0` recurs). [D]
- Realization ⇒ strip (`riemannZeta_ne_zero_of_holderRealization`): a Hölder suspension of a mixing SFT with
  `ζ = exp Σ Z_n/n` on `Re s > 1` gives `ζ ≠ 0` on `Re s > 1 − ε`, because Ruelle–Pollicott makes the dynamical zeta
  the reciprocal of a function holomorphic there (`exists_holomorphic_reciprocal`, `HTGeometry/SymbolicRuellePollicott.lean`);
  identity theorem with `(s−1)ζ(s)F(s) = s − 1`. Zeros of ζ are then not resonances. [S]
- Even realizations: `graphZeta · det(1 − M) = 1` far right, `det(1 − M)` entire, so a finite graph zeta has no zeros;
  `ζ ≠ graphZeta` because `ζ(−2) = 0` (`riemannZeta_ne_graphZeta`). Virtual realizations
  `det(1−M⁻)/det(1−M⁺)`: both determinants are exponential polynomials with real frequencies, which vanish on a real
  progression only if identically zero (`eq_zero_of_vanish_on_progression`); the trivial zeros `−2(k+1)` then kill
  the odd determinant (`riemannZeta_ne_virtualRealization`). `EvenRealizationsHaveNoZeros.lean`,
  `TheArchimedeanPlaceForbidsFiniteVirtualRealizations.lean` [S].
- Amplifiers: rate = depth (`norm_le_of_eventually_norm_le`); moments lose a root; a fixed loss gives the sharp bound
  and kills the pole coefficient; an envelope loss `e^{2kλ}` gives `|α| ≤ Be^λ`, attained. Brauer families at level `k`
  on `r` phases have `≥ C(r+k−1,k)` members; the cost `C(r+k−1,k)^{1/k} ≥ r/k`; over ℤ at scale `y`, `r = π(y)`.
  `TheAmplifierLaw.lean`, `OrthogonalityAmplifiersAreTrivial.lean` [D].
- Oscillation (relative Dolgopyat) fails on finite additive realizations (Dirichlet simultaneous approximation) and
  on the free realization (`P(σ+it)` returns to `P(σ)`). `OscillationFailsOnAdditiveRealizations.lean` [D].

## G12. The classical analytic engine inside `RHTower/Sieve` (unconditional)

- Vinogradov–Korobov: `ζ(β+iγ) ≠ 0` for `γ ≥ γ₀`, `β > 1 − (log γ)^{−2/3}(log log γ)^{−5/3}/10⁸`
  (`riemannZeta_ne_zero_vinogradovKorobov`, `RHTower/Sieve/VinogradovKorobovZeroFree.lean:373`) [D].
- Guth–Maynard Theorem 1.1 (large values: `|W| ≤ C T^ε(N²/V² + N^{18/5}/V⁴ + T N^{12/5}/V⁴)` for 1-separated `W`
  where `|Σ_{N<n≤2N} b_n n^{it}| ≥ V`) is a proved theorem, `guthMaynardLargeValuesBound_holds`
  (`RHTower/Sieve/GuthMaynardTheoremOneOne.lean:184`; statement `GuthMaynardLargeValuesStatement.lean:23`) [D].
- Consequences: zero density `#zeroHeightBox(σ,T) ≤ D(1+log T)^B T^{(30/13+ε)(1−σ)}`; primes in every interval
  `(x, x+x^α]`, `α > 17/30`, with `ψ(x+h) − ψ(x) ∼ h` uniformly for `x^α ≤ h ≤ x/2`
  (`guthMaynard_thirtyThirteenths_and_seventeenThirtieths_window`,
  `ReflectiveDirichletPolynomialS2/ShortWindowDispersionAtSeventeenThirtieths.lean:55`) [D].
- In the balanced regime `Q ≍ P`, power saving in short windows `⌈Q^α⌉` for the Möbius row and for the prime row are
  each equivalent to quasi-RH `zetaZeroAbscissa < 1` (`moebius_and_prime_powerWindowSaving_iff_quasiRH`) [D].
- Other machinery present: Ingham fourth moment and mollifier second moments, Levinson linear mollifiers,
  Barban–Vehov, Matomäki–Teräväinen Type I/II prime amplifiers, Heath-Brown sparse mean values, Kloosterman sums,
  upper-bound sieves for prime pairs. `RHTower/Sieve` has 3,084 files and two `riemannHypothesis_iff` declarations. [D]
- Fixed-σ density: for `σ > ½`, the zero count with `Re ≥ σ` in a window of length `≍ U` is `≤ ε(T₂ − T₁)`
  (`eventually_zeroCount_fixedSigma_le`, `RHTower/ZetaFixedSigmaDensity.lean:151`) [D].

## G13. Numerical checks (Python, not Lean; scripts in `computations/2026-10-30-reboot-final-checks/`)

- `HD(1) = 3/2 − 2^{−1/2}cot 2^{−1/2} = 0.6725007037`; `2HD/(1+HD) = 0.8041858`; `1 − (1−HD)/(3/2+√2) = 0.8876200`.
- The TTPC formula `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F(α)dα` with the GUE form factor (`F(α) = α` on `[0,1]`, `1` beyond)
  gives the certified proportion `2 − κ = 1 − 1/(3λ²)` for `λ ≥ 1`: `13/16` at `4/3`, `8/9` at `√3`, `0.9967` at `10`.
  Under full pair-correlation knowledge the rank–trace census tends to `1` and never reaches it.
- Prime part of the pole-vector residual, `‖P_N x − (log N − γ)x‖²` with `x_n = n^{−1/2}` (row `n` equals
  `n^{−1/2}(A(⌊N/n⌋) + log n − log N + γ)`, `A(y) = Σ_{t≤y}Λ(t)/t`): `0.0832` at `N = 10⁴, 10⁵, 10⁶, 2·10⁶`
  (constant), i.e. relative `0.0832/log N`. Share of this budget from rows with `⌊N/n⌋ < 2, 4, 16, 256`:
  `0.777, 0.879, 0.965, 0.998`. The budget is a boundary layer at the horizon, with an `N`-independent profile
  `R(y) = A(⌊y⌋) − log y + γ` (`R(1) = γ = 0.577`, `R(2) = 0.231`, `R(4) = 0.077`, `R(16) = −0.042`).

## G14. The coalescence blind spot of explicit-formula censuses (ACS, proofs/statements read)

- `doubleZeroBlockData s₁ d₂` (all zeros critical, `d₂` double) and `coalescedPairBlockData s₁ d₂` (`d₂` coalesced
  off-line pairs) have the identical summed Gram matrix `extremalDiag s₁ d₂` and the same `N`; every functional of
  `(Â, N)` valid on all normalized blocks certifies at most `(2 − κ)N` simple critical zeros there
  (`universal_gram_certification_classification`,
  `ArithmeticCastelnuovoSeveri/WhatAGramFunctionalCertifiesWithoutEffectivity.lean`) [D].
- Breaking it needs either the split `(P, Q)` (on-line Parseval slack `onSlack = ‖P‖² − c tr P + (c²/4) rank P`,
  negative-part credit `2 tr Q₋ > 0` iff `Q` not PSD) or `κ < 4/3` from prime correlations past `λ = 1`; the joint
  `(c = 2, c = 3)` functional equals `((7 − 3κ)/4)N` and is exactly `3/4` at `κ = 4/3` on the extremizer
  (`BreakingTheCoalescenceBlindSpotAndThreeQuarters.lean`) [D].
- Higher inertia: the blind-spot configuration has normalized moments `(1, 4/3, 2, 10/3)`; every polynomial weight
  of degree `≤ 3` certifies at most `2/3`; a quartic weight helps only with an upper bound on `κ₄`, and the quartic
  moment is within the correlation range only for `λ < 1/2` (cycle frequency budget `Σ|ξ_i| ≤ 4λ`). `3/4` needs
  `κ₄ ≤ 2503/768`; the sine-kernel `κ₄ = 13/4` gives `16/21` (`TheBlindSpotIsExactThroughThirdOrder.lean`) [D].
- Spectral-slack route to `HD(1)` is refuted for every bandwidth `λ < HD(1)` by the grid-dimension ceiling
  (`not_HD_one_zeroSideSlack_of_lt_HD_one`); off-line moment upgrade to `57/1000` given `3/4`
  (`CoalescentSurplusAndTransThresholdProportionLaws.lean`) [D].
- Universal reflection bound `2R(T₁,T₂) + N₀*(T₁,T₂) ≤ N(T₁,T₂)` without simplicity (`two_mul_sum_right_add_N0star_le`). [D]

## G15. Electrostatic (individual) forms with slack (AES, statements read)

- Transverse energy `𝓔 = ½Σ_{ρ≠ρ'}(Re ρ − Re ρ')²/|ρ − ρ'|²`: `𝓔 = 0` ⇔ RH ⇔ `𝓔 < 1`; `𝓔 < ∞` ⇔ finitely many off-line
  zeros; every off-line zero carries at least one quantum; `E(ρ) ≤ 16(C + log(|γ|+4))` unconditionally; RH ⇔ every
  unit window has energy `< 2` (`TheTransverseEnergyOfTheZeroDivisor.lean`, `TheEnergyOfAZeroIsLogarithmic.lean`,
  `QuantizationTurnsWindowsIntoPoints.lean`). "Averages, proportions and almost-every statements place most zeros
  near the line and exclude none: excluding an individual zero needs control below the zero spacing." [D]
- Field threshold: every off-line zero has within `C log γ` a locally rightmost terminal of depth `δ` with transverse
  field `≥ 1/(2δ) + cδ log(|γ_p|+4) ≥ √(2c log γ)`; RH ⇔ every right zero feels field `< √(2c log(|γ|+4))`
  (`exists_riemannHypothesis_iff_transverseField_lt_sqrt_log`, `TheFieldLawHasAThreshold.lean`). "The missing
  arithmetic input is an upper bound of this size, not an exact equilibrium." [D]
- External field law for `Re s > 1`: `Σ Λ(n)n^{−σ}cos(γ log n) ≤ Re(archFactor′/archFactor)(s) − m/(σ − β)` at the
  ordinate of a zero of real part `β` (`re_LSeries_vonMangoldt_le_at_zero_ordinate`, `TheExternalFieldIsAPrimeSum.lean`). [D]
- Large values at zero ordinates: `Σ_γ |F(γ)|² ≤ K log(A+R+1)(R + 8N(1+log N))(2 + log²N)Σ|a_n|²`; for powers of prime
  polynomials the aligned ordinates in `(T,2T]` at `V = η log T`, `X = (log T)^C` number `T^{1−1/C+o(1)}`
  (`LargeValuesAtZeroOrdinates.lean`, `HigherMomentsAtZeroOrdinates.lean`). [D]
- Electrostatics is blind to the archimedean twist `s ↦ ½ + λ(s−½) + iκ` (`transverseEnergy_affine`). [D]

## G16. Corpus-wide unification of the obstructions (SquareRootThreshold)

- `TheWallsMeasureOneZeroWidth.lean`: prime-side deficit primitive, Chebyshev mean square, Laplace and spectral band
  rates, Suzuki formation energy (`subpower at 1 + 2σ`), Möbius–divisor Abel energy exponents (`inf = 1 + 2Θ`), lag
  family negativity rate, CCM ground energy floor (`μ(A) ≥ −Ce^{2σA}` ⇒ `Θ ≤ σ`), heat (`Λ ≤ Θ²/2`), Balazard–Saias–Yor
  integral, prime-blind node criticality: all read `Θ = zetaZeroWidth = sup|Re ρ − ½|`. "The converse floor on `μ` from
  the width is not proved here; it is the graded form of the no-crossing problem." [D]
- CCM: `μ₀(B) ≥ −Ce^{εB}` for all `B` ⇒ every zero has `|Re ρ − ½| ≤ ε/2` (sharp form); attained top depth gives
  `μ₀(B) ≤ −c e^{2ΘB}/B³` (`CCMRestrictedWeilPolarBombieriYoshidaSharp.lean`). [D]

## G17. Deninger carriers (RHTower/Deninger, statements read)

- The resolvent-core package (centred generator with surjective off-axis resolvents and transpose eigenfunctionals at
  every `ρ − ½`) is equivalent to RH and is realized by the naive carrier of functions on the zero set; "the package
  carries no information beyond RH unless its carrier is built independently of the zeros"; a conformally scaled
  positive seminorm coexists with an eigencharacter of any off-line exponent
  (`exists_conformal_seminorm_with_offLine_character`). `DeningerResolventCoreIsRiemannHypothesis.lean` [D].
- Oriented Hilbert Hodge structure on `XiDivisorL2`: `J² = −1`, cup form alternating and nondegenerate; Frobenius
  commutes with `J` ⇔ RH (`DeningerArithmeticOrientedHilbertHodge.lean`) [D].

## G18. What bounded overlap does and does not separate

- Pole-free sign twins (completely multiplicative `±1`, bounded harmonic sums; Liouville, every cofinite flip) have a
  negative complete form above the Robin–Euler ratio `< 1` while ζ's matrix is PD at the same overlap
  (`liouvilleSelector_selective_of_signGauge`, `liouvilleSelector_selective_of_cofiniteFlip`,
  `CriticalArithmeticCorrelationTheory/FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip.lean`;
  mechanism: projection onto the pole hyperplane, `EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio.lean`). [D]
- A single-prime flip at `p` is invisible at every overlap `c ≤ (κ√p/log p)^{1/8}` and visible from `c ≍ (Kp)^{1/7}`
  (`tiltedUnitSpline_flip_threshold_polynomial`,
  `RenormalizedArithmeticPotentialTheory/TheFlipThresholdGrowsLikeAPowerOfThePrime.lean`). Conductor bound
  `E_m(c) ≤ (m/φ(m))E_1(c/m)`. [D]
- Fine towers (`ArithmeticKreinLangerTheory/FineTowersDecideEveryOrbitKernel.lean`): a kernel continuous in `log`
  whose Toeplitz forms are nonnegative on cyclic subgroups generated by `e^{s_n}`, `s_n → 0`, is PD
  (`hermQuad_nonneg_of_fine_zpowers`); the consecutive-ratio towers `⟨(n+2)/(n+1)⟩` qualify because
  `log((n+2)/(n+1)) → 0`; two primes qualify because `p^a q^b` has arbitrarily small positive scale. RH ⇔ PD on every
  consecutive tower (`riemannHypothesis_iff_zetaKernel_consecutive`). The proof uses only the scales tending to `0`. [S]

## G19. Addenda to G8 and G9

- Of the 1,718 `riemannHypothesis_iff…` declarations, 186 have a right-hand side that names the zero set or off-line
  zeros explicitly (`XiDivisorSupport`, `XiZeroCopy`, `NontrivialZetaZero`, `zetaZeroConfig.carrier`, `rightZeros`,
  `offLine`…; scan of the statement text up to `:=`). By folder: RHTower top level 153 of 1,186, RHTower/ThetaCusp 8 of 60,
  RHTower/CCM 0 of 77, RHTower/Suzuki 0 of 55, RHTower/Deninger 8 of 11. Objects defined from zeros inside other
  definitions are not detected by this scan. Example of a per-zero relabeling:
  `riemannHypothesis_iff_schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_zero` (`∀ rho : XiDivisorSupport, … = 0`).
- The qualitative quasimode chain of the fixed-overlap theorem uses Mertens' theorem: `tendsto_mertensSum_sub_log` and
  `tendsto_mertensSum_add_div_self` in
  `CriticalArithmeticCorrelationTheory/TheUpwardPrimeRowsRealizeTheCompletedShellCorrection.lean`, imported by
  `MacroscopicOverlapPositivityAtEveryOverlap.lean` through `TheUpwardPrimeWindowsCarryTheShellCorrection`. [S]
- `RHTower/Sieve` contains `VinogradovZetaGrowthBlocks.lean` and `VinogradovKorobovLogDeriv.lean` (growth blocks and the
  log-derivative step of the VK region). [D]

---

# K. The corpus condensed by object

Harvest: the module-docstring titles of all 3,934 programme modules outside `RHTower`/`HTGeometry`/vendors, the
23,457 `RHTower` titles filtered by content, and targeted `formal_tools.py research` queries; the decisive items were
read in source. Tags: [T] title-level (the module's own one-line statement), [D] docstring read, [S] statement and proof
read. Anchors are module paths relative to `formal/GaloisForLFunctions/`.

## K1. One invariant; growth equals depth
- Every growth rate in the corpus reads `Θ = sup|Re ρ − ½|`: deficit primitive, mean-square band, Laplace energy,
  Suzuki formation energy, Möbius–divisor Abel energy (`inf = 1 + 2Θ`), lag family, CCM ground energy
  (`μ₀(B) ≤ −ce^{2ΘB}/B³` when attained), heat time (`Λ ≤ Θ²/2`), window ceiling (`Θ ≤ θ* ≤ Θ/2 + ¼`)
  (`SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean`) [D].
- Growth exponent of a compact packet = depth of the zeros it sees (BSU [T]); orientation rate of a cycle = depth of the
  deepest zero it sees (AOG [T]); growth reads the depth of the deepest pair (HKT [T]); amplifier rate = depth (ART [D]);
  one Lefschetz sequence grows at the zero width (ACS [T]); the zero width is a Landau exponent (SRT [T]).
- One-sided suffices: a packet bounded on one side sees no deeper zero (BSU [T]); one-sided Lefschetz bounds at one or
  two primes are the zero-free strip (ACS [T]); each half of the count alone is RH (ASRP [D]); the global law is the
  one-sided square-root count (HKT [T]); RH ⇔ an inequality between nonnegative functionals on the nonnegative cone in
  Doob coordinates, sharp at the constant profile (`riemannHypothesis_iff_forall_nonneg_cone`, ACT [D]).

## K2. Bounded scale is blind
- Bounded-aperture tests are positive at large height: `Re W_ζ(S_ξf, S_ξf) > 0` once `log(1 + π|ξ|/4)` exceeds
  `horizonExponent(e^{2a}) + 2 pairEnergy(½, a) + O_f(1/|ξ|) = 10 + 68e^a + 2(sinh a − a) + …`, i.e. for
  `a ≲ log log|ξ| − 4.2` (`zetaZeroConfig_re_W_heightShift_pos_of_dominance`,
  `exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq`, `DilutionCrystallizationPincer/ArchimedeanDominationOfDilutedVisibility.lean`;
  `horizonExponent` at `RHTower/ZetaSymbolArchimedeanHorizon.lean:222`;
  `pairEnergy δ a = sinh(2δa)/(2δ) − a` at `SquareRootThreshold/IsolatedOffLinePairVisibilityLaw.lean:204`) [S].
- The isolated-pair price is per lag `v`, with tests supported in `[−(v/2 + w), v/2 + w]`; the on-line mass is
  `onLineMass Z β γ₀ = Σ_{Re ρ = ½} m_ρ |β̂(γ_ρ − γ₀)|²` (`SquareRootThreshold/IsolatedPairInArbitraryBackground.lean:49`),
  of size `≍ log γ₀` for ζ, so an isolated pair of depth `δ` hides only to aperture `≲ log log γ₀/(2δ)` [S].
- Unconditional Weil positivity of ζ through aperture `3/10`; `Re W_w ≥ (1/5000)∫|f|²` there for every prime weight `w`
  (`re_weilFullFunctional_ge_of_aperture_le_threeTenths`) [D]; window positivity up to `12/25` [D].
- At every aperture the negative index is at most `|lowGrid(a)| + 1`, and positivity holds once finitely many
  low-frequency values vanish (`negIndex_zeroGram_zeta_le_lowGrid`, `re_W_zeta_nonneg_of_lowGrid`, ACS) [D].
- The Weil margin is super-exponentially small: truncated Riemann kernel `f_L` gives
  `‖W(f_L,f_L)‖ ≤ Ce^{12L}e^{−πe^{2L−1/2}}‖f_L‖²`, with or without RH (`zeta_weil_margin_superexponential`) [D].
- Window-averaged positivity holds for configurations with off-line zeros; height averages are blind to small-variation
  clusters (SRT [T]); a bounded aperture range certifies no rate at all (SSIC [T]); finite-aperture positivity cannot
  decide (ASRP [T]).
- Fixed overlap of the complete Weil matrix: PD at every fixed `c`, margin = completed shell tail, critical overlap where
  margin = synthesis error = `1/log N` (G4, G9).

## K3. Detection is finite; exclusion must be uniform
- "A mechanism that fails is told so by a finite computation; a mechanism that succeeds must succeed everywhere at once"
  (`RefutationIsFiniteConfirmationIsNot.lean`) [D]; RH ⇔ no bounded-radius certificate refutes Λ's membership in the
  full Weil cone [D].
- Every off-line zero is visible at a finite aperture; finite off-line sets at a logarithmic aperture; an attained top at
  a lag logarithmic in the separation; near-top zeros of ζ at a polylogarithmic lag (SRT [T], SSIC [D]).
- Sparse test families decide RH: unimodular / even-odd / difference two-bump tests, every width, large dyadic prime
  windows, pole-free dyadic windows, one parameter (SRT [T]); `onLine_iff_polarFree_primeWindow_le_arch` [D].
- The Weil form determines the configuration; the lag family determines the configuration (SRT [T]).

## K4. What a counterexample must look like
- Hiding needs a crystal: an isolated pair of depth `δ` in on-line mass `M` hides only to lag `v ≤ arsinh(M/|Q|+1)/δ`
  (`theFloorsRequireACrystal`); only infinite off-line lattices sustain the floors; reach of a diluted lattice
  `a ≤ log((3L+ℓ)/ℓ)/(2δ) + ℓ/2`; aliasing is free below Nyquist `ℓ/2` and ends exactly there (`TheHidingLaws.lean`) [S/D].
- Crystallization hides: there are configurations `Z ⊆ Z'`, all of `Z'` off-line, with `Z` negative and `Z'` positive on
  every test of aperture `a ∈ (L/2, L]` — visibility is not monotone (`exists_offLine_superset_hiding`) [D].
- Hiding up to the threshold forces uniform depth and crystalline spacing (`uniform_crystal_of_hiding`); near-top zeros
  of ζ hide only in collapsed clusters; hiding needs near-top twins at every lag and loud twins; isolated twins of ζ
  cannot hide; twins are exponentially tight unless tripled; lag positivity forces close companions (SRT [T]).
- Shallow off-line copies (within `1/log T`) satisfy `Σ m_j² ≤ C T log T` and anti-clustering
  `Σ_{|γ_j−γ_k|≤K/log T} m_j m_k ≤ (C/8)(16+K²)T log T` (ShallowCauchyPrimeEnergy [D]).
- Census: either `≥ 3/4` critical or `≥ 17%` simple off-line within `A/log T`; off-line first moment `≤ 0.066V` (G2).

## K5. The primes are anti-crystalline
- Crystal gaps against Kronecker alignment: at a lag in a gap the crystal response is the positive constant `4L‖κ_w‖²`
  while ζ's prime phases (`loggedPrimes_linearIndependent`) align at some height, forcing negativity or exponential
  height escape (`crystal_gap_prime_torus_incompatibility`, DCP) [D]; Kronecker–Bohr prime-phase realization and
  exponential height escape (SRT [T]).
- `S(T)` (the Riemann–von Mangoldt remainder) is unbounded, from prime-torus oscillation (`rvmRemainder_unbounded`) [D].
- Two prime towers see every ordinate difference at polynomial precision (Baker); integrality alone gives `e^{−O(|Δ|)}`
  (ASRP [D]); two primes suffice for the Krein–Langer index because `log p/log q` is irrational (HKT [S]).
- Zeros of an exponential polynomial recur (ACS [T]); finite virtual realizations are impossible (ART [S]).

## K6. Torsion of the circle carries both sides of the explicit formula
- `I(m, mt) = φ(m)Λ(t)`: Λ is the intersection number of torsion orbits, a log-resultant of cyclotomic polynomials
  (`orbitIntersection_hecke`, AET) [D].
- Gauss's digamma theorem is the Fourier transform of the torsion energy on `μ_N`; the `log N` is the anomaly of `[N]`
  (`gauss_digamma_theorem`, AIT) [D]: the archimedean factor at rational points and the torsion are Fourier dual.
- Weil's prime kernel = renormalized limit of the positive gcd-twisted Abel torsion energy; the sign is lost exactly in
  the renormalization `log(1/(1−r))Σx²` (AET [D]).
- Torsion is the stable equilibrium of the circle (Fekete; energy `N log N` from `N^N`); "on the zero divisor equilibrium
  is computed and stability is the open sign" (AES [D]).
- Cyclotomic norm `≥ 1` gives a conductor-uniform floor; Ramanujan modes diagonalize affine unit averages and the full
  prime matrix (CACT/RAPT [D]).
- The finite prime chain has the spectrum of the integers: eigenvalues `→ log m + Σ_{p|m} log p/(p−1)`; top spectrum
  exhausted by the integers; gap `2 log 2` (RAPT [D/T]).
- "Torsion characteristics: where + and × meet" (AET [T]); finite intersection is gauge blind (AIT [T]).

## K7. Finite levels are positive; the limit loses the sign through a full-rank counterterm
- Survival law: positivity passes a scale limit exactly on the null cone of the counterterm; the cone is scheme-invariant
  (`quad_nonneg_of_regularized`, `survivalCone_eq_of_regularized`, RBG) [S/D].
- Torsion germ: counterterm = identity, survival cone `{0}` under every renormalization; archimedean lattice germ:
  rank-one `𝟙𝟙ᵀ`, survives on the polar-neutral hyperplane (`counterterm_rank_dichotomy`) [D].
- Coupling cannot lower the torsion rank; a partner pays at most `rank D` prime directions; the archimedean partner pays one
  (`TheCoupledSurvivalLaw.lean`) [D].
- Hecke cocycle `β(n,t) = log t − Σ_{p|t,p∤n} log p/(p−1)`, not a bounded coboundary; spacing regulator positive at every
  `ε`, covariant up to tame ramification, scalar counterterm, indefinite limit; horizon counterterm Hecke covariant on
  `p`-adic classes, tensor product of identity (torsion orbits) and polar projection (log scale) (AIT/RAPT [D]).
- "A covariant regulator whose counterterm has a nontrivial null cone is what the Hodge index would need"
  (`TheSpacingRegulatorRemovesTheAnomaly.lean`) [D].
- Self-intersection (discriminant) dominates the tower: the renormalized torsion form is negative definite above the
  second ladder level ("adjunction beats the tower") (AIT [D]).

## K8. The zeros meet arithmetic modes only at boundaries
- For the pole mode on `[1,N]`, the zero-side Dirichlet factors are exactly the Euler–Maclaurin boundary `−B_N`; "the
  zeros see the pole mode through the boundary of its horizon and through nothing else"; the pole parts give the Li
  charge `N/(ρ(1−ρ))`; the rest is Poisson-dual to the successor shells (`ThePoleModeMeetsTheZerosOnlyAtTheHorizon.lean`) [D].
- The zeros see every atomic vector through its Möbius horizons; the horizon charge is blind to the real parts of the
  zeros (`|P_a(s)P_a(1−s)| ≤ N(Σ|a_d|/d)²/|s(1−s)|`) (RAPT [D/T]).
- The quasimode residual of the complete Weil matrix is an `N`-independent `O(1)` boundary layer at the horizon (G9, G13).
- Every unconditional input lives at `Re s > 1` or on `Re s = ½` and is separated from the error by the strip; inside
  the strip only counts (`ContourCrossingObstruction.lean`) [D].
- The shells and the pole cancel on the top band: along `b + η·1_T` the joint `η`-coefficient
  `a₋a₊(H_N|T| + N S_T) − Σ_T b_n R(n)` is `O(G(log N + c + 1))` uniformly in `N`, while each term is `≍ Gcq log N`
  (`exists_abs_jointWitnessCoefficient_le`, `SuccessorShellArithmetic/TheShellsAndThePoleCancelOnTheTopBand.lean`) [D];
  integrality of the shift repays the logarithm (SSh [T]).

## K9. The successor enters only through the archimedean place
- Consecutive Hecke cycles meet through the archimedean density alone: `heckeIncidence k (k+1) = 0` and
  `archLevyDensity(log((k+1)/k)) = (k+1)√(k(k+1))/(2k+1)` (`TheSuccessorCollar.lean`, ACS) [D]; the successor connection
  is the archimedean gauge field (ALG [T]).
- An atomic archimedean spectrum blinds the successor; the successor sees only the continuous dilation spectrum; Weil's
  correlation carries no successor (`successor_blind_of_atomic`, APD) [D]; the successor is invisible at zeros (ACP [T]);
  the successor enters the count only modulo the square-root class (ASRP [D]).
- Yet ring structure (gcd(n,n+1)=1) is required: Beurling systems pass every multiplicative test (BVI, THIM class III,
  AKLT ladder, opus F3) [D].

## K10. Quantization
- Index even; RH ⇔ index `≤ 1`; transverse energy `≥ 1` per off-line zero, RH ⇔ `< 1` ⇔ window energy `< 2`; collision
  charge even; prime mass at the `√x` scale in even integer units `≤ 2 ord ξ` (BGG); the prime mean is quantized height by
  height (THIM [T]); below half damping local exponents are integers (THIM [T]); successor bias quantized by the conductor
  (SSA [T]); integer-valued PD ⇒ sign characters (APD/MPG) [D]; integrality forbids super-conformal distortion (ART) [D].

## K11. Inside the strip: statistics only
- Census 67.25%, 4/5 of ordinates, 88.76% simple-or-critical, blind spot, ceiling `1 − 1/(3λ²)` (G2, G3, G13, G14).
- Zero density `30/13`, VK, primes in `x^{17/30}` windows (G12); fixed-σ density `o(T)` [D].
- Zero density is a quadratic statistic: bounds counts, never individual locations (`ContourCrossingObstruction`,
  `CorrelationBoundsCountNotLocation`) [D].

## K12. Heat
- `0 ≤ Λ < 1/8`; for each `t > 0` only finitely many nonreal zeros of `H_t`, all real and simple beyond
  `2πe^{(1+√3/2+ε)/t}` (`riemannHeat_zeros_real_simple_sharp`) [D]; at height `t` the heat transfer is positive from
  `λ = 100/log|t|` (`exists_xiSliceHeatTransfer_pos_heat_over_log`) [D]; an off-line zero of depth `≥ δ₀` at height `γ`
  forces `Λ ≥ kkl(δ₀)/log γ` [D]; at negative time zeros come from an almost periodic Dirichlet-series model (G7).
- Heat repairs a polynomial with roots in a disc after time `32r/degree`; every finite head of `ξ` is heat-repaired at
  every large height (ALDG [T]); heat collisions count the index (HKT [T]).

## K13. Rigidity and the fakes
- Weil cone `{Λ}` or `∅`; pole weight forced; theta rigidity; pole-order-one completed positive systems are `ℝ^×ζ`
  (G1, opus F10, SBWF [T] "the simple-pole class is ζ").
- Λ-positive functions with the exact FE (and entire, pole order 2) have off-line zeros
  (`lambdaPositive_functionalEquation_not_criticalLine`, `lambdaPositive_entire_functionalEquation_not_criticalLine`) [D].
- Golden datum: integral zeta series, integral counts, FE pairing, Witt/λ-ring and Adams compatibility, upper count, PD
  vertical sections; fails unitarity, Bézout on its window surface, RR on its Rosati source cone, PD of the trace
  sequence, the lower count; has a real outer eigenvalue (AOT/ACS/AKT/APD/ACP [D]).
- Reality-sensitive unconditional tools exist (Jensen-polynomial discriminants); what they lack is decidability
  (`DiscriminantIsRealitySensitive.lean`) [D]; the Jensen polynomials of ξ satisfy Laguerre's inequality on the half-line
  (ALG [T]); the first sixty-eight Li coefficients are nonnegative (RHTower [T]).

## K14. Realizations and carriers
- Finite even/virtual realizations impossible (trivial zeros); additive ⇒ commutative; Hölder ⇒ strip; conformal
  excluded by affine recurrence (G11). Deninger carriers indexed by zeros carry nothing beyond RH; "a category with ζ as
  one member among many" unaffected (G17).

## K15. The 𝔽_q contrast
- Over `𝔽_q`: square-root cancellation is a count (orthogonality); the odd part is spectral and finite; Frobenius is
  conformal (factor `q`) while Hecke dilations over ℤ are isometric boosts; one tower suffices, two are needed over ℤ;
  Weil's theorem for curves is PD of the trace sequence on ℤ (SSA/ART/ALG/AKLT/APD [D/T]).
