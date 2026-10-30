# Reboot-final: mathematical facts read from the Lean corpus

Facts only. Each entry names its Lean anchor (path relative to `formal/GaloisForLFunctions/`).
[S] = statement and proof read (for long assemblies: the top-level proof and the named lemmas it combines). [P] = the
module's prose claims more than its Lean proves. [X] = the corpus states
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
  `SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean:389` [S]. The "prime-free" form needs the prime
  powers as the node set; only the weights disappear.
- Degree version: `eq_smul_vonMangoldt_of_weilPositiveDegree`: with pole weight `d > 0` the only positive
  weight is `d·Λ`. `RHTower/WeilConeDegreeTwinRigidity.lean:111` [S].

## G2. Unconditional zero-proportion engine (Zeta23 + RHTower census)

- [X] The pinned dependency `Zeta23` (Alpöge–Furman) proves, for Mathlib's `riemannZeta`, unconditionally and
  with multiplicity: `N₀ˢ(T,2T) ≥ (2/3 − ε)N(T,2T)` (c = 2 rank–trace certificate) and, with the
  Montgomery–Taylor window, `N₀ˢ ≥ (HD(1) − ε)N`, `HD(1) = 2 − 1/c₁* = 3/2 − 2^{−1/2}cot 2^{−1/2} = 0.6725…`.
  As cited in `RHTower/Zeta23OffLineMultipleExclusion.lean`, `RHTower/ZetaOffLineMomentMontgomeryTaylor.lean`.
- Mechanism (`RHTower/Zeta23TheoremASpectralSlack.lean`, `Zeta23OffLineMultipleExclusion.lean`; the corpus proofs
  assemble the external rank–trace core [X] with counting identities):
  sample the Weil explicit formula at the zero ordinates to get a "hat-unit Gram matrix" `Â = P + Q`, `P ⪰ 0`
  from critical zeros, `Q` from off-line pairs `{ρ, 1−ρ̄}`. The explicit formula computes `tr Â` and `‖Â‖_F²`
  (prime side needs bandwidth `λ ≤ 1`, i.e. `X = e^L ≤ T`). A rank–trace inequality
  `2c tr Â − ‖Â‖_F² ≤ Σ_{on-line} k_c(m) + c²·p` then counts simple critical zeros. [S]
- `IncommensurableGaborPinching.simple_critical_proportion_ge_67250071`: for all large `T`,
  `(0.67250071 − ε)N(0,T) ≤ N₀ˢ(0,T)`; `beyond_HD_one_simple_critical_cumulative` gives `HD(1) + 10^{−8}`.
  `IncommensurableGaborPinching/CriticalLineZeroProportion.lean:903, 1042` [S]. The `10^{−8}` comes from
  non-orthogonality: the Montgomery–Taylor kernel vanishes only on `(26/25, 43/40) ∪ (503/250, 256/125)`, whose
  sumsets miss both intervals, so no three simple critical ordinates of scaled span `≤ 3` are mutually orthogonal;
  `≥ N/625` disjoint triples give off-diagonal Frobenius energy `≥ 10^{−8}N` in the `c = 2, 3` seams.
- `four_fifths_critical_ordinates`: at least `(4/5 − ε)` of the distinct zero ordinates in `(T,2T]` carry a
  critical zero; `2HD(1)/(1+HD(1)) = 0.8042…` at Montgomery–Taylor. `RHTower/Zeta23CriticalOrdinateCensus.lean` [S].
- `simple_or_critical_optimal`: at least `1 − (1−HD(1))/(3/2+√2) − ε = 0.8876…` of zero copies are simple or
  critical (level `c = 2+√2` is optimal among rank–trace levels). Same for every primitive Dirichlet `L(s,χ)`.
  `RHTower/Zeta23SimpleOrCriticalOptimal.lean`, `Zeta23DirichletSimpleOrCriticalOptimal.lean` [S].
- Off-line multiple zeros: `(HD(1) − ε)N + M_off ≤ N₀ˢ`; `S_off + 2M_off ≤ (1 − HD(1) + ε)N`.
  `RHTower/Zeta23OffLineMultipleExclusionMontgomeryTaylor.lean` [S].
- Dichotomy: in every large dyadic window either `N₀ ≥ (3/4)N`, or at least `(HD(1) − 1/2 − 1/A − ε)N` simple
  off-line zeros lie within `A/log T` of the critical line. `RHTower/Zeta23SimpleOffLineNearLine.lean` [S].
- Off-line first moment: `Σ_{0<Im ρ≤V} m(ρ)(Re ρ − ½) ≤ (66/1000)V` for large `V` (Selberg mollifier length
  `U^{21/50}` plus the Montgomery–Taylor density). `RHTower/ZetaOffLineMomentMontgomeryTaylor.lean` [S].
- Spectral slack of the two-thirds certificate: the rank–trace step discards
  `S(T) = 2 tr Q₋ + Σ_{q>0}(q−2)² + Σ(p − 1 − m)²`. An isolated off-line pair at displacement
  `a = (β−½)log T` gives a block with eigenvalues `m(g+1)`, `−m(g−1)`, `g ≥ 1` growing with `a`. An on-line
  count near the bound forces a nearly orthonormal on-line frame, i.e. ordinates near a lattice of spacing
  `2π/L`. `RHTower/Zeta23TheoremASpectralSlack.lean` (`thmA_lam_spectralSlack`, `H(λ) = 2 − 1/λ − λ/3`) [S].
- Bandwidth: the validity bound `λ ≤ 1` of the window is used only on the prime side; all zero-side inputs hold
  for every `λ > 0`. `RHTower/Zeta23FamilyBandwidth.lean` [S].
- Derived: `≥ HD(1)` of the zeros of `ξ'` are critical (Rolle); Speiser deficit `≤ (1−HD(1))/2 + ε`;
  `≥ HD(1) − r²` simple critical zeros with no other zero within `r/log(T/2π)`; horizontally isolated at scale
  `5/(2 log(T/2π))`. `RHTower/XiDerivCriticalLineProportion.lean`, `SpeiserDeficitTwoThirds.lean`,
  `SeparatedSimpleZeros.lean`, `HorizontallyIsolatedSimpleZeros.lean` [S].

## G3. Where the explicit-formula census stops: bandwidth one

- TTPC: a band-limited test on `[−L, L]`, `L = λ log(T/2π)`, gives a Gram whose normalized Frobenius norm is
  `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F(α)dα`; certified proportion `2 − κ`. For `λ ≤ 1` Montgomery–Vaughan kills every
  off-diagonal prime pair and `κ = 1/λ + λ/3`, minimum `4/3` at `λ = 1`: proportion `2/3`
  (`ArithmeticCastelnuovoSeveri.subthreshold_cert_le_two_thirds`, arithmetic of `kfun λ = 1/λ + λ/3` [S]). The
  Montgomery–Vaughan reading is the README's (`TransThresholdPairCorrelation/README.md` §2) [P].
- Beyond `λ = 1` the only new term is the **signed correlation of close prime pairs** `|log(n/m)| ≲ 1/T` (coalescent
  band). At `λ = 4/3`, `3/4` needs `primeSurplus ≤ (1/18 + o(1))(aL)²Tℓ₁/2π`, i.e. `∫_1^{4/3}(4/3−α)F(α)dα ≤ 1/9`
  (`frobeniusFormFactor_four_thirds_le_five_fourths_iff`, arithmetic for `F(α) = α` on `[0, 1]`). Assembled certificate:
  `N₀*(T,2T) ≥ (29/36 − ε)N − coalescentSurplus` (`zeta_coalescent_certificate_four_thirds`). [S]
- Calibration at `4/3` (`calibration_five_models_four_thirds`): Hardy–Littlewood/GUE surplus `−1/144` (meets budget,
  gives `13/16`); uncorrelated `0`; Poisson without repulsion `+1/16` (fails); unsigned additive sieves need
  `Υ ≤ 8/9` (impossible). Barriers: positive spectral majorants miss by `8/3` (`fejer_shifted_bound_gap`); higher
  moments are capped at `kλ ≤ 1` (`higherMoment_rudnick_sarnak_cap`) [P]: the Lean takes `kλ ≤ 1` as a hypothesis and
  derives `λ ≤ 1/k ≤ 1/3`; the cap is not proved about ζ.
- Reduction of the open input: proper prime powers cost `O(T^{−1/3+η}N)`; `p = 2` has no coalescent partner;
  only odd primes at even shifts remain; the actual sum = parity-locked Ramanujan stabilizer model + **centred
  stabilizer discrepancy** (`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`). The model transfers
  to the negative Ward–Mertens repulsion `−Ω̂(0)Σ_{q odd}μ²(q)/φ(q)`. The discrepancy is the open input. [S]
- The corpus's only prime-pair inputs are upper-bound sieves (`RHTower.Sieve.sum_card_primePair_le_sharp`,
  `TransThresholdPairCorrelation` 2-adic parity halving `sum_card_primePair_le_parity_unrestricted`). [S]
- Overlap coordinates: `bandwidth X T = 1 + log(overlap X T)/log T`, `overlap = X/T`
  (`SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean:48`) [S]. The module states that "a fixed overlap
  greater than one still has limiting bandwidth one". The complete Weil matrix has horizon `N` and width `c/N`, i.e.
  length `N` at height `N/c` (inference from the definitions).

## G4. The complete Weil matrix: fixed overlap versus the RH schedules

- `completeWeilMatrix φ c N = normalizedFullWeilHorizonMatrix (atomDilate φ (c/N)) N`; its quadratic form is the
  literal `weilQuad` of the atomic test (`completeWeilMatrix_inner_eq_weilQuad`).
  `RenormalizedArithmeticPotentialTheory/TheCompleteWeilMatrixHasAnExactErrorDecomposition.lean:24,117` [S].
- Fixed overlap, general profile: for every `C²` profile supported in `[0,1]` whose Fourier transform has no real
  zero, and every fixed `c > 0`, the complete Weil matrix is eventually positive definite
  (`eventually_noRealZero_completeWeilMatrix_posDef`). Inputs: Gamma reserve, defect reserve, conductor floor
  `(2/M)∫_{t>c}|φ̂(2πt)|²`. `CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean` [S].
- Uniform bounded overlap: for every `K`, one horizon works for all `c ∈ (0, K]` (tilted spline,
  `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap`). [S]
- Growing overlap on fixed finite conductor packets: `c ≤ (log N)^A`, `A < 1/48`, energy `≥ (const/c⁷)Σa_m²`
  (`eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap`). [S]
- RH schedules: tilted spline `c_N = 2(log N)^α`, `α > 1/4` (`riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log`);
  general `C²` profile under `OverlapGrowthTwo` (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`) [S];
  `dcProfile r`: `c_N = (log log N)^α`, `α > 1 + 1/r` (`riemannHypothesis_iff_dcProfile_nonneg_loglog`) [S].
- Denjoy–Carleman rate: for any `C^∞` unit-mass profile vanishing off `[−1,1]` with
  `∫|φ^{(q)}| ≤ A B^q q!(log(q+3))^{2q}`, RH ⇔ for every `K ≥ 1` the atomic families at overlap
  `K·L(log L)²`, `L = log log N`, are eventually nonnegative (`riemannHypothesis_iff_forall_bounded_rate`); one
  fixed `K` already gives Weil positivity on every test supported in `[−R,R]` with
  `24 e B_φ ⌈1 + e^{2R+2}⌉ < K` (`nonneg_of_atomicFamilies_nonneg_of_rate`), window radius `≈ ½ log K`.
  `TransMetzlerWeilPositivity/ABoundedOverlapRateSeesASemilocalWindow.lean:298,439,458` [S].
- The Steklov DC profile is an iterated box average; `TheSincProductProfile.lean` builds the infinite box
  convolution (Fourier transform a product of `sinc` factors, all zeros real) with
  `∫|∂^q| ≤ 4·12^q q!(log(q+3))^{2q}` [S].
- Index along schedules: `hermNegIndex` of the atomic Gram at the DC schedule tends to `κ(K_ζ)` = number of right
  zeros (`dcProfile_atomicGram_reaches_index`, `EffectiveArithmeticHodgeTheory/TheExplicitSchedulesReachTheIndex.lean:755`) [S];
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
  every other test. `RHTower/InfiniteSymmetry/*.lean` [S].
- MPG: PD + integer divisor + simple pole + isolation force `ζ(1+it) ≠ 0`; `ζ(s)Φ(s+κ)` keeps all four invariants
  and vanishes inside the strip (`interior_zero_invisible`). (opus-reboot-facts F8, statements re-located.)

## G7. Heat flow: zero margin on the zero side

- `newmanConstant_nonneg : 0 ≤ newmanConstant`; `not_real_rooted_of_neg`: for `t < 0`, `H_t` has a nonreal zero.
  `RHTower/DeBruijnNewmanConstant.lean:63`, `RHTower/DeBruijnNewmanNonnegative.lean:588` [S].
- `newmanConstant_lt_eighth` (Ki–Kim–Lee, `Λ < 1/2` in standard normalization), by a barrier-zero velocity argument.
  `RHTower/DeBruijnNewmanStrictBound.lean` [S].
- `le_newmanConstant_of_offLine_zero`: an off-line zero of depth `≥ δ₀` at height `γ ≥ t₁` gives
  `Λ ≥ kklDetectionRate δ₀ / log γ`. `newmanConstant_le_half_sq_zetaZeroWidth`: `Λ ≤ Θ²/2`. `RH ↔ Λ = 0`. [S]

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
  `≤ C c⁴/log N`, center residual `≤ C c²/log N`, self error `≤ C c²/N²` on `r̂_m`. [S]
- Ground state (`TheCompleteWeilGroundStateIsThePole.lean`): the completed energy floor is attained at conductor 1;
  exactly one eigenvalue lies below the midpoint of the gap; its line captures the normalized pole vector. Bottom of
  spectrum → `E(c) = (2/M)Σ_{k≥1}(1/k)∫_{kc}^∞|φ̂(2πt)|²dt`, which → 0 as `c → ∞`
  (`TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean`). [S]
- Tilted spline floor `E_m(c) ≥ (2·const/M)c^{−7}` for every `m` (`tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor`);
  Gamma reserve at growing overlap `archForm ≥ (κc^{−7}log N − bc)(c/N)MΣx²` (`archForm_atomicTest_ge_growing`). [S]
- Critical overlap (`TheCriticalOverlapIsLogLogTimesLogSquared.lean`): for a log-DC profile `|φ̂(ξ)| ≤ Aμ_B(2π|ξ|)`,
  `log(1/μ_B(c)) ≍ c/(log c)²`; `c*_N` := least `c ≥ 1` with `μ_B(c)² log N ≤ 1`, so `c*_N ≍ L(log L)²`. "The tail
  energy, which is both the margin of the complete Weil form and its synthesis error, equals the Weil weight
  `1/log N` there." RH ⇔ every bounded multiple `K c*_N` is eventually nonnegative
  (`riemannHypothesis_iff_forall_critical_multiple`); one `K` gives Weil positivity on tests supported in `[−R,R]`
  when `24eB⌈1+e^{2(R+1)}⌉ < K/(32e)` (`nonneg_of_critical_multiple`). [S]
- `TheFixedProfileReachesAnIteratedLogEndpoint`: RH receiver at `L(log L)²log log L` for the Steklov profile;
  "improves the synthesis requirement; it does not prove positivity of the actual complete form". [S]

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
  (`patternSymbol_crystal_dichotomy`). [S]
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
  `p(1)(Σ|c|)²`, bounded in `N`. The lower bound is a growth argument along unbounded powers. [S]
- Finite index is Lindelöf-deep (`lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top`):
  finitely many off-line zeros ⇒ LH and a zero-free half-plane `Re s > ½ + α`, `α < ½`. `κ(K_ζ)` is even; RH ⇔ `κ ≤ 1`.
  `HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean` [S].
- Pole on a tower is one hyperbolic plane; tower index and `Arch − Prime` index differ by at most one
  (`hermNegIndex_le_add_one_of_eq_on_ker`, `ThePoleIsTheOnlyRemovableHyperbolicDirection.lean`) [S].
- Stepanov compression (`compress_pairKernel`, `isPosDefKernel_compress_iff`): compressing by `P = Σp_αδ_{y_α}`
  multiplies a pair weight by `P̂(χ)·conj P̂(χ†)`; PD iff `P̂` vanishes at one character of every pair; on `ℚ_{>0}`
  `P̂` is the Dirichlet polynomial `Σp_α y_α^s` at `s = ρ − ½`. [S]

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
  affine map is a permutation of `ZMod ℓ`, so `0` recurs). [S]
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
  `TheAmplifierLaw.lean`, `OrthogonalityAmplifiersAreTrivial.lean` [S].
- Oscillation (relative Dolgopyat) fails on finite additive realizations (Dirichlet simultaneous approximation) and
  on the free realization (`P(σ+it)` returns to `P(σ)`). `OscillationFailsOnAdditiveRealizations.lean` [S].

## G12. The classical analytic engine inside `RHTower/Sieve` (unconditional)

- Vinogradov–Korobov: `ζ(β+iγ) ≠ 0` for `γ ≥ γ₀`, `β > 1 − (log γ)^{−2/3}(log log γ)^{−5/3}/10⁸`
  (`riemannZeta_ne_zero_vinogradovKorobov`, `RHTower/Sieve/VinogradovKorobovZeroFree.lean:373`) [S, top-level assembly].
- Guth–Maynard Theorem 1.1 (large values: `|W| ≤ C T^ε(N²/V² + N^{18/5}/V⁴ + T N^{12/5}/V⁴)` for 1-separated `W`
  where `|Σ_{N<n≤2N} b_n n^{it}| ≥ V`) is a proved theorem, `guthMaynardLargeValuesBound_holds`
  (`RHTower/Sieve/GuthMaynardTheoremOneOne.lean:184`, `guthMaynardLargeValuesBound_of_S_bounds` from
  `propSixOneBound_zeta`, `propElevenTwoBound_zeta`; statement `GuthMaynardLargeValuesStatement.lean:23`) [S, top-level assembly].
- Consequences: zero density `#zeroHeightBox(σ,T) ≤ D(1+log T)^B T^{(30/13+ε)(1−σ)}`; primes in every interval
  `(x, x+x^α]`, `α > 17/30`, with `ψ(x+h) − ψ(x) ∼ h` uniformly for `x^α ≤ h ≤ x/2`
  (`guthMaynard_thirtyThirteenths_and_seventeenThirtieths_window`,
  `ReflectiveDirichletPolynomialS2/ShortWindowDispersionAtSeventeenThirtieths.lean:55`) [S].
- In the balanced regime `Q ≍ P`, power saving in short windows `⌈Q^α⌉` for the Möbius row and for the prime row are
  each equivalent to quasi-RH `zetaZeroAbscissa < 1` (`moebius_and_prime_powerWindowSaving_iff_quasiRH`) [S].
- Other machinery present: Ingham fourth moment and mollifier second moments, Levinson linear mollifiers,
  Barban–Vehov, Matomäki–Teräväinen Type I/II prime amplifiers, Heath-Brown sparse mean values, Kloosterman sums,
  upper-bound sieves for prime pairs. `RHTower/Sieve` has 3,084 files and two `riemannHypothesis_iff` declarations. [S]
- Fixed-σ density: for `σ > ½`, the zero count with `Re ≥ σ` in a window of length `≍ U` is `≤ ε(T₂ − T₁)`
  (`eventually_zeroCount_fixedSigma_le`, `RHTower/ZetaFixedSigmaDensity.lean:151`) [S].

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
  `ArithmeticCastelnuovoSeveri/WhatAGramFunctionalCertifiesWithoutEffectivity.lean`) [S].
- Breaking it needs either the split `(P, Q)` (on-line Parseval slack `onSlack = ‖P‖² − c tr P + (c²/4) rank P`,
  negative-part credit `2 tr Q₋ > 0` iff `Q` not PSD) or `κ < 4/3` from prime correlations past `λ = 1`; the joint
  `(c = 2, c = 3)` functional equals `((7 − 3κ)/4)N` and is exactly `3/4` at `κ = 4/3` on the extremizer
  (`BreakingTheCoalescenceBlindSpotAndThreeQuarters.lean`) [S].
- Higher inertia: the blind-spot configuration has normalized moments `(1, 4/3, 2, 10/3)`; every polynomial weight
  of degree `≤ 3` certifies at most `2/3`; a quartic weight helps only with an upper bound on `κ₄`, and the quartic
  moment is within the correlation range only for `λ < 1/2` (cycle frequency budget `Σ|ξ_i| ≤ 4λ`). `3/4` needs
  `κ₄ ≤ 2503/768`; the sine-kernel `κ₄ = 13/4` gives `16/21` (`TheBlindSpotIsExactThroughThirdOrder.lean`) [S].
- Spectral-slack route to `HD(1)` is refuted for every bandwidth `λ < HD(1)` by the grid-dimension ceiling
  (`not_HD_one_zeroSideSlack_of_lt_HD_one`); off-line moment upgrade to `57/1000` given `3/4`
  (`CoalescentSurplusAndTransThresholdProportionLaws.lean`) [S].
- Universal reflection bound `2R(T₁,T₂) + N₀*(T₁,T₂) ≤ N(T₁,T₂)` without simplicity (`two_mul_sum_right_add_N0star_le`). [S]

## G15. Electrostatic (individual) forms with slack (AES, statements read)

- Transverse energy `𝓔 = ½Σ_{ρ≠ρ'}(Re ρ − Re ρ')²/|ρ − ρ'|²`: `𝓔 = 0` ⇔ RH ⇔ `𝓔 < 1`; `𝓔 < ∞` ⇔ finitely many off-line
  zeros; every off-line zero carries at least one quantum; `E(ρ) ≤ 16(C + log(|γ|+4))` unconditionally; RH ⇔ every
  unit window has energy `< 2` (`TheTransverseEnergyOfTheZeroDivisor.lean`, `TheEnergyOfAZeroIsLogarithmic.lean`,
  `QuantizationTurnsWindowsIntoPoints.lean`). "Averages, proportions and almost-every statements place most zeros
  near the line and exclude none: excluding an individual zero needs control below the zero spacing." (The quoted
  sentence is docstring prose [P]; the energy statements are [S].)
- Field threshold: every off-line zero has within `C log γ` a locally rightmost terminal of depth `δ` with transverse
  field `≥ 1/(2δ) + cδ log(|γ_p|+4) ≥ √(2c log γ)`; RH ⇔ every right zero feels field `< √(2c log(|γ|+4))`
  (`exists_riemannHypothesis_iff_transverseField_lt_sqrt_log`, `TheFieldLawHasAThreshold.lean`). "The missing
  arithmetic input is an upper bound of this size, not an exact equilibrium." [S]
- External field law for `Re s > 1`: `Σ Λ(n)n^{−σ}cos(γ log n) ≤ Re(archFactor′/archFactor)(s) − m/(σ − β)` at the
  ordinate of a zero of real part `β` (`re_LSeries_vonMangoldt_le_at_zero_ordinate`, `TheExternalFieldIsAPrimeSum.lean`). [S]
- Large values at zero ordinates: `Σ_γ |F(γ)|² ≤ K log(A+R+1)(R + 8N(1+log N))(2 + log²N)Σ|a_n|²`; for powers of prime
  polynomials the aligned ordinates in `(T,2T]` at `V = η log T`, `X = (log T)^C` number `T^{1−1/C+o(1)}`
  (`LargeValuesAtZeroOrdinates.lean`, `HigherMomentsAtZeroOrdinates.lean`). [S]
- Electrostatics is blind to the archimedean twist `s ↦ ½ + λ(s−½) + iκ` (`transverseEnergy_affine`). [S]

## G16. Corpus-wide unification of the obstructions (SquareRootThreshold)

- `TheWallsMeasureOneZeroWidth.lean`: prime-side deficit primitive, Chebyshev mean square, Laplace and spectral band
  rates, Suzuki formation energy (`subpower at 1 + 2σ`), Möbius–divisor Abel energy exponents (`inf = 1 + 2Θ`), lag
  family negativity rate, CCM ground energy floor (`μ(A) ≥ −Ce^{2σA}` ⇒ `Θ ≤ σ`), heat (`Λ ≤ Θ²/2`), Balazard–Saias–Yor
  integral, prime-blind node criticality: all read `Θ = zetaZeroWidth = sup|Re ρ − ½|`. "The converse floor on `μ` from
  the width is not proved here; it is the graded form of the no-crossing problem." [S]
- CCM: `μ₀(B) ≥ −Ce^{εB}` for all `B` ⇒ every zero has `|Re ρ − ½| ≤ ε/2` (sharp form); attained top depth gives
  `μ₀(B) ≤ −c e^{2ΘB}/B³` (`CCMRestrictedWeilPolarBombieriYoshidaSharp.lean`). [S]

## G17. Deninger carriers (RHTower/Deninger, statements read)

- The resolvent-core package (centred generator with surjective off-axis resolvents and transpose eigenfunctionals at
  every `ρ − ½`) is equivalent to RH and is realized by the naive carrier of functions on the zero set; "the package
  carries no information beyond RH unless its carrier is built independently of the zeros"; a conformally scaled
  positive seminorm coexists with an eigencharacter of any off-line exponent
  (`exists_conformal_seminorm_with_offLine_character`, a two-dimensional model `ℂ × ℂ`). `DeningerResolventCoreIsRiemannHypothesis.lean` [S].
- Oriented Hilbert Hodge structure on `XiDivisorL2`: `J² = −1`, cup form alternating and nondegenerate; Frobenius
  commutes with `J` ⇔ RH (`DeningerArithmeticOrientedHilbertHodge.lean`) [S].

## G18. What bounded overlap does and does not separate

- Pole-free sign twins (completely multiplicative `±1`, bounded harmonic sums; Liouville, every cofinite flip) have a
  negative complete form above the Robin–Euler ratio `< 1` while ζ's matrix is PD at the same overlap
  (`liouvilleSelector_selective_of_signGauge`, `liouvilleSelector_selective_of_cofiniteFlip`,
  `CriticalArithmeticCorrelationTheory/FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip.lean`;
  mechanism: projection onto the pole hyperplane, `EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio.lean`). [S]
- A single-prime flip at `p` is invisible at every overlap `c ≤ (κ√p/log p)^{1/8}` and visible from `c ≍ (Kp)^{1/7}`
  (`tiltedUnitSpline_flip_threshold_polynomial`,
  `RenormalizedArithmeticPotentialTheory/TheFlipThresholdGrowsLikeAPowerOfThePrime.lean`). Conductor bound
  `E_m(c) ≤ (m/φ(m))E_1(c/m)`. [S]
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
  log-derivative step of the VK region). [S]

---

# K. The corpus condensed by object

Every item below was read in source: statement and proof, or statement and the proof's assembly from named lemmas
that were themselves read. Tags: [S] proof read; [P] the module's prose claims more than its Lean content, which is
stated next to the tag; [X] the Lean wraps the pinned external `Zeta23` package. Anchors are paths relative to
`formal/GaloisForLFunctions/`.

## K0. The mechanisms behind the laws

Almost every structural theorem in K1–K10 is one of eight mechanisms applied to the explicit formula.

- **M1 Explicit formula.** An arithmetic functional of a compact test equals `Σ_ρ c_ρ e^{(ρ−½)τ}` plus a bounded
  archimedean tail plus pole terms (`hasSum_packet_explicit_formula`, `BiScaleUncertainty/PacketBoundednessCriterion.lean`;
  `lagStructure`, `SquareRootThreshold`) [S].
- **M2 Exponential-sum extraction.** A sum `Σ c_i ν_i^n` or `Σ c_ρ e^{λ_ρ τ}` is `O(r^n)` only if every coefficient
  at a node of modulus `> r` vanishes. The tools are Vandermonde non-cancellation of unimodular sums
  (`coeff_eq_zero_of_tendsto_zero`, `HeckeKreinToeplitz/GrowthReadsTheDepthOfTheDeepestPair.lean`), Laplace continuation
  plus residues (`coeff_eq_zero_of_eqOn_zeroResolvent`), discrete Cauchy transforms (`classSum_eq_zero_of_growth`,
  `ArithmeticCastelnuovoSeveri/OneLefschetzSequenceGrowsAtTheZeroWidth.lean`) and Cesàro means
  (`not_eventually_re_mul_pow_le`) [S].
- **M3 Landau one-sidedness.** A one-sided bound `ηF ≤ Ke^{στ}` makes `εe^{στ} − ηF` a nonnegative measure. Its Laplace
  transform is analytic at every real point beyond `σ` because ζ has no real zero in `(0, 1)`
  (`zeroShift_ne_ofReal` from `riemannZeta_real_strip_ne_zero`, `BiScaleUncertainty/PacketOneSidedGrowthLaw.lean:73`),
  so the abscissa is `σ` [S]. The only exception to one-sidedness anywhere in the corpus is a real positive eigenvalue
  or real zero. Examples:
  - over `𝔽_q` the upper count misses a real outer eigenvalue (`UpperLefschetzBoundsAreBlindOnlyToRealZeros.lean`);
  - over ℤ one prime is rotated by two-term tests (`rotation_factor`), and two primes force `Im ρ = 0` through
    `irrational_log_ratio` (`exists_prime_frobEig_phase_sq_ne`, `OneSidedLefschetzBoundsAtTwoPrimesAreTheStrip.lean:200`)
    [S].
- **M4 Archimedean domination.** At height `ξ` the Gamma density `log(1 + π|ξ|/4)` exceeds
  `horizonExponent(e^{2a}) + 2 pairEnergy(½, a) = 10 + 68e^a + 2(sinh a − a)` for tests of aperture `a`
  (`zetaZeroConfig_re_W_heightShift_pos_of_dominance`, `DilutionCrystallizationPincer/ArchimedeanDominationOfDilutedVisibility.lean:70`)
  [S].
- **M5 Toeplitz minors and Fejér elimination.** A two-bump test reads the `2×2` minor
  `|S_γ(v) + conj S_γ(−v)| ≤ 2 Re S_γ(0)`. Fejér-power windows and the recursion
  `(x² + β²)K_{k+1} = cK_k` eliminate companions one at a time (`dipole_elimination`, `elimSeq_cons`,
  `SquareRootThreshold/ZetaNearTopClustersCollapseBeyondTheThreshold.lean`) [S].
- **M6 Local zero count.** At most `40 log(180|t|)` zero copies have ordinate within `1` of `t`
  (`RHTower.card_le_of_ordinates_in_window`). It is the only ζ-specific input of the hiding laws for ζ
  (`ZetaLagPositivityForcesCloseCompanions.lean` docstring and proof) and of large-height heat repair
  (`ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean`) [S].
- **M7 Linear algebra of renormalization.** Survival cones, the rank of coupled counterterms and Finsler–Debreu
  (`RenormalizedBiarithmeticGeometry/TheRenormalizationSurvivalLaw.lean`,
  `RenormalizedArithmeticPotentialTheory/TheCoupledSurvivalLaw.lean`) [S].
- **M8 Symmetry bookkeeping and integer orders.**
  - The index is even because right zeros come in conjugate pairs (`negIndex_zetaKernel_eq_two_mul`).
  - The transverse quantum is `1` because the segment from `ρ` to `1 − ρ̄` is horizontal (`pairQuanta_le_transverseEnergy`).
  - Abel residues are even integers because central orders are even under the FE (`tendsto_abel_excess_eq_centralDrop`).
  - Local exponents are integers because a ratio of analytic functions has integral order on a ray
    (`exists_int_localExponent_of_receiverBounded_damped`).
  - The successor bias is `−1/p` by `Σ χ(r)χ(r+1) = −1` (`succCorr_legTwin`).
  - Integer-valued PD functions are sign characters (`intValued_posDef_iff_signCharacter`) [S].

Three modules state sweeping claims in prose while their Lean proves only arithmetic:
- `RHTower/ContourCrossingObstruction.lean` [P]: "every unconditional input is separated from the error by the strip";
  "inside the strip only counts". The Lean is `regions_separated : ½ < σ ∧ σ < 1 → ½ < σ ∧ σ < 1` and
  `inside_strip_only_counts : 1 ≤ N → N ≤ S → 1 ≤ S`.
- `RHTower/CorrelationBoundsCountNotLocation.lean` [P]: the Lean is `|‖z + c‖² − ‖z‖²| ≤ 2‖z‖‖c‖ + ‖c‖²` and
  `N·c ≤ S → N ≤ S/c`.
- `RHTower/DiscriminantIsRealitySensitive.lean` [P]: the Lean is `∏(r_i − r_j)² ≥ 0` and the quadratic discriminant.

## K1. Growth rates read the depth `Θ = sup|Re ρ − ½|`

- **Packets** (`BiScaleUncertainty/PacketOneSidedGrowthLaw.lean`) [S].
  - The packet is `P_f(τ) = Σ_{n ≤ e^{τ+R}} Λ(n)n^{−1/2}f(log n − τ) − ∫2cosh(x/2)f(x − τ)dx`, the smoothed `ψ`-error
    at `x = e^τ` over `√x`.
  - `P_f = O(e^{στ})` ⇔ `f̂(γ_ρ) = 0` for every zero of depth `> σ` (M1 + M2).
  - Either one-sided bound suffices (M3).
- **Orbit correlations** `c_f(t) = W(f(·−t), f)` of any tempered FE-symmetric configuration grow at the depth of the
  deepest seen zero (`orbitCorr_rate_iff_blindAbove`, `ArithmeticOrientationGeometry/TheOrientationRateIsTheDepthOfTheDeepestSeenZero.lean`)
  [S].
- **Lefschetz sequences** `c_m = W(T_{p^m}g, g) = Σ_τ X_τ conj X_{1−τ̄} p^{m(τ−½)}`: for ζ one test has `c_m = O(R^m)`
  ⇔ `R ≥ p^Θ` (`zeta_lefschetz_growth_law`; needs `deepSparse_zeta`) [S].
- **Lag families, dyadic prime windows, the deficit primitive and the mean-square band**: Θ is the infimum of the
  admissible one-sided rates (`TheZeroWidthIsALandauExponent.lean`) [S]. A bounded parameter range carries no exponent;
  that is a property of exponents.
- **Polar ground energy.** `zetaZeroWidth ≤ polarGroundEnergyRate ≤ ½`, with `½` from `μ₀(A) ≥ −(10 + 68e^A)`. The
  reverse inequality is open (`TheZeroWidthIsALandauExponent.lean`, section 5) [S].
- **Abstract Krein–Langer kernels** along `u^n` grow at the largest node modulus, by Vandermonde (HKT) [S].
- **One-sided global laws** [S]:
  - `negIndex zetaKernel = 0` ⇔ `ψ(x) − x ≤ C√x log² x` eventually (one-sided converse
    `riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq`, `RHTower/VonKochChebyshevBound.lean:644`, by Landau);
  - over `𝔽_q`, index zero ⇔ `N_k ≥ q^k + 1 − Cq^{k/2}` (`global_law_count`).
- **Nonnegative-cone criterion** (`riemannHypothesis_iff_forall_nonneg_cone`, `ArithmeticCriticalityTheory/NonnegativeConeZeroFormCriterion.lean`)
  [S]. In Doob coordinates every term is a nonnegative functional. Tests of any sign are lifted by plateaus of the
  theta ground state, which lie in the radical, and the inequality is sharp at the constant profile.

## K2. Bounded scale is blind, and why

- **Aperture `3/10`.** `e^{0.6} < 2`, so the window `n ≤ e^{2a}` contains no integer `≥ 2`. Positivity there is
  pole-plus-archimedean and holds for every weight, the Liouville twin included (`aperturePositive_threeTenths`,
  `ArithmeticOfSquareRootPrecision/FiniteAperturePositivityCannotDecide.lean`) [S]. Aperture `12/25` reads only `n = 2`.
- **Finite windows.** Aperture-`A` positivity is determined by `λ` on `n ≤ e^{2A}` (`aperturePositive_congr`), so no
  finite aperture implies an asymptotic count [S].
- **Domination (M4).** It holds up to `a ≲ log log|ξ| − 4.2` [S].
- **Low-frequency divisor.** At degree `a`, Weil positivity holds once `f̂` vanishes at `i/2` and on a grid of
  `#lowGrid(a)` frequencies below `T(a) = horizonFreq a = 4(e^{2(10+68e^a)} − 1)`. The negative index is
  `≤ #lowGrid(a) + 1`, doubly exponential in `a`. Mechanism: M4 plus Lipschitz sampling (`re_W_zeta_nonneg_of_lowGrid`,
  `ArithmeticCastelnuovoSeveri/TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies.lean:256`) [S].
- **Superexponential margin.** The truncated Riemann kernel `Φ` (its transform is Ξ, so it is in the radical) gives
  `‖W(f_L, f_L)‖ ≤ Ce^{12L}e^{−πe^{2L−1/2}}‖f_L‖²` (`zeta_weil_margin_superexponential`,
  `RHTower/WeilMarginSuperexponentialLaw.lean:916`) [S].
- **Averaging.** Windowed height averages at resolution `r` are integrals of aperture-`r` Weil forms. Model off-line
  lattices, isolated pairs in dense lattices, clusters with `r·TV(d)·sinh(2δr) ≤ 1` and Toeplitz-PSD profiles all pass
  them (`WindowedPositivityNoGoForOffLineConfigurations.lean`, `WindowedBlindnessForClustersAndProfiles.lean`) [S].

## K3. Refutation and detection

- Any failure of Weil positivity is witnessed by one compactly supported test of finite radius. RH ⇔ no finite-radius
  reading refutes membership of Λ in the Weil cone (`riemannHypothesis_iff_no_radiusReading_refutes`,
  `ScaleSignedIncidenceCriticality/RefutationIsFiniteConfirmationIsNot.lean:361`) [S].
- **Finite off-line sets** are visible at aperture `(1/2g)log⁺((2M_b + 4Σ|q_t|)/c) + (|T| + 2)ℓ/2 + w`. The constant `c`
  comes from compactness (`exists_weighted_powerSum_window_lower`, `SquareRootThreshold/EqualDepthClusterInArbitraryBackground.lean:43`)
  and is not effective in the configuration (`finiteOffLine_visible`) [S].
- **ζ, attained top:** visible at lag `O_w((log γ₀·log(log γ₀/g) + log log γ₀)/δ₀)`, `g` the separation near the top
  (`zeta_attained_top_visible_log`) [S].
- **ζ, any near-top zero:** a zero within `1/V` of the supremum makes a modulated difference test negative at a lag
  `≤ V` once `V ≥ V_w(γ₀, δ₀) ≍ (log γ₀)² log log γ₀/δ₀` (`zeta_near_top_visible_at_polylog_lag`,
  `ZetaNearTopZerosAreVisibleAtAPolylogarithmicLag.lean:275`) [S].
- **Sparse families decide RH** (M5 + M3 with no real zeros):
  - unimodular two-bump tests (three parameters);
  - difference tests (two parameters, one sign);
  - one parameter for all but countably many widths `w < ½ log 2`;
  - dyadic prime windows beyond any `X₀`;
  - pole-free windows against the archimedean term alone (`onLine_iff_polarFree_primeWindow_le_arch`);
  - the same for primitive Dirichlet `L` (`grh_iff_primeWindow_nonneg`) [S].
- **Determination.** The Weil form, or the lag family alone up to `m(ρ) + m(ρ̄)`, determines a tempered configuration
  (uniqueness of exponential sums; `eq_of_weil_eq`, `eq_zetaZeroConfig_of_lag_weil_eq`) [S].

## K4. The shape a hidden off-line zero must have

These are implications of the form "Weil-nonnegative on the lags `[0, V]` ⇒ structure". RH gives the hypothesis at
every `V`; a counterexample violates it by `V_w` (K3).

- **Model configurations** (`ScaleSignedIncidenceCriticality/TheHidingLaws.lean`) [S]:
  - an isolated off-line pair in on-line mass `M = Σ_{on-line} m_ρ|β̂(γ_ρ − γ₀)|²` hides only to lag
    `arsinh(M/|Q| + 1)/δ`, i.e. aperture `≈ log M/(2δ)`;
  - a diluted lattice reaches `a ≤ log((3L + ℓ)/ℓ)/(2δ) + ℓ/2`;
  - aliasing is free below `ℓ/2` and ends there.
- **Crystallization.** Adding the half-step translate of an off-line lattice doubles its Nyquist aperture, so visibility
  is not monotone in the configuration (`exists_offLine_superset_hiding`, `CrystallizationHidesOffLineZeros.lean:97`)
  [S]. Periodic patterns hiding at unboundedly many scales must be uniform crystals (`uniform_crystal_of_hiding`) [S].
- **ζ, near-top zeros** (`SquareRootThreshold/Zeta*.lean`; M5 + M6) [S]:
  - **Trichotomy** (`zeta_hiding_needs_near_top_twins`). For every `V` and `T` there is a `1/V`-near-top zero above
    `max(T, T_w)` with one of: a negative difference test at a lag `≤ V`; or `V < V_w(z₀)`, i.e. every near-top zero
    lies at height `γ₀ ≥ exp exp(c_wΘV)`; or a twin of its Legendre record within `R_w(γ₀)/V`,
    `R_w ≍ log log γ₀`.
  - **Loud twins.** Hiding needs other zeros, together nearly as loud as the record, within
    `r ≍ κ(log|Im z*|)^{1/3}/V` of the point below it (`zeta_twin_law`).
  - **Tight twins.** An isolated twin is exponentially tight, at distance `≤ C log γ₀·r e^{−cVr}` with
    `c = log 3/(4π)`, by Fejér recursion (`zeta_near_top_twin_tight_or_triple`).
  - **No isolated twins.** Isolated twins cannot hide, because squared nearby transforms keep a coherent phase
    (`zeta_isolated_twins_cannot_hide`).
  - **Collapse.** Hiding a near-top record up to lag `V` needs a cluster of `p ≤ P ≍ log γ₀` zeros of geometric-mean
    radius `≲ e^{−cVδ₀/p}`: an approximate multiple zero of multiplicity `p + 1`. This sets in once `Vr ≫ log γ`,
    "beyond the square-root threshold `V ≍ log T`" (`zeta_near_top_cluster_collapse`, `zeta_cluster_collapse_explicit`).
- **Shallow zeros** (`ShallowCauchyPrimeEnergy/*.lean`) [S]. In `[T, 2T]`, within `1/log T` of the line:
  - `Σ m_j² ≤ CT log T` and `Σ_{|γ_j−γ_k| ≤ K/log T} m_j m_k ≤ (C/8)(16 + K²)T log T`. These have the order of all zeros
    and exclude no individual cluster.
  - Selberg's near-line density, formalized: depth `α/log T` costs `e^{−α/28}/α`
    (`exists_selberg_exponential_nearLine_zeroDensity_long`).
- **Low height:** every off-line zero has `γ² ≥ 431/2` (`im_sq_ge_of_xi_eq_zero_of_re_ne_half`, used in
  `RHTower/LiFirstCoefficientsNonneg.lean`) [S].

## K5. Prime phases, transcendence, recurrence

- **Kronecker density** (non-quantitative): the prime-only polynomial reaches `±` its `ℓ¹` envelope at some height. With
  the archimedean bound `Re A_f(ξ) ≤ 2e^a‖f‖₁² + B_f²(½ + πC) + ‖f‖₂² log(1 + 2π|ξ|)`, ζ is negative there or the height
  satisfies `log(1 + 2π|ξ|) > (B − …)/‖f‖₂²` (`exists_re_W_neg_or_height_escape`,
  `SquareRootThreshold/KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape.lean:535`) [S].
- **Crystal gap.** In a gap of the lattice `nL` the model crystal answers `4L‖κ_w‖² > 0`; on ζ the Kronecker step
  applies (`crystal_gap_prime_torus_incompatibility`, `DilutionCrystallizationPincer/PrimeTorusCrystallineResonanceObstruction.lean:140`)
  [S]. The comparison is between ζ and a model lattice. Both outcomes are compatible with RH.
- **Dirichlet recurrence:** `d` prime phases come within `2π/(Q+1)` of `0` at some integer height `≤ (Q+1)^d`
  (`exists_fin_primeLog_phase_recurrence_quantitative`) [S].
- **Effective Baker (Fel'dman), formalized** (`RHTower/Matveev/EffectiveBaker.lean:195`, 4,825 lines) [S]:
  - `|Σν_i log p_i| ≥ c(2 + |ν|₁)^{−C}`;
  - the exponent `C₀ = feldmanLambdaExponent ≥ q = E^{m+1}(R+1)`, with `E = 1000·Wb·(R+1)`, `Wb ≥ Σ log p_i` and
    `R ≍ (m+1)(m+2) log(1000Wb)`, grows at least exponentially in the number `d = m + 1` of primes;
  - two primes: `|e_p| log q + |e_q| log p ≥ c min(|Δ|, (2 + |Δ|)^{−C})`, against `e^{−O(T)}` from integrality alone
    (`two_prime_alias_bound`) [S].
- **`S(T)` is unbounded** (`rvmRemainder_unbounded`, `SquareRootThreshold/ZetaZeroCountRemainderIsUnbounded.lean:101`)
  [S].
- **Recurrence.** Zeros of finite exponential polynomials recur vertically, by simultaneous approximation and Rouché.
  A recurrent tempered configuration therefore has Hodge defect `0` or `∞`
  (`expPoly_pontryagin_dichotomy`, `recurrent_pontryagin_dichotomy`) [S].

## K6. Torsion of the circle

- **Intersection.** `I(m, mt) = φ(m)Λ(t)`, with `I(m, n) = log|Res(Φ_m, Φ_n)|` (Apostol), via
  `J(a, b) = gcd(a, b) log lcm(a, b)` and double Möbius inversion (`orbitIntersection_eq`, `orbitIntersection_hecke`,
  `ArithmeticEffectivityTheory/TheIntersectionOfTorsionOrbits.lean`) [S].
- **Renormalized energy.** For `r < 1` the gcd-twisted torsion energies `Q_r` are nonnegative: they are the Gram matrix
  of Ramanujan-sum vectors, Schur-multiplied by the gcd twist. Also
  `Q_r(x) + log|1 − r| Σx_n² → −Σ x_m x_n P(m, n) − Σ x_n² I(n, n)/φ(n)`
  (`weilPrimeKernel_renormalized_torsion_energy`, `ArithmeticEffectivityTheory/TheWeilPrimeKernelIsARenormalizedTorsionEnergy.lean:370`)
  [S].
- **Gauss digamma.** `Σ_{0<a<N} log|1 − ζ_N^a| cos(2πak/N) = log N + γ + ½(ψ(k/N) + ψ(1 − k/N))`, as the
  `r → 1` limit of the Fourier expansion of the torsion energy on `μ_N`. The `log N` is the regulator anomaly
  (`gauss_digamma_theorem`, `ArithmeticIntersectionTheory/GaussDigammaIsTheFourierTransformOfTheTorsionEnergy.lean:210`)
  [S].
- **Fekete.** `Σ_{i≠j} log|z_i − z_j| ≤ N log N` on the circle (Hadamard), attained by `μ_N`
  (`ArithmeticElectrostatics/TheTorsionIsTheStableEquilibriumOfTheCircle.lean`) [S].
- **Gauss sums.** `|τ(χ, ψ)|² = |F|` by orthogonality; the root number has modulus `1`
  (`ArithmeticEffectivityTheory/TheTorsionCharacteristics.lean`) [S].
- **Cyclotomic norm.** A nonvanishing primitive prefix `Σ_{j<k} ζ^j` has `Σ_ζ |·|² ≥ φ(m)` by norm `≥ 1` and AM–GM
  (`totient_le_primitiveRootPrefixEnergy`, `CriticalArithmeticCorrelationTheory/CyclotomicNormGivesAConductorUniformCurvatureFloor.lean:81`)
  [S].
- **Gauge blindness.** For completely multiplicative `ε = ±1` (Liouville among them), `P^ε(m, n) = ε(m)ε(n)P(m, n)`:
  every sign twin's prime form is ζ's in the gauge `x ↦ εx`. No statement about the prime form alone separates ζ from
  its sign twins; selectivity must come from the pole term `(Σx√n)(Σx/√n)` and the archimedean place
  (`ArithmeticIntersectionTheory/TheFiniteIntersectionIsGaugeBlind.lean`) [S].

## K7. Spectrum of the prime form and renormalization

- **Pole gauge.** `poleDefect N x = Σ_m Σ_{t≤N/m} Λ(t)(x(mt) − x(m)/√t)² ≥ 0`, and `P_N + D_N ≤ (log N − γ + ε)I`
  eventually (`RenormalizedArithmeticPotentialTheory/TheDeficitOfThePrimeFormIsADirichletEnergy.lean:47`) [S].
- **Gap.** `P_N(x) ≤ (log N − γ − 2log 2 + ε)|x|²` on `Σx_n/√n = 0`, via Efron–Stein on `Q`-smooth boxes, the ladder gap
  `log p Σp^{−i}` (`= 2log 2` at `p = 2`), a halo of mass `O((E + Var)/log X)`, and two scales
  (`eventually_atomicWeilForm_le_two_log_two`, `TheSpectralGapOfThePrimeFormIsTwoLogTwo.lean:1085`) [S].
- **Top spectrum.** Within `T` of `log N − γ` it is indexed by the integers `m` with `log m + Σ_{p|m} log p/(p−1) < T`,
  from the box modes `Ψ_m` (`TheTopSpectrumOfThePrimeFormIsExhaustedByTheIntegers.lean`,
  `TheFinitePrimeChainHasTheSpectrumOfTheIntegers.lean`) [S].
- **Survival law.** Positivity passes a scale limit on the null cone of the counterterm. The cone is scheme-independent.
  For an identity counterterm every symmetric form is a renormalized limit of PD forms. A rank-one `vvᵀ` leaves the
  hyperplane `⟨v, x⟩ = 0` (`RenormalizedBiarithmeticGeometry/TheRenormalizationSurvivalLaw.lean`) [S].
- **Abel torsion germ.** The counterterm is `I` and the survival cone `{0}`. The limit is indefinite on `{1, q}` because
  the order-1 orbit has zero self-intersection while `P(1, q) = Λ(q)/√q > 0` (`torsionLimitForm_neg`). The lattice germ
  has counterterm `𝟙𝟙ᵀ` (`counterterm_rank_dichotomy`) [S].
- **Coupling.** `rank C ≤ rank D`. Under the Abel regulator a partner pays at most `rank D` torsion directions; the
  lattice germ pays one (`coupled_torsion_survival`, `coupled_lattice_primeSurvival_le_one`) [S].
- **Hecke cocycle.** `β(n, t) = log t − Σ_{p|t,p∤n} log p/(p−1)`, not a bounded coboundary
  (`ArithmeticIntersectionTheory/TheHeckeCocycleOfRenormalization.lean`) [S].
- **Spacing regulator** `ρ_n = e^{−ε/n}`: positive at every `ε`, Hecke-covariant up to tame ramification, scalar
  counterterm `log(1/(2ε))`, limit `−P + diag(e(n))` indefinite on `{1, 2}`
  (`TheSpacingRegulatorRemovesTheAnomaly.lean`) [S].
- **Horizon (`N → ∞`).** [S]
  - Polar (rank one) on uniform step profiles: `|P_N(x) − ℓ(x)²| ≤ (log 8 + 5)Σ|c_i||c_j|H_{min}`
    (`TheHorizonCountertermIsPolar.lean`).
  - Unbounded rank on `p`-adic valuation classes (`horizonCounterterm_rank_unbounded`).
  - On class profiles exactly `Σ_j δ_j^{−1}ℓ_j(x)²` with `δ_j = (1 − 1/p)/p^j`; survival cone `ℓ_j = 0` for every `j`
    (`TheHorizonCountertermIsATensorProduct.lean`).
  - `[p]`-covariant on `p`-adic classes (`TheHorizonCountertermIsHeckeCovariant.lean`).
- **Self-intersection.** On a `p`-ladder vanishing at its two lowest levels the renormalized torsion form is
  `≤ −((1 − q)/(1 + q))log p|x|²`, `q = p^{−1/2}` (`TheSelfIntersectionDominatesTheTower.lean`) [S].

## K8. Horizons and the successor

- **Horizon identity.** At a zero, `X_N(ρ) = −B_N(ρ)` with `B_N(s) = N^{1−s}/(s−1) − s·emTail N s`, so
  `Q(f_pole) = Re Σ_ρ m_ρ ĝ(γ_ρ)conj ĝ(conj γ_ρ)B_N(1−ρ)B_N(ρ)` (`weilQuad_poleMode_eq_tsum`,
  `ThePoleModeMeetsTheZerosOnlyAtTheHorizon.lean:167`) [S]. The "Poisson dual of the successor shells" in its docstring
  is not a theorem of the module.
- **Charge.** `|P_a(s)P_a(1−s)| ≤ N(Σ|a_d|/d)²/|s(1−s)|`, because `N_d^{1−β}N_e^β ≤ N`
  (`TheHorizonChargeIsBlindToTheRealPartsOfTheZeros.lean`) [S].
- **Tail, computed from the definitions.** `emPole N s = N^{1−s}/(s−1)` and `emTail N s = ∫_N^∞{x}x^{−s−1}dx`
  (`RHTower/EMCarrier.lean:46,58`). Hence
  `B_N(ρ)B_N(1−ρ) = N^{−1}[N/(ρ−1) − ρJ_N(ρ)][−N/ρ − (1−ρ)J_N(1−ρ)]`, with `J_N(s) = ∫_1^∞{Nu}u^{−s−1}du` and
  `|J_N(s)| ≤ 1/Re s`. Depth enters every term only through bounded factors; there is no `N^δ` growth.
- **Integrality of the shift.** The continuum shell completion (no integer successors) has energy
  `log(1/(2πc)) + β/M → −∞`. The lattice gain is `log(2πc) − β/M + o(1)`, and the actual energy is `≥ 0` and `→ 0`. The
  gap `|h| ≥ 1` alone repays `M log c`
  (`SuccessorShellArithmetic/TheIntegralityOfTheShiftRepaysTheLogarithm.lean`) [S].
- **Top band.** Along `b + η1_T` the joint coefficient `a₋a₊(H_N|T| + NS_T) − Σ_T b_nR(n)` is `O(G(log N + c + 1))`,
  while each term is `≍ Gcq log N` (`exists_abs_jointWitnessCoefficient_le`) [S].
- **Successor collar.** `heckeIncidence k (k+1) = 0` and `archLevyDensity(log((k+1)/k)) = (k+1)√(k(k+1))/(2k+1)`
  (`ArithmeticCastelnuovoSeveri/TheSuccessorCollar.lean`) [S].
- **Successor connection.** The successor defect of `P_N` has no sign on the nonnegative cone. In the gauge `g = conj χ`
  the archimedean kernel on the edge `(n, n+1)` carries `conj A_ω(n)`, `A_ω(n) = conj χ(n)χ(n+1)`, and is nonnegative on
  all edges of `[1, N]` iff `ω(p) = 1` for every `p ≤ N + 1`
  (`ArithmeticLorentzianGeometry/TheSuccessorConnectionIsTheArchimedeanGaugeField.lean`) [S].
- **Successor at zeros.** `ΣΛ(n)(n+1)^{−s} = −ζ'/ζ − D_Λ`, with `D_Λ` holomorphic on `Re s > 0` and
  `|D_Λ(s)| ≤ |s||ζ'/ζ(1+σ)|` (`ArithmeticCorrespondencePositivity/TheSuccessorIsInvisibleAtZeros.lean`) [S].
- **Atomic blindness.** On `Aff(ℚ)` an atomic archimedean dilation spectrum makes `φ(x ↦ x + b)` constant
  (`successor_blind_of_atomic`) [S].
- **Successor class.** `Count a ⇔ a − 1 ∈ 𝒬`, and any `u` with `u − 1 ∈ 𝒬` gives the same statement
  (`ArithmeticOfSquareRootPrecision/TheSuccessorEntersOnlyModuloTheSquareRootClass.lean`) [S].

## K9. Heat

- **Bounds.** `0 ≤ λ_WD ≤ Λ ≤ 1/8`; RH ⇔ `λ_WD = 0`. No slack below `0`, by Newman–Rodgers–Tao
  (`RHTower/XiSliceHeatTransferNoSlack.lean`) [S].
- **Sharp KKL.** For `0 < t ≤ 1/8`, zeros of `H_t` with `|Re z| ≥ max(X₀, 2πe^{(1+√3/2+ε)/t})` are real and simple
  (`riemannHeat_zeros_real_simple_sharp`, `RHTower/KiKimLeeSharpSimpleZeros.lean:78`) [S].
- **Repair from counting.** A degree-`N` polynomial with roots in `|ρ| ≤ r` is heat-repaired at `32r/N`. The radius-`R`
  head of the Ξ-slice is repaired at `32R²/N(t, R) → 0` (M6; "the Euler region is not used")
  (`ArithmeticLocalDivisorGeometry/RootRadiusHeatCone.lean`, `RadiusHeadHeatPositivity.lean`) [S].
- **Slice repair rates.** Every `T_{2m}(λ, 0, t) > 0` for `λ ≥ κ/log|t|` and `|t| ≥ t₀`, with:
  - `κ = 100` (`XiSliceHeatEffectiveKKL.lean:374`);
  - `κ = 1 + δ` (convexity);
  - `κ = 19/25` (Weyl, `μ(½) ≤ 1/6`);
  - `κ = 17/25` (`μ(5/7) ≤ 1/14`, `XiSliceHeatRateInteriorLindelof.lean:754`) [S].
  The size-only method floors at the parabola envelope of the Lindelöf profile (`27/40` with these exponents).
- **Detection rate.** An off-line zero `½ + δ + it`, `t ≥ e^{16}`, `δ ≥ δ₀`, makes some `T_n(κ/log t, 0, t)` negative
  for every `κ ≤ κ₀(δ₀) = δ₀²/(200(log(3/δ₀) + 1))` (`re_xiSliceHeatTransfer_neg_of_slice_zero`,
  `XiSliceKKLScaleOffLineDetection.lean:772`) [S].
  - The loss from linear `δ/(96(c+1))` (under regular growth) to `δ²` is the three-radii bound: "the worst case of
    `≍ log t` zeros clustered near `½ + it`".
  - Consequences: every-height positivity at rate `κ₀(δ₀)` excludes `Re ρ ≥ ½ + δ₀` above `e^{16}`
    (`re_lt_of_heat_rate_pos`), and `Λ ≥ κ₀(δ)/log Im ρ` for every off-line zero.
- **Isolated pair.** If the cofactor varies little on scale `√λ`, `λ_WD ≥ b²/3`
  (`XiSliceHeatIsolatedPairThreshold.lean`) [S].

## K10. Rigidity, fakes, realizations

- **Simple pole.** A completed positive system with pole budget `1` is `Kζ`. Mechanism: PD vertical sections of
  `−F'/F`, Hadamard `Re Λ'/Λ ≥ 0` and `G ≤ 4√x` give complete monotonicity, then a Bernstein–Widder Dirichlet measure,
  then FE plus finite-order rigidity give `μ = mΣδ_k` (`completedPositiveSystem_one_one_eq_zeta`,
  `StripBochnerWeilForcing/TheSimplePoleClassIsZeta.lean`) [S].
- **Λ ≥ 0 with the exact FE does not force the line** (`RHTower/LambdaPositiveFunctionalEquationOffLine.lean:441`,
  `RHTower/EntireFunctionalEquationOffLine.lean:294`) [S].
  - `F = ζG` with rational `G`. A nonnegative reflection-antisymmetric correction needs a positive coefficient at a real
    leading frequency, hence a real pole.
  - At `w = ½` the pole sits at `s = 1`, giving `G = (s−ρ)(s−ρ̄)(s−1+ρ)(s−1+ρ̄)/[s(s−1)]²`.
  - The completed function `ξ·quartet` is then entire of order one. `F` has a pole of order `3` at `s = 1`; the order of
    that pole is the distinguishing datum.
- **Golden datum** (`q = 5`, `β = (φ, φ⁻¹)`, `ArithmeticCastelnuovoSeveri/FakeCurvesAndTheWindowLaw.lean:118`) [S]:
  - it has an integral zeta series, integral counts and the FE pairing, and satisfies the upper Lefschetz bound with
    `C = 0`;
  - it is not unitary and fails Bézout on its window surface (`selectivityBattery_goldenDatum_nonObject`);
  - its trace sequence is not PD (`not_isEvenPosDef_goldenDatum_traceSeq`);
  - no finite divisor saves its Hodge index (`goldenDatum_no_finite_divisor`).
- **Jensen polynomials of ξ.** The binomial homogenizations are Lorentzian because the Taylor coefficients of `ξ(½ + x)`
  form a Turán sequence (`RHTower.xi_centre_turanSeq`). Hence Laguerre's inequality holds on `s ≥ 0`; this is weaker
  than real-rootedness for degree `≥ 3` (`ArithmeticLorentzianGeometry/LorentzianPolynomialsAndTheTuranLayer.lean:319`)
  [S].
- **Li coefficients.** The first `68` are nonnegative, termwise, from `γ² ≥ 431/2` (`re_xiLiPaired_nonneg_of_le_68`) [S].
- **Sign twins** share the prime form (K6). The successor bias of a Legendre twin is `−1/p` (M8).

## K11. Statistics in the strip

- **Census and density.** The census (G2), Guth–Maynard and Vinogradov–Korobov (G12), Selberg near-line density (K4) and
  fixed-σ density `o(T)` via Littlewood's count (`eventually_zeroCount_fixedSigma_le`,
  `RHTower/ZetaFixedSigmaDensity.lean:151`) [S/X].

## K12. The 𝔽_q contrast (statements read in the cited modules)

- Index zero is the lower count `N_k ≥ q^k + 1 − Cq^{k/2}` (`global_law_count`).
- The upper count misses exactly a real outer eigenvalue (K10).
- No finite frequency divisor rescues a fake curve's Hodge index, while ζ's failure at degree `a` is confined to
  `#lowGrid(a) + 1` low frequencies (K2).
- One prime tower decides over `𝔽_q`; over ℤ two primes are needed for one-sided bounds (M3).
