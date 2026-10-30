# Reboot-final: mathematical facts read from the Lean corpus

Facts only. Each entry names its Lean anchor (path relative to `formal/GaloisForLFunctions/`).
[S] = statement and proof read. [D] = statement and module docstring read. [X] = the corpus states
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
