# Trans-Threshold Pair Correlation (TTPC)

**One question.** The explicit-formula Gram matrix of a band-limited test at height `T` certifies a
proportion `2 − κ` of zeros on the line, `κ` its normalized Frobenius norm. Below prime cutoff `X = T`
Montgomery–Vaughan kills every off-diagonal prime pair and the method stops at `2/3`. What signed
information about prime pairs beyond `X = T` lowers `κ`, and how much is needed for `3/4`?

Parameter: **bandwidth** `λ`, `X = (T/2π)^λ`. Objects: off-diagonal prime-pair kernels of the Frobenius
norm, the mixed Dirichlet mean values they reduce to, the form factor `F(α)` on `α > 1`. Target:
`2 − κ(λ)`. A zero-proportion programme, not an RH route. Everything is unconditional;
`RHTower.PrimeSurplusFourThirds` and `CoalescentSurplusAtMost β` appear only as premises.

Namespace `GaloisForLFunctions.TransThresholdPairCorrelation`; umbrella `TransThresholdPairCorrelation.lean`.

---

## 1. Place in the research

The square-root threshold `X ≍ T` in its plainest form: the input that blocks `3/4` is the **signed
correlation of close prime pairs** `|log(n/m)| ≲ 1/T`, which no upper-bound sieve and no size-only
Hilbert inequality controls. Unit: `(λ, 2 − κ(λ))`, or the share of the `1/18` budget paid.

| Programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Rank–trace inertia: `(2−κ)N` and no evaluation-Gram functional does better (coalescence blind spot at `λ=1`). Two routes to `3/4`: zero-side slack or prime surplus at `4/3`. TTPC is the engine of the second; ACS turns budgets into proportions (`CoalescentSurplusAndTransThresholdProportionLaws`) |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Phase transition of `L²` Hilbert methods at `X = T`; TTPC is its open problem made finite |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | `2/3` as a resolution limit: double zero and coalescing pair share a shadow |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Its band `|ξ| ≤ √N` is `λ = 2` |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Single-height prime-ratio Schur constant; close-pair kernel is its height average |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Sieve parity barrier: close pairs bounded only by size, factor two off |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Log-free large sieve; balanced-scale statistics need signed prime-row input too |
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Needs single-height prime saving; TTPC needs the height average at longer length |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Nyquist rank bound reads `N ≍ T` as a section count |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Same mean-value diagonal `X ≍ T` cuts the damping chain at half damping; shared tool, different obstruction |

`RHTower` owns the Gram infrastructure: wide trace, surplus split, diagonal constant
(`RHTower.diagonal_main_le`), prime–pole cross bound (`RHTower.abs_Mform_PX_PiX_params43_le`), conditional
`3/4` (`RHTower.zeta_three_quarters_of_prime_surplus`), Jackson-weighted Frobenius entries, weighted seam
(`RHTower.seamA_weighted`), exchange rate above `λ=1` (`RHTower.opt_sub_two_thirds`).

---

## 2. Why

**Rank–trace and `2/3`.** A test on `[−L, L]`, `L = λl`, `l = log(T/2π)`, gives a `d×d` Gram on the grid
`τ_k = T + kh`, `h = 2π/L`, from `ν_X = μ + Π_X + P_X`, `P_X(τ) = −π⁻¹Σ_{n≤X}Λ(n)n^{−½}cos(τ log n)`. Poisson
on the grid identifies `tr(G̃²)` with `𝓜[ν_X,ν_X] = ∬Φ(τ−τ')²ν_X(τ)ν_X(τ')` up to an end form `E`. Split:
**core** (archimedean, pole, prime diagonal `𝒟`) evaluates to `(1/λ + λ/3 + o(1))(aL)²Tℓ₁/2π`; **surplus**
carries the off-diagonal pairs `𝒪₁` (difference frequency), `𝒪₂` (sum frequency), prime–pole, end
effect. For `λ ≤ 1` frequencies are `1/T`-separated, MV gives `𝒪₁ = o(Tl³)`, `κ = 1/λ + λ/3`, min `4/3` at
`λ=1`: proportion `2/3` (`ArithmeticCastelnuovoSeveri.subthreshold_cert_le_two_thirds`).

**Four thirds.** At `λ = 4/3` the core is `43/36 = 5/4 − 1/18`; the target `κ ≤ 5/4` (⇒ `3/4`) needs
`primeSurplus ≤ (1/18 + o(1))(aL)²Tℓ₁/2π`. Spectrally: `∫_1^{4/3}(4/3−α)F(α)dα ≤ 1/9`, twice GUE.

**Close pairs and signs.** Beyond `λ = 1` frequencies can be `T^{−4/3}` apart; in the **coalescent band**
`|log(n/m)| ≲ T⁻¹` the window cannot resolve them, absolute Hilbert bounds lose `T^{λ−1}`. Trivial size
`l²T^{4/3}` vs budget `Tl³`: save `T^{1/3}` *and* land below an explicit constant. Sieves need weights
`≥ 0`; the height phase `(m/n)^{iT}` changes sign.

---

## 3. Objects and language

| Object | Definition | Lean |
|---|---|---|
| Difference-frequency kernel | `A⁻(y,y') = ∬Φ(τ−τ')²cos(τy−τ'y')`; cos/sin parts | `Aminus`, `AminusCos`, `AminusSin`, `Cp`, `Sp` |
| Off-diagonal sums | full, cosine, sine, Fourier-weighted | `ppOffDiag`, `ppOffDiagCos`, `ppOffDiagSin`, `ppOffDiagFourier` |
| Prime Dirichlet polynomials | `C_w`, `S_w` | `primeDirichletCos`, `primeDirichletSin` |
| End-effect form | grid minus continuous | `endForm` |
| Jackson pair kernel | supported in `|θ| < 4b` | `jacksonPairKernel`, `jacksonCloseApprox` |
| Form-factor Frobenius norm | `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F` | `frobeniusFormFactor`, `transThresholdIntegral` |
| Prime-surplus ratio | `(9/8)(I − 1/18) − 1/144` at `4/3`; general λ | `primeSurplusRatioOfIntegral`, `generalPrimeSurplusRatio` |
| Affine models | `F = β + γ(α−1)` on `α > 1` | `affineTransModel` |
| Dyadic cosine kernel | `(sin 2u − sin u)/u` | `dyadicCosineKernel` |
| Narrow-strip energy / gain | `E(δ)`; gain under `Bδ²/(1+δ)²` | `narrowStripCesaroEnergy`, `narrowStripGain` |
| Window profile | smooth `u ∈ [0,1]`, collar `ε₁` | `WindowProfile`, `exists_windowProfile` |
| Coalescent sums | `π⁻¹a_na_m g(log m)Ω̂(log n − log m)` on `0<|log(n/m)|≤θ₀`; prime-only; odd primes at even shifts | `coalSum`, `primeCoalSum`, `primeCoalescentSurplus`, `oddEvenShiftPrimeCoalescentSurplus` |
| Budget predicates | `≤ (β+o(1))N(T,2T)` | `PrimeCoalescentSurplusAtMost`, `ArithmeticCastelnuovoSeveri.CoalescentSurplusAtMost` |

**Words.** Sub-/trans-threshold: `λ ≤ 1` / `λ > 1`. Coalescent band: `|log(n/m)| ≲ T⁻¹`. Close/far pair
for a Jackson width `b`: `|log(n/m)| < 4b` / rest. Budget: `1/18` of `(aL)²Tℓ₁/2π` at `λ = 4/3`.

---

## 4. Mechanisms

1. **Parity split; sine part nonsingular.** For even `Φ` eight half-line moment terms collapse to two
   (`ppOffDiag_eq_cos_add_sin`); `S⁺` Lipschitz ⇒ `|A⁻_sin| ≤ 2∫Φ²|x|` (`abs_AminusSin_le`).
2. **Cosine part = mixed Dirichlet mean value.** `C⁺(y) → πg(y)` with `O(T⁻²)` tail; MV on the tail
   (`exists_abs_ppOffDiagCos_sub_fourier_params43_le`); exact identity
   `ppOffDiagFourier = 2π∫_T^{2T}(C_gC_1 + S_gS_1) − 2πTΣa_n²g(log n)`, diagonal cancels
   (`ppOffDiagFourier_eq_primeDirichlet_integral`, `abs_ppDiag_add_ppOffDiagFourier_sub_integral_le`).
3. **End effect split bilinearly** along `μ + Π_X + P_X`; archimedean part `X`-free, `O(Ll³ log l)` for
   `λ ≤ 2` (`endForm_nuX_split`, `exists_abs_endForm_mu_mu_le`).
4. **Jackson grid weights** make pair kernels vanish for `|θ| ≥ 4b`; far pairs and sum frequencies paid
   by outer Jackson mass (`jacksonPairKernel_eq_zero_of_le_abs`, `abs_weighted_frobenius_pp_sub_closeKernel_le`).
   Cubic tails stop it at `b ≫ T^{−5/9}`, short of the coalescent band.
5. **Form-factor bridge.** `κ(4/3) ≤ 5/4 ⇔ I ≤ 1/9` (`frobeniusFormFactor_four_thirds_le_five_fourths_iff`);
   prime diagonal carries `3/16` of trans-threshold mass; surplus `(9/8)(I−1/18) − 1/144`
   (`primeSurplusRatio_bridge`); GUE gives `−1/144` (slack `1/16`). Barriers: positive spectral majorants
   miss by `8/3` (`fejer_shifted_bound_gap`); higher moments force `kλ ≤ 1` (`higherMoment_rudnick_sarnak_cap`).
6. **Height averaging** at fixed `L`: far pairs `|log(n/m)| > T^{−1+η}` and sum frequencies negligible
   (`abs_avg_ppOffDiag_sub_close_le`, `abs_avg_ppSumFreq_le`); at fixed λ the moving cutoff costs `√ε X log²X`.
7. **Fejér/Lorentz mean squares**: exact positive pair sum against Fejér (`integral_fejer_mul_PX_sq`);
   Lorentz `(R + X)` mean value without Hilbert (`integral_lorentz_mul_PX_sq_le`) — a size bound.
8. **Smooth grid weights**: exact weighted-kernel difference, Lorentz grid sums (`KfunW_sub_mul_Kfun_eq`,
   `sum_lor_grid_le`); no aliasing, no end form, no moving cutoff.
9. **Smooth-window certificate.** Weighted trace loses only its collar (`trace_ge_at`); weighted Frobenius
   = `L²` × smooth form (`abs_weightedFrobenius_sub_smoothForm_le`); nine channels (`smoothPair_nuX_le`):
   core `43/36`, exact coalescent kernel, far/sum paid by `Ω̂` decay, prime–pole by Lorentz Cauchy–Schwarz.
   Assembled (`zeta_coalescent_certificate`, `zeta_coalescent_certificate_four_thirds`):
   `N₀*(T,2T) ≥ (29/36 − ε)N(T,2T) − coalescentSurplus`. `29/36 − 3/4 = 1/18`.
10. **Budget ladder** (ACS): `β < 5/36` beats `2/3`; `β ≤ 577/4500` beats `HD(1)`; `β ≤ 1/18` gives `3/4` and
    off-line moment `57/1000`; HL value `β = −1/144` gives `13/16`
    (`coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters`); two-window mixture reaches `3/4`
    iff `F ≤ B ≤ 2954/1035` (`mixOpt_values_and_three_quarters_criterion`).
11. **Prime-power elimination and parity reduction.** Sub-Nyquist terms vanish
    (`coalSum_term_eq_zero_of_lt_inv`); `p = 2` has no coalescent partner for `θ₀ < 1/3`, so only odd primes at
    even shifts remain (`primeCoalSum_eq_oddEvenShiftPrimeCoalSum`); proper prime powers cost
    `O(T^{−1/3+η}N)` (`eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le_mul_Ncount`), so
    `CoalescentSurplusAtMost β ↔ PrimeCoalescentSurplusAtMost β` for `0 < η < 1/3`
    (`coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost`). 2-adic parity halves the 2D Selberg
    prime-pair bound and lifts the shift restriction (`sum_card_primePair_le_parity_unrestricted`).
12. **Model calibration.** Coalescent linearization `T log(1+h/m) → Th/m` (`coalescent_sum_linearization_bound`);
    Frullani kills the Poisson linear term against the dyadic kernel (`abs_integral_dyadic_frullani_le`);
    HL deficit `−½ log H` integrates to `−(L−l)³/12 < 0` (`hl_coalescent_deficit_integral`). Five models at
    `4/3` (`calibration_five_models_four_thirds`): HL/GUE `−1/144`; uncorrelated `0`; Poisson without
    repulsion `+1/16` (fails); spectral sieve `F ≤ Υ` meets budget iff `Υ ≤ 2`; unsigned additive sieve needs
    `Υ ≤ 8/9`. The budget uses arithmetic repulsion.
13. **Lobe cancellation and Ramanujan transfer.** Unsigned shift sums of `|cosTransform Ω|` diverge with
    the inner lobe `K₁ ≍ T^{α−1}` (`sum_Icc_abs_cosTransform_ge_inner_lobe`); signed sums obey the trapezoidal
    Dirichlet identity (`two_sin_mul_trapezoidal_sum_cos`). Ramanujan lag coefficients cancel the `1/θ` pole
    across `d ∣ q` (`trapezoidal_ramanujan_cos_eq`), bounds uniform in period count
    (`abs_sum_ramanujanLagCoefficient_mul_cos_add_le`); weighted by `μ²/φ²` the singular-series sum transfers
    to the negative Ward–Mertens repulsion sum (`abs_sum_singularSeries_cosTransform_add_le`).
14. **Narrow strip** `λ = 1 + δ`: gain `δ(2 − (3E−4)δ)/(3(1+δ)²)`, beats `2/3` iff `E(δ) < 2/(3δ) + 4/3`
    (`narrowStrip_beats_two_thirds_iff`); odd-odd close-pair terms vanish up to `X = 2/b`
    (`odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b`); a quadratic bound `β ≤ Bδ²/(1+δ)²` gives gain
    `(3B²+7B+3)/(9(B+1)²(3B+2))` at `δ* = 1/(3B+2)`, half kept after collar (`narrowStrip_optimal_delta_gain`,
    `narrowStrip_collar_preserves_gain`).

---

## 5. Pillar theorems

1. Sine part nonsingular; cosine part = mixed Dirichlet mean value (`abs_AminusSin_le`, `ppOffDiagFourier_eq_primeDirichlet_integral`).
2. Archimedean end effect `X`-free (`exists_abs_endForm_mu_mu_le`).
3. Budget = form-factor bound; Fejér and Rudnick–Sarnak barriers (`primeSurplusRatio_bridge`, `fejer_shifted_bound_gap`, `higherMoment_rudnick_sarnak_cap`).
4. Height averaging leaves only the coalescent band (`abs_avg_ppOffDiag_sub_close_le`).
5. **Smooth-window certificate at `4/3`** (`zeta_coalescent_certificate`).
6. **Reduction to odd primes at even shifts** (`coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost`, `eventually_primeCoalescentSurplus_eq_oddEvenShift`).
7. Calibration: the budget needs repulsion (`calibration_five_models_four_thirds`, `hl_coalescent_deficit_integral`).
8. Signed lobe cancellation and Ramanujan pole cancellation (`sum_Icc_abs_cosTransform_ge_inner_lobe`, `trapezoidal_ramanujan_cos_eq`).
9. Narrow-strip exchange rate (`narrowStrip_beats_two_thirds_iff`, `narrowStrip_optimal_delta_gain`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Triangle inequality on the eight moments | `O(L²X) ≫ Tl³` for `λ > 1`; loses all cancellation |
| Sharp window `1_{[T,2T]}` | Endpoints leak `O(1/|θ|)`; smooth or Jackson weights needed |
| Jackson reaches the coalescent band | Cubic tails force `b ≫ T^{−5/9}` at `4/3` |
| Height averaging at fixed λ | Moving cutoff costs `√ε X log²X`; average at fixed `L` |
| Prime–pole channel by sup norms | `≍ LT^{4/3}`; use Lorentz Cauchy–Schwarz |
| Lorentz mean value on close pairs | Size bound; the problem is signed |
| Positive spectral majorants | `8/27`, factor `8/3` short of `1/9` |
| Higher moments bypass pair correlation | `kλ ≤ 1` |
| `PrimeSurplusFourThirds` / `CoalescentSurplusAtMost` established | Premises only; the reduction is the content |
| Budget = power saving | Must land below `1/18` against a truth of `−1/144` |
| Sieve bounds close pairs | Signed phase ⇒ size bound, factor two (parity) |
| Poisson model = HL main term | Poisson without repulsion `+1/16` fails; budget uses `−½ log H` |
| Close-pair threshold prime-blind | Odd integers double it to `2/b` |
| Pair correlation beyond `α = 1` is a separate input | Equivalent (under RH) to prime-pair correlations with power-saving error |
| Zero-side slack below `3/4` | Refuted at every `λ ∈ (0,3/4)` (`ArithmeticCastelnuovoSeveri.not_three_quarters_zeroSideSlack_of_lt_three_quarters`) |
| Mollifiers instead of `λ > 1` | CGG optimum `1 − (1+θ)^{−3}`; `3/4` needs `θ ≥ 4^{1/3} − 1` (`RHTower.CGGMollifier.three_quarters_le_iff`) |

---

## 7. Open problems

1. **Coalescent surplus at `4/3`**: `oddEvenShiftPrimeCoalescentSurplus u η T ≤ (1/18 + o(1))N(T,2T)` for one
   profile, one `0 < η < 1/3` — odd primes at even shifts within `T^{−1+η}`. Every intermediate β is a result.
2. **Signed sieve transfer**: carry the trapezoidal lobe cancellation to `1_ℙ(m)1_ℙ(m+2r)`; size-only sieves
   diverge on the inner lobe.
3. **Singular-series error**: unconditional additive-divisor control of prime-pair correlation minus its
   truncated HL singular series, integrated against the signed coalescent kernel, below the budget,
   uniformly in the moving cutoff (pointwise upper sieves, unweighted counts and non-uniform asymptotics
   do not pay it).
4. **Finite sum → form factor**: transfer the height-averaged prime-pair sum to `F(α)` on `(1, 1+δ]`.
5. **Narrow-strip quadratic bound** `β(δ) ≤ Bδ²/(1+δ)²` for the signed coalescent sum.
6. **Signed mixed mean value** `∫_T^{2T}(C_gC_1 + S_gS_1)` at `X = T^{4/3}`.

---

## 8. Tools

Built: parity splitting; second-moment tail reduction and exact mean-value identity; bilinear end-effect
split; Jackson weights; height averaging; Fejér/Lorentz mean squares; smooth grid weights; form-factor
calculus; coalescent linearization and Frullani calculus; narrow-strip calculus and 2-adic collar;
smooth-window certificate; prime-power elimination and parity-halved 2D Selberg; trapezoidal
Dirichlet–Ramanujan transfer. To build: the bounds of open problems 1, 3, 4.

---

## 9. Working conventions

State bandwidth, window (sharp/smooth/Jackson) and normalization of every estimate. Keep oscillating
kernels signed until a cancellation is used. Separate reduction, model calculation, and estimate on
actual primes. Report the unit: bandwidth and proportion, or share of `1/18`. Gram/trace/Jackson
infrastructure is in `RHTower` (`ZetaTraceWide`, `ZetaFrobeniusSurplusSplit`, `ZetaThreeQuartersOfPrimeSurplus`,
`ZetaWeightedFrobeniusClose`, `ZetaWeightedFrobeniusFar`).
