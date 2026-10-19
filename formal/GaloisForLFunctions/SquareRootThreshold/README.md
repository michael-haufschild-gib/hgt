# Square-Root Threshold (`GaloisForLFunctions.SquareRootThreshold`)

**One question.** At height `T`, which information in the explicit formula makes an individual
off-line zero visible, and which unconditional mechanisms can reach that information?

Background ([`docs/reports/review-1910/opus.md`](../../../docs/reports/review-1910/opus.md)):
* every live RH route is already at full height: its open inequality is RH-equivalent or a
  quasi-RH half-plane statement;
* every positivity route leaves the same unpaid term, the signed prime−polar pairing;
* the difficulty sits at the height `T` and at the resolution of the local zero spacing
  `2π/log T`.

SRT states every problem at a given height and resolution, and pairs **visibility** theorems with
**invisibility** theorems.

---

## 1. Motivation

A test `f` supported in `[-a, a]` (the *aperture* `a`) reads the prime powers up to `X = e^{2a}`
and resolves ordinates only to scale `π/a`. Zeros near height `T` are spaced by `2π/log(T/2π)`. A
Dirichlet polynomial of length `X`, averaged over a height window of length `ℓ`, is controlled by
its diagonal exactly when `X ≲ ℓ`.

The lattice law `RHTower.offLineLattice_weil_positive_iff` shows that a dense off-line
configuration becomes visible only above the Nyquist aperture `L/2`, whatever its depth. For the
zeros of `ζ` this means prime length beyond `T`: this is the **square-root threshold**.

---

## 2. Objects and language

The objects come from `Zeta23` (`formal/.lake/packages/Zeta23`) and the RHTower lattice module. Do
not redefine them.

| Object | Meaning | Lean |
|---|---|---|
| Paper Fourier transform | `h_f(z) = ∫ f(u) e^{izu} du` | `Zeta23.paperFT` |
| Zero ordinate | `γ_ρ = (ρ − ½)/i`; `Im γ_ρ = ½ − Re ρ` | `Zeta23.gammaOf` |
| Depth | `δ = |Re ρ − ½|` | — |
| Zero configuration | locally finite multiset in the strip, invariant under `ρ ↦ 1 − ρ̄` | `Zeta23.ZeroConfig` |
| Weil form | `W(f,g) = Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))` | `Zeta23.ZeroConfig.W` |
| Weil kernel | `k = f ⋆ g̃`; `h_k(z) = h_f(z) conj(h_g(conj z))` | `Zeta23.EF.weilTest`, `EF.paperFT_weilTest` |
| Zeros of `ζ` | with the explicit formula | `Zeta23.zetaZeroConfig`, `WeilEF.EF_lit_zetaZeroConfig` |
| Lattices | doubled on-line lattice / off-line lattice pair of spacing `2π/L` | `RHTower.onLineLatticeConfig`, `RHTower.offLineLatticeConfig` |
| Height shift | `S_ξ f(u) = e^{2πiξu} f(u)`, so `h_{S_ξ f}(z) = h_f(z + 2πξ)` | `heightShift` |
| Window slice | `g_s(u) = f(u + s) η(u)` | `windowSlice` |
| Windowed Weil form | the Weil form of `k_f · k_η`; equals `∫ |h_η(−2πξ)|² W(S_ξ f, S_ξ f) dξ` | `windowedW` |
| Tempered configuration | `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞` | `TemperedConfig` |
| Pair energy | `S(a) = ∫_{-a}^{a} sinh²(δu) du = sinh(2δa)/(2δ) − a` | `pairEnergy` |
| Exponential sum | `Q(ξ) = Σ_j c_j e^{2πiξν_j}` | `expSum` |
| Prime polynomial | `Π_f(ξ) = Σ_{2≤n≤X} Λ(n) n^{−1/2}(k_f(log n) n^{2πiξ} + k_f(−log n) n^{−2πiξ})` | `primePolynomial` |
| Archimedean–pole part | `A_f(ξ) = h_k(i/2) + h_k(−i/2) + ∫ h_k μ` with `k = S_ξ f ⋆ (S_ξ f)~` | `archPart` |
| Diagonal energy | `V_f = Σ_{2≤n≤X} Λ(n)²/n (|k_f(log n)|² + |k_f(−log n)|²)` | `primeVariance` |

**Words.**
* **Visible at aperture `a`:** some `C²` test supported in `[-a, a]` makes `Re W(f, f) < 0`.
* **Invisible:** the form is nonnegative on all such tests.
* **Dense:** off-line points spaced like the background.
* **Isolated:** one reflected off-line pair inside an on-line background.

---

## 3. Mechanisms

1. **Lag representation.** `W(f,g) = Σ_ρ m_ρ h_k(γ_ρ)`. An aperture-`a` test sees the
   configuration only through lags `|v| ≤ 2a`. A depth `δ` enters through the weight `e^{±δv}`.
2. **Poisson on lattices.** On a lattice of spacing `2π/L` the zero sum becomes
   `L Σ_m k(mL) e^{±δmL}`. Below `L/2` only the lag-zero atom survives.
3. **Rank-two pair estimate.** A reflected pair contributes `2 Re(A conj B)` with
   `A = ⟨F, e^{δ·}⟩` and `B = ⟨F, e^{−δ·}⟩`. On `[-a, a]` this is at least
   `(2a − sinh(2δa)/δ)‖F‖²`, with equality at `F = sinh(δ·)`.
4. **Slice factorization.** `k_f · k_η = ∫ k_{g_s} ds`, and every slice lies in the support of
   `η`.
5. **Height averaging.** `k_η(v) = ∫ |h_η(−2πξ)|² e^{2πiξv} dξ`. So windowed forms are height
   averages of localized forms.
6. **The pole is a pair.** The pole terms `h_k(i/2) + h_k(−i/2)` have the shape of a depth-`½`
   pair at height `0`. For an odd real profile they equal `−2(∫ f sinh(u/2))²`. The pole of `ζ` at
   `s = 1` is the contribution of the whole infinite prime tail.
7. **Windowed Gram identity.**
   `∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = Σ_{j,k} c_j c̄_k k_η(ν_j − ν_k)`. Since `k_η` vanishes beyond
   `2r`, only pairs of frequencies closer than `2r` interact.
8. **Height phase of prime pairs.** At height `T` a pair `(n, m)` enters with the phase
   `(m/n)^{iT}`. In Zeta23 this is the kernel `Aminus`, an integral over `t ∈ [T, 2T]`. For
   `m = n + h` the phase `e^{iTh/n}` changes sign as `n` varies.

---

## 4. Theorems

### Visibility of isolated pairs

Module [`IsolatedOffLinePairVisibilityLaw`](IsolatedOffLinePairVisibilityLaw.lean).
* `isolatedPairConfig_weil_nonneg_iff`: one pair of depth `δ` in a doubled on-line lattice of
  spacing `2π/L` is invisible at aperture `a ≤ L/2` iff `sinh(2δa)/δ ≤ 2L + 2a`.
* `isolatedPairConfig_weil_nonneg_nyquist_iff`: the pair is visible below the Nyquist aperture iff
  `sinh(δL) > 3δL`, i.e. `δL > x₀ ≈ 2.84`.
* `isolatedPairConfig_weil_nonneg_of_le_log`, `exists_re_W_isolatedPairConfig_neg_of_log_le`:
  deep pairs are visible at aperture `≈ (1/2δ) log(4δL)`.

Module [`DepthGapVisibilityLaw`](DepthGapVisibilityLaw.lean).
* `re_W_modulatedTest_le_of_depthGap`: suppose the neighbours of `ρ₀` within ordinate distance `R`
  have depth `≤ δ'`. Then
  `Re W ≤ −2m_{ρ₀}P² + 384 A₀ log(|γ₀| + 3) N² (e^{2δ'a} + e^a/(1 + R))`.
  So `ρ₀` is visible once `2(δ − δ')a ≳ log(A₀ log γ₀)`.
* `zeta_weil_positive_forces_deep_companion`: if `ζ` is Weil-nonnegative at aperture `a`, every deep
  zero has a companion of depth `> δ'` within `R`.
* `δ' = 0` is `RHTower.re_W_modulatedTest_le_of_isolated`; `δ' = δ` is the lattice
  invisibility.

### Window and height averages

Modules [`WindowedWeilFormSliceTransfer`](WindowedWeilFormSliceTransfer.lean),
[`WindowedPositivityNoGoForOffLineConfigurations`](WindowedPositivityNoGoForOffLineConfigurations.lean),
[`HeightWindowAverageRepresentation`](HeightWindowAverageRepresentation.lean),
[`ZetaSmallApertureHeightWindowPositivity`](ZetaSmallApertureHeightWindowPositivity.lean).
* `windowedW_eq_integral_W`, `re_windowedW_nonneg_of_aperture_nonneg`: for tempered
  configurations, positivity at aperture `r` makes every windowed form with window in `[-r, r]`
  nonnegative, at every aperture of the test.
* `windowedW_offLineLattice_eq_onLine`, `exists_offLine_lattice_windowed_nonneg`,
  `exists_isolatedPair_windowed_nonneg`: off-line configurations of every depth pass all window
  averages at a fixed resolution.
* `windowedW_eq_integral_heightShift`: windowed forms are height averages.
* `zetaZeroConfig_re_W_nonneg_of_small_aperture`: `ζ` is Weil-nonnegative at aperture `e^{−50}`.
* `re_integral_heightShift_zetaZeroConfig_nonneg`: the height averages of `ζ` with windows of
  aperture `e^{−50}` are nonnegative for tests of every aperture.
* `integral_heightShift_offLineLattice_eq`: the off-line lattice of spacing `πe^{50}` has the same
  averages at every depth.

### Single heights

Module [`ZetaSingleHeightPositivityAboveArchimedeanHorizon`](ZetaSingleHeightPositivityAboveArchimedeanHorizon.lean).
* `zetaZeroConfig_re_W_heightShift_ge`:
  `Re W_ζ(S_ξ f) ≥ (log(1 + π|ξ|/4) − 10 − 68√X − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`.
* `exists_zetaZeroConfig_re_W_heightShift_nonneg`: every fixed profile is nonnegative at all large
  heights. The range `X ≲ (log T/68)²` is the visibility range of depth-`½` zeros.

### Mean squares below and beyond the threshold

Modules [`WindowedMeanValueDiagonalLaw`](WindowedMeanValueDiagonalLaw.lean),
[`ZetaLocalizedFormWindowedVarianceLaw`](ZetaLocalizedFormWindowedVarianceLaw.lean),
[`WindowedOffDiagonalBeyondThreshold`](WindowedOffDiagonalBeyondThreshold.lean).
* `integral_normSq_mul_normSq_dirichletSum`: if `2rX ≤ 1`, Dirichlet polynomials of length `X`
  are seen exactly diagonally.
* `zetaZeroConfig_W_heightShift_eq_sub`: `W_ζ(S_ξ f) = A_f(ξ) − Π_f(ξ)`.
* `integral_windowed_sq_deviation_eq`: below the threshold the windowed mean square of
  `W_ζ − A_f` is `‖η‖² V_f`.
* `exists_primeVariance_le`: `V_f ≤ 2‖f‖⁴ · 2a(2a + C)`.
* `lintegral_bad_heights_le_of_height`: the window proportion of heights with `Re W_ζ < 0` is at
  most `V_f/A₀² = O((log X/log T)²)`.
* `integral_pairTransform_mul_normSq_expSum_eq_diag_add`: the mean square is the diagonal plus the
  off-diagonal over pairs with `|ν_j − ν_k| < 2r`.
* `integral_normSq_mul_normSq_expSum_le`, `card_close_log_le`, `integral_windowed_sq_deviation_le`:
  at every length, the windowed mean square of `W_ζ − A_f` is at most
  `‖η‖² V_f (1 + X(e^{2r} − e^{−2r}))`.
* `le_integral_normSq_mul_normSq_expSum_of_nonneg`: for nonnegative coefficients and windows, every
  off-diagonal term is nonnegative. So bounds that use only the sizes `|c_j|` cannot beat the
  `O(rX)` excess.
* `integral_pairTransform_mul_integral_windowed_eq`: averaging over centres with a second window
  `ω` weights each pair by `k_η k_ω(ν_j − ν_k)`. The averaged excess is a correlation of prime
  pairs at multiplicative distance `< 2 min(r, ρ)`.
* `integral_pairTransform_mul_integral_windowed_centred_eq`: centred at height `T`, each pair
  carries in addition the phase `e^{2πiT(ν_j − ν_k)}`, which for prime pairs is
  `(m/n)^{2πiT}` (mechanism 8).

### The prime–tail coupling

Module [`PrimeTailCouplingCriterion`](PrimeTailCouplingCriterion.lean).
* `riemannHypothesis_iff_primePolynomial_le_archPart`: RH holds iff `Re Π_f(ξ) ≤ Re A_f(ξ)` for
  every aperture, profile and height.
  * The left side involves only the prime powers `n ≤ e^{2a}`.
  * The right side is the pole, i.e. the infinite prime tail, plus the archimedean term, i.e. the
    zero density.
* `exists_archPart_zero_lt_primePolynomial`: the archimedean–pole side cannot be frozen at one
  height. Take the odd profile `sinh(u/2)(a² − u²)₊^{5/2}` at large `a`.
  * `pole_terms_odd_eq`, `integral_norm_sq_paperFT_mul_mu_le`: `Re A_f(0) < 0`.
  * `exists_lt_re_primePolynomial`: the prime polynomial, with windowed mean zero, exceeds this
    value somewhere.
* `re_primePolynomial_zero_neg`: under RH the prime polynomial of this profile is negative at
  height `0`. The finitely many primes must cancel the pole.
* `primePolynomial_le_archPart_iff_poleCompression`: the criterion is equivalent to the rank-two
  inequality `RHTower.riemannHypothesis_iff_weilPoleCompression_nonneg`, a `2 × 2` prime–Gamma
  inequality on the pole directions `e^{±u/2}` at every aperture. This is the depth-`½` pair sector
  at height `0`.
  * By `RHTower.riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound` it reads
    `|∫₀^t (e^v − ψ(e^v)) dv| ≤ B e^{t/2}`.
* `primePolynomial_le_archPart_of_zetaStronglyRecurrent`: Bagchi's strong recurrence
  (`RHTower.riemannHypothesis_of_zetaStronglyRecurrent`) implies the criterion.
  * Recurrence lives inside the strip, where universality makes local properties free; its
    unconditional shadow is `RHTower.exists_zetaSelfReturn_density_zero`.
  * The coupled criterion uses the global explicit formula; its unconditional shadow is
    `lintegral_bad_heights_le_of_height`.

---

## 5. The regime map

Height `T`, prime length `X = e^{2a}`, height-window length `ℓ ≈ 1/r`.

| Regime | What holds for `ζ` | Calibration |
|---|---|---|
| windows `ℓ ≳ e^{50}`, every `X` | averages nonnegative | off-line lattices pass too |
| single heights, `X ≲ (log T/68)²` | nonnegative | visibility range of depth-`½` zeros |
| windows `ℓ ≥ 2X` | variance exactly diagonal; negative heights `O((log X/log T)²)` | mean value theorem as an identity |
| windows, `X > T` | mean square `≤ ‖η‖² V_f (1 + X(e^{2r} − e^{−2r}))` | sharp for size-only bounds |
| single heights, `X ≲ (log T)^{1/δ}` | visibility under a depth gap `δ − δ'` | without a gap: lattice invisibility |
| all heights and apertures | equivalent to RH and to the rank-two pole inequality | primes cancel the pole at height `0` |

---

## 6. Pitfalls

| Pitfall | What is true instead |
|---|---|
| Treating aperture as a height cutoff | Aperture is a frequency resolution. A small aperture sees deep isolated zeros at any height. |
| Expecting thresholds for finite configurations | A finite configuration with an off-line pair is visible at every aperture. Thresholds come from the density of the background. |
| Expecting averaged information to reach depth | Window averages of resolution `r` are integrals of aperture-`r` Weil forms. Off-line lattices of spacing at most `π/r` pass them. |
| Positivity on a restricted family as evidence for RH | State the family's resolution and compare it with the lattice law first. |
| Weakening to "fixed σ < 1" | These are quasi-RH half-planes, open for every `σ < 1`. |
| Applying an upper-bound sieve beyond `X = T` | The sieve bounds prime pairs only against weights `w ≥ 0`. The height phase `(m/n)^{iT}` changes sign, so the sieve reverts to the size-only bound. |
| Treating `X = T` as a technical limit of one method | It is the diagonal threshold of the mean value theorem, the point where the sieve loses the height phase, and the density-hypothesis threshold of the zero side. |
| Using `Re W` without the conjugation convention | `W(f, f)` uses `conj(h_f(conj γ))`. For an off-line pair it is `2 Re(A conj B)`. |

---

## 7. Open problems

1. **Beyond the square-root threshold.** Bound the off-diagonal prime pairs at bandwidth
   `λ = log X/log T > 1`.
   * The target is the surplus of `RHTower/ZetaThreeQuartersOfSurplus`: the off-diagonal prime
     pairs `Σ_{n≠m} a_n a_m A⁻(log n, log m)` plus the sum frequencies, the prime–pole cross term
     and the grid correction. If `𝒮 ≤ (1/18)·norm` at `λ = 4/3`, then three quarters of the zeros
     are simple and on the line.
   * By `RHTower/PairCorrelationExchangeRate`, a bound `F ≤ B` for the pair correlation on
     `(1, λ)` gives the proportion `(2B − 1)/(3B − 2)`. Every finite `B` beats `2/3`.
   * Each known route stops at `X = T`, for a different reason:
     * **Coefficient sizes.** The excess `O(rX)` is attained for aligned phases
       (`le_integral_normSq_mul_normSq_expSum_of_nonneg`).
     * **Upper-bound sieve.** It requires `w ≥ 0`, but the height phase changes sign
       (mechanism 8). Using the phase requires prime-pair asymptotics with error terms: the
       parity problem.
     * **Zero side.** An off-line zero of depth `δ` has weight `T^{2λδ}`, so the needed estimate is
       `N(½ + δ, T) ≪ T^{1 − 2λδ + ε}`. The density hypothesis gives `λ ≤ 1` exactly.
   * The pair-correlation conjecture is open on `(1, λ)` even under RH.
2. **Depth gaps under clustering.** A configuration may have no depth gap near an off-line zero,
   i.e. a cluster of comparable depths. Find the aperture at which such a cluster of `ζ`-density
   becomes visible. The lattice law gives the answer `L/2` for exact lattices.
3. **Sharper constants.** Improve the small-aperture constant `e^{−50}` towards Yoshida's
   aperture. Replace the horizon `68√X` by the sharp prime-sum constant.

---

## 8. Working rules

1. **Search before proving.** Run `../scripts/formal_tools.py research "<query>"`. The lattice, tilt,
   `paperFT` and explicit-formula tools already exist (Zeta23, `RHTower/ZeroLatticeDepthNyquistLaw`,
   `RHTower/WeilMarkovOddSectorTrivialZeroSquares`, `RHTower/IsolatedDeepZeroWeilDetection`).
2. **Pair every invisibility theorem with a visibility witness,** and conversely.
3. **Calibrate.** Every statement names its resolution or aperture and the strongest unconditional
   value known.
4. **Lean discipline.**
   * Unconditional theorems only; `C²` compactly supported tests.
   * Configurations quantified as classes (finite, lattice, tempered) or concrete (`zetaZeroConfig`).
   * One foreground `lake --old env lean -j 1 -o …` compilation at a time.
   * Imported `#print axioms` audit from a scratch file.
   * Wire new modules into [`SquareRootThreshold.lean`](../SquareRootThreshold.lean).
