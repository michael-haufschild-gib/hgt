# Trans-Threshold Pair Correlation (`GaloisForLFunctions.TransThresholdPairCorrelation`)

**One question.** The explicit-formula Gram matrix of a band-limited test at height `T` certifies
a proportion of the zeros of `ζ` on the critical line, and the proportion is set by the prime
pairs the prime cutoff `X` lets in. Below `X = T` the Montgomery–Vaughan inequality removes every
off-diagonal prime pair and the method stops at `2/3`. What signed information about prime pairs
beyond `X = T` lowers the Frobenius norm of that Gram matrix, and how much of it is needed for
`3/4`?

Trans-Threshold Pair Correlation (TTPC) is the analysis of the prime side of the rank–trace method
beyond the square-root threshold. Its parameter is the **bandwidth** `λ`, with
`X = (T/2π)^λ`; its objects are the off-diagonal prime-pair kernels of the Frobenius norm, the
mixed mean values of prime Dirichlet polynomials they reduce to, and the pair-correlation form
factor `F(α)` on `α > 1`. Its target is the certified proportion `2 − κ(λ)`, where `κ` is the
normalized Frobenius norm. It is a zero-proportion programme, not an RH route. Every theorem is
unconditional; `RHTower.PrimeSurplusFourThirds` and `PairCorrelationFourThirds` appear only as
the premises of stated implications.

---

## Place in the research

The square-root threshold `X ≍ T` is where every positivity and cancellation route of the corpus
stops (Square-Root Threshold, open problem 1). TTPC works at that threshold on the most concrete
quantity available: a finite sum over prime pairs, with an explicit normalization and an explicit
budget. The question it isolates is the signed correlation of close prime pairs
`|log(n/m)| ≲ 1/T`, which no upper-bound sieve and no size-only Hilbert inequality controls.

| Programme | Interface |
|---|---|
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Proves that rank–trace inertia certifies `(2 − κ)N` zeros and no functional of the evaluation Gram alone certifies more, with the coalescence blind spot at `λ = 1`. It has two routes to `3/4`: a zero-side spectral slack, or the prime surplus at `λ = 4/3`. TTPC is the analytic engine of the second, and ACS turns its certificate into budgets for `2/3`, `HD(1)` and `3/4` (§3.12). |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Explains why `L²` Hilbert-inequality methods have a phase transition at `X = T`. TTPC is its open problem 1 made into a finite estimate. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Its band `|ξ| ≤ √N` for a prime polynomial of length `N` is the regime `λ = 2`, beyond the range treated here; below the band Montgomery–Vaughan bounds everything, as below `λ = 1` here. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Its replacement hypothesis is a bounded Schur constant for prime-ratio correlations at one height. The close-pair kernel here is the height-averaged form of the same correlations. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Proves the sieve parity barrier as a sharp theorem in receiver coordinates. Close prime pairs meet the same barrier: an upper-bound sieve bounds them only by size, a factor two off. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies the log-free large sieve with the Montgomery–Vaughan constant. Its balanced-scale single-modulus statistics are the other place where signed prime-row information beyond the large sieve is needed. |
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Needs a single-height prime saving on its aperture face. TTPC needs the averaged-over-height version at much longer prime length. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Its Nyquist rank bound reads the same threshold `N ≍ T` as a dimension count of sections at separated heights. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Reads the two-thirds barrier as a resolution limit: the evaluation Gram is a reading whose shadow contains both a double critical zero and a coalescing pair, so no functional of it certifies more than `(2 − κ)N`. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Its half-damping operator bound for the damping chain cuts a Dirichlet polynomial at the same diagonal `X ≍ T` of the mean value theorem; it shares the tool, not the obstruction. |

`RHTower` owns the explicit-formula Gram infrastructure on which every statement here is built:
the wide-bandwidth trace, the split of the Frobenius surplus, the diagonal constant
(`RHTower.diagonal_main_le`), the prime–pole cross bound (`RHTower.abs_Mform_PX_PiX_params43_le`),
the conditional three-quarters theorem (`RHTower.zeta_three_quarters_of_prime_surplus`), the
Jackson-weighted close and far Frobenius entries, and the exchange rate just above `λ = 1`
(`RHTower.opt_sub_two_thirds`).

On the RH frontier TTPC is a supporting framework of HF and ACS. Its unconditional output is the
actual-`ζ` smooth-window certificate `N₀* ≥ (29/36 − ε)N − coalescentSurplus`; what remains is the
complete near-diagonal signed prime surplus, and a bound `≤ (1/18 + o(1))N` would give `3/4` of the
zeros on the line, not RH.

**The shared target.** The other programmes work on RH as the sign of one critical arithmetic
form. TTPC works one level below, on a proportion of zeros, but at the same wall: what blocks
`3/4` is the signed correlation of prime pairs beyond `X = T`, the square-root threshold in its
plainest form. Its unit is the pair `(λ, 2 − κ(λ))`. A partial result reports the bandwidth it
reaches and the proportion it certifies, or the budget it pays out of `1/18`.

Read §1 for the barrier and the target constant, §2 for the objects, §§3.1–3.5 for the four
reductions and the form-factor bridge, §§3.6–3.8 for the three localization tools (height
averaging, Lorentz mean values, smooth grid weights) and what each can and cannot reach, and §3.11
for the smooth-window certificate that places the whole `1/18` budget on the coalescent band, §3.12
for what each budget gives; §4
lists the pillar theorems, §5 the traps, §§6–7 the questions and open problems.

---

## 1. Why

### 1.1 The rank–trace method and the two-thirds barrier

A band-limited test profile supported on `[−L, L]`, `L = λl`, `l = log(T/2π)`, gives a `d × d` Gram
matrix `G̃ = L⁻¹G` on the vertical grid `τ_k = T + kh`, `h = 2π/L`, `d = ⌊LT/2π⌋`, built from the
explicit-formula density

    ν_X(τ) = μ(τ) + Π_X(τ) + P_X(τ),     P_X(τ) = −(1/π) Σ_{n≤X} Λ(n) n^{−1/2} cos(τ log n),

with `μ` archimedean and `Π_X` the pole part. Poisson summation on the grid identifies the
Frobenius norm `tr(G̃²)` with the continuous form `𝓜[ν_X, ν_X] = ∬_{[T,2T]²} Φ(τ − τ′)² ν_X(τ)
ν_X(τ′)`, up to a grid end-effect form `E(ν_X, ν_X)`. Expanding `ν_X` splits the norm into

* the **core**: `𝓜[μ, μ] + (1/2π²)𝒟 + 2𝓜[μ, P_X] + 2𝓜[μ, Π_X] + 𝓜[Π_X, Π_X]`, with the prime
  diagonal `𝒟 = Σ_{n≤X} a_n² A⁻(log n, log n)`. It evaluates unconditionally at every bandwidth to
  `(1/λ + λ/3 + o(1))(aL)² Tℓ₁/2π`;
* the **Frobenius surplus**: `(1/2π²)(𝒪₁ + 𝒪₂) + 2𝓜[P_X, Π_X] + E(ν_X, ν_X)`, where
  `𝒪₁ = Σ_{n≠m≤X} a_n a_m A⁻(log n, log m)` is the off-diagonal difference-frequency prime-pair sum
  and `𝒪₂` the sum-frequency term. Without the prime–pole cross term it is the **prime surplus**
  `RHTower.primeSurplus`.

Rank–trace inertia turns a bound `κ` on the normalized Frobenius norm into `(2 − κ)N` simple zeros
on the line, and no functional of the evaluation Gram alone does better
(`ArithmeticCastelnuovoSeveri.universal_matrix_functional_barrier`). For `λ ≤ 1` the logarithmic
frequencies `log n`, `n ≤ X ≤ T`, are spaced by at least `1/T`, the inverse length of the window
`[T, 2T]`. Montgomery–Vaughan then gives `|𝒪₁| ≪ L²X = o(Tl³)`, so `κ(λ) = 1/λ + λ/3`, minimized on
`(0, 1]` at `λ = 1`: `κ(1) = 4/3`, proportion `2/3`
(`ArithmeticCastelnuovoSeveri.subthreshold_cert_le_two_thirds`).

### 1.2 The bandwidth four thirds

At `λ = 4/3` the core drops to `3/4 + 4/9 = 43/36 = 5/4 − 1/18` (`RHTower.diagonal_main_le`), the
prime–pole cross term stays `O(T^{5/6} log² T)` (`RHTower.abs_Mform_PX_PiX_params43_le`), and the
sum-frequency term is `O(XL) = O(T^{4/3} log T)`, negligible only if its oscillation over
`[T, 2T]` or the grid weighting is used. What remains is one inequality,

    primeSurplus(p_{4/3}, F_{4/3}) ≤ (1/18 + o(1)) (aL)² Tℓ₁/2π     (RHTower.PrimeSurplusFourThirds),

which gives `κ(4/3) ≤ 5/4` and `3/4` of the zeros simple and on the line
(`RHTower.zeta_three_quarters_of_prime_surplus`,
`ArithmeticCastelnuovoSeveri.zeta_three_quarters_from_prime_surplus`). On the spectral side the
same budget is the form-factor bound `∫_1^{4/3}(4/3 − α)F(α)dα ≤ 1/9`, twice the GUE value `1/18`
(§3.5).

### 1.3 Why close pairs, and why signed

Beyond `λ = 1` adjacent frequencies `log n, log m ∈ (log T, (4/3) log T]` can sit as close as
`X⁻¹ ≍ T^{−4/3} ≪ T⁻¹`. Inside the **coalescent band** `|log(n/m)| ≲ T⁻¹` the Hilbert denominator
`(log n − log m)⁻¹` no longer oscillates over `[T, 2T]`, and absolute-value Hilbert bounds lose the
factor `X/T = T^{λ−1}`. The trivial size of `𝒪₁` at `λ = 4/3` is `l²T^{4/3}`, the budget is of order
`Tl³`: the estimate must save `T^{1/3}` over the trivial bound and then land at an explicit
constant. A sieve bounds the close pairs only against nonnegative weights, while the height phase
`(m/n)^{iT}` changes sign. The input must be the sign of a prime-pair correlation.

---

## 2. What: objects and language

| Object | Definition | Lean |
|---|---|---|
| Difference-frequency kernel | `A⁻(y, y′) = ∬_{[T,2T]²} Φ(τ − τ′)² cos(τy − τ′y′)` | `Aminus` |
| Half-line moments of `Φ²` | `C^±(y)`, `S^±(y)`; for even `Φ`, `C⁻ = C⁺`, `S⁻ = −S⁺` | `Cp`, `Sp`, `Cm_eq_Cp_of_even`, `Sm_eq_neg_Sp_of_even` |
| Cosine part | `(C⁺(y) + C⁺(y′))(sin 2Tθ − sin Tθ)/θ`, `θ = y − y′` | `AminusCos` |
| Sine part | `(S⁺(y′) − S⁺(y))(cos 2Tθ + cos Tθ)/θ`, no close-pair pole | `AminusSin` |
| Off-diagonal sums | `Σ_{n≠m≤X} a_n a_m A⁻(log n, log m)` and its cosine, sine and Fourier-weighted forms | `ppOffDiag`, `ppOffDiagCos`, `ppOffDiagSin`, `ppOffDiagFourier` |
| Prime Dirichlet polynomials | `C_w(τ) = Σ_{n≤X} a_n w(log n) cos(τ log n)`, `S_w(τ)` likewise | `primeDirichletCos`, `primeDirichletSin` |
| End-effect form | `E(u, v) = L⁻² Σ_{k,l<d} G_{kl}(u)G_{kl}(v) − 𝓜[u, v]` | `endForm` |
| Jackson close-pair kernel | `(L/2π)∫ W(s + rh)W(s)e^{iθs}ds`, supported in `|θ| < 4b` | `jacksonPairKernel`, `jacksonCloseApprox` |
| Normalized Frobenius norm | `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ − α)F(α)dα` | `frobeniusFormFactor` |
| Trans-threshold integral | `I(λ) = ∫_1^λ(λ − α)F(α)dα` | `transThresholdIntegral` |
| Normalized prime surplus | `(9/8)I − 5/72 = (9/8)(I − 1/18) − 1/144` at `λ = 4/3`; `(2/λ²)I(λ) − (λ−1)²/λ² − (λ−1)³/(3λ²)` in general | `primeSurplusRatioOfIntegral`, `generalPrimeSurplusRatio` |
| Dyadic cosine kernel | `f_dyadic(u) = ∫_1^2 cos(tu)dt = (sin 2u − sin u)/u` | `dyadicCosineKernel` |
| Affine trans-threshold model | `F_{β,γ}(α) = α` on `[0, 1]`, `β + γ(α − 1)` on `(1, ∞)` | `affineTransModel` |
| Narrow-strip Cesàro energy | `E(δ) = (2/δ²)∫_1^{1+δ}(1 + δ − α)F(α)dα` | `narrowStripCesaroEnergy` |

**Words.**

* **Bandwidth** `λ = log X/log(T/2π)`; **sub-threshold** `λ ≤ 1`, **trans-threshold** `λ > 1`.
* **Coalescent band**: prime pairs with `|log(n/m)| ≲ T⁻¹`, where the window `[T, 2T]` cannot
  resolve the two frequencies.
* **Close pair** for a Jackson window of width `b`: `|log(n/m)| < 4b`. **Far pair**: the rest.
* **Core, surplus**: the part of the Frobenius norm evaluated unconditionally, and the remainder
  carrying the prime pairs.
* **Budget**: `1/18` of the normalization `(aL)²Tℓ₁/2π` at `λ = 4/3`, the room between the core
  `43/36` and the target `5/4`.

---

## 3. How: mechanisms

### 3.1 Parity splitting and the nonsingular sine part

The classical treatment expands `(y − y′)A⁻(y, y′)` into eight half-line moment terms and bounds
each by Montgomery–Vaughan; beyond `λ = 1` this loses the parity. For even `Φ` the parity relations
collapse the eight terms to two (`sub_mul_Aminus_eq_of_even`, `Aminus_eq_AminusCos_add_AminusSin`,
`ppOffDiag_eq_cos_add_sin`). Since `S⁺` is Lipschitz with constant `∫Φ(x)²|x|dx`
(`abs_Sp_sub_Sp_le`), the difference `S⁺(y′) − S⁺(y)` cancels the denominator, and
`|A⁻_sin(y, y′)| ≤ 2∫Φ(x)²|x|dx` for all `y, y′` (`abs_AminusSin_le`): the sine part has no close-pair
singularity.

### 3.2 Second-moment reduction and the exact mean-value identity

For the cosine part, `2C⁺(y) = ∫_{−T}^T Φ(x)² cos(xy)dx` while `∫_ℝ Φ(x)² cos(xy)dx = 2πg(y)`, and
Chebyshev's inequality on `|x| > T` gives `|C⁺(y) − πg(y)| ≤ (2T²)⁻¹∫Φ(x)²x²dx`
(`abs_Cp_sub_pi_mul_g_le`). Montgomery–Vaughan applied to this `O(T⁻²)` tail replaces `C⁺(log n)` by
`πg(log n)` across all off-diagonal pairs up to `X = (T/2π)^{4/3}`, with total error
`O(T^{−2/3} log T)` (`abs_ppOffDiagCos_sub_fourier_le`,
`exists_abs_ppOffDiagCos_sub_fourier_params43_le`). The remaining sinc kernel integrates back to
`∫_T^{2T} cos(τθ)dτ`, which gives the exact identity

    ppOffDiagFourier(g, T, X) = 2π ∫_T^{2T}(C_g(τ)C_1(τ) + S_g(τ)S_1(τ))dτ − 2πT Σ_{n≤X} a_n² g(log n)

(`ppOffDiagFourier_eq_primeDirichlet_integral`), and adding the prime diagonal cancels the last
term (`abs_ppDiag_add_ppOffDiagFourier_sub_integral_le`). The off-diagonal problem is a mixed mean
value of two prime Dirichlet polynomials of length `X > T` on `[T, 2T]`.

### 3.3 Bilinear splitting of the end effect

Bounding `E(ν_X, ν_X)` monolithically through the combined sup-norm `l + 4√X` costs
`O(Ll log l · X)`, which at `λ = 4/3` is `T^{4/3}` and swamps the budget. Splitting `E` along
`ν_X = μ + Π_X + P_X` into six bilinear terms (`endForm_trinomial`, `endForm_nuX_split`) and using
the `X`-free growth bound `|μ(τ)| ≤ C₀l + log⁺(|τ|/4T)` (`mu_nuBound`) gives
`|E(μ, μ)| ≤ C L l³ log l` at every `λ ≤ 2` (`exists_abs_endForm_mu_mu_le`), `O(l⁴ log l)` at `4/3`
(`exists_abs_endForm_mu_mu_params43_le`). The archimedean end effect leaves the barrier; the prime
components remain.

### 3.4 Jackson weights localize the close pairs

With the sharp window `1_{[T,2T]}` the kernel `(sin 2Tθ − sin Tθ)/θ` leaks `O(1/|θ|)` from the
endpoints, so far pairs still count. Weighting the grid by a Jackson window `W` with Fourier
transform supported in `(−2b, 2b)` makes `W(s + rh)W(s)` band-limited to `(−4b, 4b)`
(`RHTower.integral_jacksonProduct_mul_cexp_eq_zero`). The close-pair kernel then vanishes identically for
`|θ| ≥ 4b` (`jacksonPairKernel_eq_zero_of_le_abs`), and the continuous kernel sum over all pairs is
the sum over close pairs (`sum_jacksonCloseApprox_eq_close`). On the band `[2b, L/2 − 2b]` the
difference and sum frequencies stay `4b` away from every grid alias (`alias_sep_diff_of_mem_Icc`,
`alias_sep_sum_of_mem_Icc`). The whole Jackson-weighted prime–prime Frobenius sum differs from the
close-pair kernel sum by the outer Jackson mass times `Σ_{|r|<d}(Σ_n|c_n|‖A_n(r)‖)²`
(`abs_weighted_frobenius_pp_sub_closeKernel_le`): far pairs and sum frequencies are paid by the
window, and only close pairs remain.

### 3.5 The form-factor bridge

For any form factor with `F(α) = α` on `[0, 1]`, the normalized Frobenius norm is the sub-threshold
baseline `2/λ − 2/(3λ²)` plus `(2/λ²)I(λ)` (`frobeniusFormFactor_eq_split`). At `λ = 4/3` the
baseline is `9/8`, and `κ(4/3) ≤ 5/4` iff `I ≤ 1/9` (`frobeniusFormFactor_four_thirds_le_five_fourths_iff`).
The prime diagonal up to `(T/2π)^{4/3}` already carries `(λ − 1)/λ² = 3/16` of the trans-threshold
mass (`43/36 = 9/8 + 5/72`), so the normalized prime surplus is `(9/8)(I − 1/18) − 1/144`, and the
prime-side budget `1/18` is exactly `I ≤ 1/9` (`primeSurplusRatio_bridge`). The GUE prediction
`I = 1/18` gives surplus `−1/144`: the budget has slack `1/16` against the conjectured truth.

### 3.6 Height averaging localizes to the coalescent band

The rank–trace seam is linear in `tr G̃²` once the inertia parameter is fixed, and it holds for
every grid weighting `|w_k| ≤ 1` (`RHTower.seamA_weighted`), so it may be averaged over the window
height `T` against a weight `ω` before the prime side is evaluated. At fixed `L` — fixed profile
and fixed prime cutoff — the averaged pair kernels decay in the frequency `θ = log n ∓ log m`: `k`
integrations by parts give `|∫ω(T) sin(κT + c)dT| ≤ ‖ω^{(k)}‖₁/|κ|^k`, and the averaged kernel is at
most `2‖ω^{(k)}‖₁(∫Φ²)/|θ|^{k+1}` plus an offset tail (`abs_avg_Agen_le`). For `ω` of width `εT` the
far pairs `|log(n/m)| > T^{−1+η}` and all sum frequencies then cost `o((aL)²Tℓ₁)` once
`η(k + 1) > λ` and `λ < 2` (`abs_avg_ppOffDiag_sub_close_le`, `abs_avg_ppSumFreq_le`), where the
sharp window charges each of them `O(X log X)`. After height averaging only the coalescent band
carries trans-threshold mass. The restriction is real: at fixed bandwidth the cutoff
`X = (T/2π)^λ` moves with `T`, and averaging across a moving cutoff costs `≍ √ε X log²X`.

### 3.7 Fejér and Lorentz mean squares of the prime polynomial

Against a Fejér profile the mean square of the prime polynomial is an exact positive pair sum,
because the profile's Fourier transform is a triangle:
`∫F_b(τ − c)P_X(τ)²dτ = π⁻¹Σ_{n,m}a_na_m(Λ_b(y_n − y_m)cos((y_n − y_m)c) + Λ_b(y_n + y_m)cos((y_n + y_m)c))`
(`integral_fejer_mul_PX_sq`). For `b ≤ 1` the sum frequencies drop out and only pairs
`|log(n/m)| < b` remain, which a Chebyshev count bounds (`integral_fejer_mul_PX_sq_le`). Two Fejér
profiles half a period apart dominate a Lorentzian of width `R = 1/b`
(`lorentz_le_fejer_add_fejer`), hence the Lorentz-weighted mean value
`∫P_X(τ)²/(1 + ((τ − c)/R)²)dτ ≤ π√e log X(3ψ(X) + RΣ_{n≤X}Λ(n)/n)`
(`integral_lorentz_mul_PX_sq_le`): the `(R + X)` shape of the Montgomery–Vaughan theorem on a window
of length `R`, with no Hilbert inequality. It is a size bound, adequate for error terms of length
`R`, not for the close pairs.

### 3.8 Smooth grid weights

Sampling a weight `0 ≤ W ≤ 1` on the grid `τ_k` changes the grid kernel by
`K_W − W(τ)K = Σ_k(W(τ_k) − W(τ))φ̂(τ − τ_k)φ̂(τ′ − τ_k)` exactly (`KfunW_sub_mul_Kfun_eq`). For a
Lipschitz weight every coefficient is at most `min(ℓ|τ_k − τ|, 1)`, and grid sums of Lorentz
profiles are controlled by one averaging lemma, `Σ_k(1 + c²(x − τ_k)²)⁻¹ ≤ 4π/(ch)`
(`sum_lor_grid_le`): the weighted kernel is the weight times the unweighted one, up to an error of
the size of the Lipschitz constant against a Lorentzian of width `T`. A smooth compactly supported
weight vanishes off the grid range, so there is no aliasing and no end form at fixed bandwidth. This
is the route that avoids both the Jackson tails (trap below) and the moving cutoff of §3.6.

### 3.9 Coalescent sieve anatomy and model calibration

In the coalescent band `0 < n − m = h ≤ c m / T`, the multiplicative phase `T log(1 + h/m)` and
symmetric weight `(m(m + h))^{−1/2}` linearize to `T h / m` and `m⁻¹` with explicit error
`((L_K c² + M_K c / 2)/T) Σ Λ(m)Λ(m + h)/m` (`coalescent_sum_linearization_bound`). Under the
Hardy–Littlewood prime-pair heuristic `C_HL(H) = H − ½ log H + O(1)`, the continuum Poisson linear
term `H` integrates to zero against the signed dyadic kernel `f_dyadic(u) = (sin 2u − sin u)/u` by
the Frullani identity `∫_ε^R (sin 2u − sin u)/u du = ∫_R^{2R} (sin u)/u du − ∫_ε^{2ε} (sin u)/u du`
(`integral_sin_div_two_mul`, `abs_integral_dyadic_frullani_le`). What enters the prime surplus is
solely the arithmetic repulsion: the singular-series logarithmic deficit `−½(y − l)` integrates
against `g(y) = L − y` on `[l, L]` to `−(L − l)³/12 < 0` (`hl_coalescent_deficit_integral`), so the
Hardy–Littlewood main term has strictly favourable negative sign before any error term is estimated.

Across the two-parameter affine family `F_{β,γ}(α) = β + γ(α − 1)` on `α > 1` (`affineTransModel`),
the general prime-surplus ratio is `((λ − 1)²/λ²)(β − 1) + ((λ − 1)³/(3λ²))(γ − 1)`
(`generalPrimeSurplusRatio_affineTransModel`). At `λ = 4/3`, calibrating five benchmark models
(`calibration_five_models_four_thirds`) shows:
1. **Hardy–Littlewood / Function-Field / GUE** (`β = 1, γ = 0`): surplus `−1/144 < 0`;
2. **Uncorrelated baseline** (`β = 1, γ = 1`): surplus `0`;
3. **Naive Poisson off-diagonal without repulsion** (`β = 2, γ = 1`): surplus `+1/16 > 1/18`,
   failing the `1/18` budget by `1/144`;
4. **Spectral sieve upper bound** (`β = Υ, γ = 0`): surplus `(9Υ − 10)/144`, meeting `1/18` iff
   `Υ ≤ 2` (the exact factor-two parity limit);
5. **Unsigned additive sieve** (`β = 1 + Υ, γ = 1`): surplus `Υ/16`, requiring `Υ ≤ 8/9 < 1`.

### 3.10 Narrow-strip close-pair energy and the `2`-adic parity collar

In a narrow trans-threshold strip `λ = 1 + δ` (`δ > 0`), the proportion gain over `2/3` is
`(2 − κ(1 + δ)) − 2/3 = δ(2 − (3 E(δ) − 4)δ)/(3(1 + δ)²)` (`narrowStrip_proportion_gain_eq`), where
`E(δ) = (2/δ²)∫_1^{1+δ}(1 + δ − α)F(α)dα` (`narrowStripCesaroEnergy`). Because the diagonal gain is
first-order (`2δ/3`) while the close-pair penalty is second-order (`E(δ)δ²`), `2 − κ(1 + δ) > 2/3`
holds iff `E(δ) < 2/(3δ) + 4/3` (`narrowStrip_beats_two_thirds_iff`), and any uniform bound
`E(δ) ≤ B` on `(0, 1/(3(B − 1))]` achieves `1/(3(3B − 2))` at `δ* = 1/(3(B − 1))`
(`constrainedStrip_optimal_exchange_rate`).

On the discrete prime side, `log n − log m ≥ (n − m)/n` (`log_sub_log_ge_sub_div`) forces all
off-diagonal Fejér close-pair terms to vanish identically for `X ≤ 1/b`
(`fejer_double_sum_eq_diag_of_le_inv_b`). Because all odd primes `p ≥ 3` lie in `2ℕ + 1`, any two
distinct odd integers `m < n` satisfy `n − m ≥ 2`; thus `log n − log m ≥ 2/n`, and all odd-odd
off-diagonal Fejér close-pair terms vanish identically across the doubled range `X ≤ 2/b`
(`odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b`), and `X ≤ 1/(2b)` for Jackson weights
(`jacksonPairKernel_odd_offDiag_eq_zero_of_le_inv_two_b`). Above `2/b`, any Selberg/Bombieri–Davenport
small-shift sieve bound controls the close-pair sum on `[1/b, (1 + δ)/b]` with a quadratic `O(δ²)`
bound (`sieved_closePrimePair_strip_bound`).

### 3.11 The smooth-window certificate

The rank–trace seam holds for every grid weighting `|w_k| ≤ 1` (`RHTower.seamA_weighted`). Take
`w_k = u((τ_k − T)/T)` for a smooth profile `u` with values in `[0, 1]`, vanishing off `[ε₁, 1 − ε₁]`
and equal to `1` on `[2ε₁, 1 − 2ε₁]` (`WindowProfile`, `exists_windowProfile`). Then:

* **Trace.** The weighted trace loses only its collar: `tr Ĝ_w ≥ N − 4ε₁Tl − O(T) − O(T^{11/12}l⁶)`
  (`trace_ge_at`). The prime part of the collar is a cosine polynomial with Lipschitz coefficients;
  summation by parts against `2 sin(θ/2) Σ_{j<K} cos(φ + jθ) = sin(φ + (K − ½)θ) − sin(φ − θ/2)` and
  Jordan's inequality make it `O(T)` (`abs_weighted_P_part_le_lipschitz`).
* **Frobenius norm.** The weighted Frobenius sum is `L²` times the smooth form
  `∬ Ω(τ) Φ(τ − τ')² ν_X(τ) ν_X(τ')`, `Ω = u_T⁴`, up to a Lipschitz sampling error and the lattice
  deficit inside the window (`abs_weightedFrobenius_sub_smoothForm_le`). Since `Φ² ⋆ P_X = −2C_g` is
  again a prime polynomial, the form splits into nine channels along `μ + Π_X + P_X`
  (`smoothPair_nuX_le`): the archimedean and prime diagonals (the unconditional core `43/36`), the
  exact coalescent kernel `π⁻¹ a_n a_m g(log m) Ω̂(log n − log m)` on `0 < |log(n/m)| ≤ T^{−1+η}`
  (`coalSum`), far pairs and sum frequencies paid by `|Ω̂(θ)| ≤ ‖Ω^{(k)}‖₁/|θ|^k`, archimedean–prime
  channels by the half-period shift, and the prime–pole channels by Cauchy–Schwarz against the
  Lorentz mean squares of `P_X` and `C_g` (`frob_le_at`).

Assembled through the seam (`zeta_coalescent_certificate_four_thirds`, `zeta_coalescent_certificate`):

    N₀*(T, 2T) ≥ (29/36 − ε) N(T, 2T) − coalescentSurplus u η T     for all large T.

Since `29/36 − 3/4 = 1/18`, three quarters of the zeros on the line follow from
`coalescentSurplus u η T ≤ (1/18 + o(1)) N(T, 2T)` for one profile and one `η > 0`: a statement about
prime pairs at multiplicative distance at most `T^{−1+η}` only.

### 3.12 What the certificate gives at each budget

Arithmetic Castelnuovo–Severi reads the certificate as a scale of results in the normalised
coalescent surplus `β` (`CoalescentSurplusAndTransThresholdProportionLaws`). Any bound
`coalescentSurplus ≤ (β + ε)N(T, 2T)` gives `N₀* ≥ (29/36 − β − ε)N` dyadically and cumulatively
(`zeta_N0star_and_offLineMoment_of_coalescentSurplus`); `β < 5/36` beats `2/3`, `β ≤ 577/4500` beats
`HD(1)`, `β ≤ 1/18` gives `3/4` and the off-line moment `57/1000`, and the Hardy–Littlewood value
`β = −1/144` would give `13/16`
(`coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters`). In the affine models the
budget separates the two targets: the unsigned additive sieve at its factor-two parity limit has
surplus `1/8` and certifies `49/72 > HD(1)`, but reaches `3/4` only for `Υ ≤ 8/9 < 1`; the spectral
sieve reaches `3/4` exactly at `Υ = 2` (`five_model_separation_of_HD_one_and_three_quarters`). The
two-window mixture of bandwidths `1` and `4/3` has the exact optimal envelope
`2/3 + (181 − 18B)²/(1728(91 + 9B))` under `F ≤ B`, and reaches `3/4` at weight `4/9` iff
`B ≤ 2954/1035` (`mixOpt_values_and_three_quarters_criterion`). No bound on `β` is proved.

---

## 4. Foundational pillar theorems

All unconditional.

1. **The sine part has no close-pair pole.** `|A⁻_sin(Φ, T, y, y′)| ≤ 2∫Φ(x)²|x|dx` for all
   `y, y′` (`abs_AminusSin_le`), after the exact parity split (`ppOffDiag_eq_cos_add_sin`).
2. **The cosine part is a mixed Dirichlet mean value.** Up to `O(T^{−2/3} log T)` at `λ = 4/3`
   (`exists_abs_ppOffDiagCos_sub_fourier_params43_le`) it is the `[T, 2T]` mean value of
   `C_gC_1 + S_gS_1`, with the diagonal cancelled exactly
   (`ppOffDiagFourier_eq_primeDirichlet_integral`, `abs_ppDiag_add_ppOffDiagFourier_sub_integral_le`).
3. **The archimedean end effect is `X`-free.** `|E(μ, μ)| ≤ C L l³ log l` at every `λ ≤ 2`
   (`exists_abs_endForm_mu_mu_le`).
4. **Jackson weights reduce the prime–prime Frobenius sum to close pairs**, with a factored
   outer-mass error (`abs_weighted_frobenius_pp_sub_closeKernel_le`).
5. **The prime budget is the form-factor bound.** `κ(4/3) ≤ 5/4 ⟺ I ≤ 1/9`, and the prime surplus
   is `(9/8)(I − 1/18) − 1/144` (`frobeniusFormFactor_four_thirds_le_five_fourths_iff`,
   `primeSurplusRatio_bridge`).
6. **Two barriers.** The shifted Fejér majorant misses `1/9` by the factor `8/3`
   (`fejer_shifted_bound_gap`), and trace certificates of order `k ≥ 3` are confined to `kλ ≤ 1`
   (`higherMoment_rudnick_sarnak_cap`).
7. **Height averaging leaves only the coalescent band.** At fixed `L`, averaging over `T` with a
   weight of width `εT` makes the far pairs `|log(n/m)| > T^{−1+η}` and the sum frequencies
   negligible against the budget (`abs_avg_ppOffDiag_sub_close_le`, `abs_avg_ppSumFreq_le`).
8. **Lorentz mean value without Hilbert.** The prime polynomial obeys the `(R + X)` mean value on
   Lorentz windows of width `R`, from an exact positive Fejér pair sum
   (`integral_lorentz_mul_PX_sq_le`).
9. **Coalescent Frullani cancellation and five-model calibration.** The continuum Poisson linear
   density cancels against the dyadic cosine kernel (`abs_integral_dyadic_frullani_le`), leaving the
   strictly negative Hardy–Littlewood logarithmic deficit `−(L − l)³/12 < 0`
   (`hl_coalescent_deficit_integral`); calibrating five models at `λ = 4/3` proves the budget requires
   arithmetic repulsion (`calibration_five_models_four_thirds`).
10. **Narrow-strip exchange rate and `2`-adic parity collar doubling.** `2 − κ(1 + δ) > 2/3` iff
    `E(δ) < 2/(3δ) + 4/3` (`narrowStrip_beats_two_thirds_iff`), and `2`-adic parity forces all
    odd-odd close-pair terms to vanish up to `X = 2/b` (`odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b`).
11. **The bandwidth-`4/3` certificate lives on the coalescent band.** For every `ε, η > 0` there is
    a smooth window with `N₀*(T, 2T) ≥ (29/36 − ε)N(T, 2T) − coalescentSurplus u η T` for all large
    `T` (`zeta_coalescent_certificate`); the surplus is the smooth-window pair sum over
    `0 < |log(n/m)| ≤ T^{−1+η}` normalised by `(aL)²`.

---

## 5. Traps and sharp boundaries

| Trap | What is true instead |
|---|---|
| Bounding `𝒪₁` by the triangle inequality on the eight half-line moments | Gives `O(L²X)`; for `λ > 1`, `L²X ≫ Tl³`. Discarding the sign of `sin 2Tθ − sin Tθ` and the Lipschitz cancellation in `S⁺(y′) − S⁺(y)` forfeits all trans-threshold cancellation. |
| Working with the sharp window `1_{[T,2T]}` | Pairs with `|θ| ≫ T⁻¹` still contribute `O(1/|θ|)` through the endpoints. A smooth weight, or Jackson grid weights, is needed to localize to `|θ| < 4b`. |
| Expecting Jackson windows to reach the coalescent band | `F_b²` has cubic tails, so the outer Jackson mass is `≍ L/(b³M²)` and the far-pair error `≍ XL³/(b³M²)`; against the budget this forces `b ≫ X^{1/3}/T` (`b ≫ T^{−5/9}` at `λ = 4/3`). The "close pairs" `|log(n/m)| < 4b` then still include `T⁻¹ ≪ |θ| ≪ T^{−5/9}`, where the pair kernel is `≍ L/|θ|`. Jackson localization stops short of `h ≪ m/T`. |
| Averaging over the height at fixed bandwidth | The cutoff `X(T)` moves with `T`, and the moving cutoff costs `≍ √ε X log²X`. Height averaging localizes at fixed `L` (§3.6), so it needs core estimates uniform in `λ`. |
| Bounding the prime–pole channel of the smooth form by sup norms | `|Π_X| ≤ 3√X/T` against `|C_g| ≤ L·3√X` gives `≍ L X = L T^{4/3}`, above the budget. Cauchy–Schwarz against the Lorentz mean square of `C_g` gives `O(X L^{3/2}/√T) = O(T^{5/6}L^{3/2})` (`smoothPair_nuX_le`). |
| Using the Lorentz mean value on the close pairs | It is a size bound of Montgomery–Vaughan shape; on a window of length `R ≍ T` it sees `|log(n/m)| ≲ 1/R` only through their number. The close-pair problem is a signed one. |
| Positive spectral majorants | Montgomery's shift method uses only `F ≥ 0` and `F(α) = |α|` on `[−1, 1]`; the shifted Fejér kernel then gives `8/27`, a factor `8/3` above `1/9` (`fejer_shifted_bound_gap`). Arithmetic input on `[1, 4/3]` is required. |
| Higher moments to bypass pair correlation | `tr(G̃^k)` in its unconditional range forces `kλ ≤ 1`, so `λ ≤ 1/3` for `k ≥ 3` (`higherMoment_rudnick_sarnak_cap`): higher moments shrink the bandwidth. |
| Reading `PrimeSurplusFourThirds` as established | It is the premise of `RHTower.zeta_three_quarters_of_prime_surplus`. The unconditional content is the reduction of §3, not the bound. |
| Treating the budget as a power saving | A saving of `T^{1/3}` over the trivial bound only reaches the right order. The bound must land below `1/18` of an explicit normalization, against a conjectured value `−1/144`. |
| Expecting a sieve to bound close pairs | Upper-bound sieves need weights `w ≥ 0`; the height phase changes sign, so the sieve reverts to the size bound, a factor two off at best (the parity barrier). |
| Confusing the Poisson continuum with the HL main term | A naive Poisson off-diagonal model without arithmetic repulsion (`β = 2, γ = 1`) has surplus `+1/16 > 1/18` (`calibration_five_models_four_thirds`). The Frullani identity kills the continuum linear term against the signed dyadic kernel, and the budget uses the `−½ log H` singular-series deficit. |
| Treating the close-pair threshold `X = 1/b` as prime-blind | While `1/n ≥ b` stops at `X = 1/b` on all integers, odd integers have `n − m ≥ 2`, so all odd-odd close-pair terms vanish up to `X = 2/b` (`odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b`). |
| Treating pair correlation beyond `α = 1` as a separate input | Under RH it is equivalent to prime-pair correlations with a power-saving error; unconditionally it needs additive-divisor inputs for `Λ` of twin-prime strength. |
| Breaking the coalescence blind spot by zero-side slack below `3/4` | Unconditionally `zeroSideSlack(λ, T) ≤ (λ − H(λ) + ε)N(T, 2T)`, which refutes the slack needed for `3/4` at every `λ ∈ (0, 3/4)` (`ArithmeticCastelnuovoSeveri.not_three_quarters_zeroSideSlack_of_lt_three_quarters`). |
| Mollifiers as an alternative to `λ > 1` | For mollified discrete moments of CGG type the optimum is `1 − (1 + θ)^{−3}`, so `3/4` needs `θ ≥ 4^{1/3} − 1` (`RHTower.CGGMollifier.three_quarters_le_iff`); at `θ = 4/7` it is `988/1331 < 3/4` (`RHTower.CGGMollifier.ratio_bound_four_sevenths`). |

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **Why does the rank–trace method stop at `2/3`?** Because Montgomery–Vaughan decouples prime
   pairs exactly up to `X = T`, and `κ(λ) = 1/λ + λ/3` is smallest at `λ = 1` on that range.
2. **What exactly separates `2/3` from `3/4`?** One prime-surplus inequality with budget `1/18` at
   `λ = 4/3`, equivalently `I ≤ 1/9`.
3. **Which parts of the surplus are harmless?** The sine part, the cosine tail beyond `T`, the
   archimedean end effect, the far pairs and the sum frequencies. What remains is the mixed
   Dirichlet mean value, or the close-pair kernel.
4. **What does a positive majorant achieve?** `8/27`, a fixed factor `8/3` short.
5. **What part of the Hardy–Littlewood main term enters the surplus, and what is its sign?** The
   continuum Poisson linear term cancels identically against the signed dyadic kernel by Frullani's
   identity (`abs_integral_dyadic_frullani_le`); only the singular-series logarithmic deficit
   `−½ log H` survives, contributing `−(λ − 1)³/(3λ²) = −1/144 < 0` at `λ = 4/3` with strictly
   favourable negative sign before any error term is estimated (`hl_coalescent_deficit_integral`).
6. **Which features of the primes does the `1/18` budget actually use?** Calibration across five
   models (`calibration_five_models_four_thirds`) shows that a naive Poisson off-diagonal model
   without repulsion gives `+1/16 > 1/18` (failing by `1/144`), an unsigned additive sieve bound
   `F(α) − α ≤ Υ` requires `Υ ≤ 8/9 < 1`, and a spectral bound `F(α) ≤ Υ` meets `1/18` iff `Υ ≤ 2`.
7. **How does the exchange rate behave in a narrow strip `λ = 1 + δ`?** The proportion gain is
   `δ(2 − (3 E(δ) − 4)δ)/(3(1 + δ)²)`, which beats `2/3` iff `E(δ) < 2/(3δ) + 4/3`
   (`narrowStrip_beats_two_thirds_iff`), while `2`-adic parity doubles the close-pair vanishing
   threshold on odd integers from `1/b` to `2/b` (`odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b`).

### 6.2 Tools

Built and reusable:

- *Parity splitting* of the difference-frequency kernel and the Lipschitz cancellation of its sine
  part.
- *Second-moment tail reduction* of the cosine part and the exact Dirichlet mean-value identity.
- *Bilinear end-effect splitting* along `μ + Π_X + P_X`.
- *Jackson grid weights*: band-limited products, exact close-pair support and alias separation.
- *Height averaging*: oscillatory decay of averaged pair kernels at fixed `L`.
- *Fejér and Lorentz mean squares*: exact positive pair sums, the `(R + X)` mean value on Lorentz
  windows.
- *Smooth grid weights*: the exact weighted-kernel difference and the Lorentz grid-sum lemma.
- *Form-factor calculus*: the split of `κ`, the bridge to the prime surplus, the Fejér and
  Rudnick–Sarnak barriers.
- *Coalescent linearization and Frullani calculus*: multiplicative-to-additive linearization in
  `0 < h ≤ cm/T`, exact Frullani cancellation of the dyadic cosine kernel, and the five-model
  calibration bridge.
- *Narrow-strip Cesàro energy and `2`-adic parity collar*: exact first-order vs. second-order
  narrow-strip criterion, `2`-adic parity collar doubling up to `2/b`, and small-shift sieve strip
  bounds.
- *Smooth-window certificate*: the convolution `Φ² ⋆ v` for slowly varying, decaying and prime
  densities; the exact coalescent kernel; the nine-channel evaluation; the grid comparison with the
  lattice deficit; the collar form of the weighted trace; the seam assembly at `λ = 4/3`.

To be built:

- a signed bound on the mixed mean value `∫_T^{2T}(C_gC_1 + S_gS_1)` at `X = T^{4/3}`;
- a bound `coalescentSurplus ≤ (β + o(1)) N(T, 2T)` for the coalescent band, at `β = 1/18` or any intermediate budget (open problem 1);
- an unconditional asymptotic transfer from the finite height-averaged prime-pair sum at `[T, 2T]` to
  the spectral form factor `F(α)` in `λ = 1 + δ`.

---

## 7. Open problems

1. **The coalescent surplus at bandwidth `4/3`.** By the smooth-window certificate (§3.11),
   `RHTower.PrimeSurplusFourThirds` is equivalent, up to `o(1)`, to
   `coalescentSurplus u η T ≤ (1/18 + o(1))N(T, 2T)` for one profile and one `η > 0`: a bound on the
   smooth-window pair sum over `0 < |log(n/m)| ≤ T^{−1+η}` alone. After the linearization of §3.9
   this is a sign-sensitive estimate for `Σ_{m,h} Λ(m)Λ(m + h) m⁻¹ K(Th/m)` on `T < m ≤ T^{4/3}`,
   `0 < h ≪ m/T`. Every intermediate budget is a result (§3.12): `β < 5/36` beats `2/3`,
   `β ≤ 577/4500` beats `HD(1)`.
2. **What a size-only sieve can reach.** In the unsigned additive model the factor-two parity
   limit gives `β = 1/8` and the proportion `49/72 > HD(1)`, while `3/4` needs `Υ ≤ 8/9 < 1`, below
   parity (§3.12). Open: whether an upper-bound sieve applied to the actual coalescent band, which
   sees the kernel only through its size, obeys the model's bound; and, for `3/4`, which signed
   correlation of prime pairs at distance `≲ m/T` breaks the parity barrier.
3. **The signed mixed mean value.** The identity of §3.2 is exact. Find the arithmetic structure of
   `C_g` and `C_1` (both prime Dirichlet polynomials of length `T^{4/3}`, one Fourier-weighted) that
   makes their correlation over `[T, 2T]` smaller than the product of their sizes, at the constant
   `(4/9 + 1/18)(aL)²Tℓ₁/2π`.
4. **From the finite prime-pair sum to the form factor.** The calibration of §3.9 and the
   narrow-strip criterion of §3.10 are statements about `F(α)`. An unconditional asymptotic transfer
   from the finite height-averaged prime-pair sum at `[T, 2T]` to `F(α)` on `(1, 1 + δ]` is not
   available; without it no bound on `F` is a bound on the certificate.
5. **The exchange rate just above `λ = 1`.** Transfer the finite-`T` narrow-strip close-pair bound
   through the smooth-weighted grid assembly without losing the `O(δ)` diagonal gain to the
   finite-height window tails.

---

## 8. Working in the theory

- State the bandwidth, the window (sharp, smooth or Jackson) and the normalization of every
  estimate; a bound on `𝒪₁` without its normalization says nothing about the proportion.
- Keep the sign of the oscillating kernels until a cancellation has been used. The parity split
  and the Lipschitz cancellation are lost by the first triangle inequality.
- Separate the reduction from the estimate. Every module here reduces the surplus; none bounds the
  close-pair kernel, and none should be described as doing so.
- Report the unit: the bandwidth reached and the proportion certified, or the share of the `1/18`
  budget paid.
- Search the corpus first (`scripts/formal_tools.py research "<query>"`): the Gram, trace and
  Jackson infrastructure lives in `RHTower` (`ZetaTraceWide`, `ZetaFrobeniusSurplusSplit`,
  `ZetaThreeQuartersOfPrimeSurplus`, `ZetaWeightedFrobeniusClose`, `ZetaWeightedFrobeniusFar`).

---

## Source entry points

| Module | Content |
|---|---|
| `PrimeSurplusAnatomyAndDirichletMeanValue` | parity split of `A⁻`, nonsingular sine part, second-moment reduction, exact mean-value identity and diagonal cancellation |
| `ArchimedeanEndEffectAndSurplusSplitting` | trinomial splitting of the end-effect form; `X`-free archimedean end-effect bound |
| `JacksonWeightedPrimeFrobeniusDecomposition` | compact support of the Jackson pair kernel, alias separation, global close-pair reduction |
| `FormFactorThresholdAndShiftInequality` | form-factor split of `κ`, the `1/9` equivalence, the prime-surplus bridge, the Fejér gap, the Rudnick–Sarnak cap |
| `HeightAveragedCoalescentLocalization` | oscillatory decay of height-averaged pair kernels; far pairs and sum frequencies negligible at fixed `L` |
| `FejerWeightedPrimeMeanSquare` | Fejér mean square as an exact pair sum; Lorentz-weighted `(R + X)` mean value |
| `SmoothGridWeightKernel` | grid kernel of a smooth height weight; Lipschitz comparison; Lorentz grid sums |
| `CoalescentSieveAnatomyAndModelCalibration` | coalescent multiplicative-to-additive linearization; Frullani cancellation of the dyadic cosine kernel; HL logarithmic deficit negativity; general-`λ` prime-surplus bridge and five-model calibration |
| `SmoothWindowContinuousForm` | `Φ² ⋆ v` for slowly varying, decaying and prime densities; Fubini under linear growth; exact coalescent kernel and its diagonal/close/far/sum-frequency split; half-period shift; Lorentz mean square of `C_w` |
| `SmoothWindowFrobeniusChannels` | bilinear expansion along `μ + Π_X + P_X`; the nine channels (`smoothPair_nuX_le`) |
| `SmoothWindowGridComparison` | weighted Frobenius sum as `L²` times the smooth form; Lorentz mean square of `ν_X`; lattice deficit at distance `D` |
| `SmoothWindowWeightedTrace` | summation by parts; Jordan bound on the alias interval; prime part of the trace at `λ = 4/3`; collar form of the trace |
| `SmoothWindowProfile` | window profiles, existence, scaled weights, derivative and collar bounds |
| `SmoothWindowFrobeniusBound` | the smooth-window Frobenius bound at one height |
| `SmoothWeightedCertificateAtFourThirds` | rates, one-height trace and Frobenius bounds, the seam assembly; `zeta_coalescent_certificate` |
| `NarrowStripClosePairEnergyAndExchangeRate` | narrow-strip Cesàro energy and `2/3` escape criterion; exact sub-threshold close-pair vanishing; `2`-adic parity collar doubling (`X ≤ 2/b`); quadratic `O(δ²)` small-shift sieve strip bound |
