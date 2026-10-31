# SignedSuccessorArithmetic (SSA)

Namespace `GaloisForLFunctions.SignedSuccessorArithmetic`; umbrella `SignedSuccessorArithmetic.lean`; 21 modules.
Everything unconditional except the explicitly conditional receiver criteria (§5, marked).

## 1. Motivation

The successor `n ↦ n+1` is the structure of `ℤ` that Beurling systems lack. SSA asks how `+1`, interacting
with `×`, forces signed cancellation in multiplicative data: at what strength, at one scale, with positivity
coming from an integer count. It has two halves. (a) **Successor calculus** of completely multiplicative
signs: exact identities, floors, quantized biases and deficits. (b) **Dirichlet forms of Möbius weights**
(from BezoutValuationIncidence): which truncation of `Σ μ(d₁)μ(d₂)(d₁d₂)^{−σ}Φ_r(d₁/d₂)` carries zero
information, and the complete unconditional phase diagram of the one that does not.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| CM sign | `CMSign`, `CMSign.ofPrimes`, `CMSign.liouville` | `f : ℕ → ℤˣ` completely multiplicative; group, free on prime values |
| Successor sign, cocycle | `succSign`, `IsDilationCocycleAt`, `IsDilationCocycle`, `signOfSucc` | `σ_f(n) = f(n)f(n+1)`; `Π_{j<m}σ(mn+j) = σ(n)`; reconstruction `Π_{k<n}σ(k)` |
| Agreement data | `agree`, `agreeCount`, `doubleAgreeCount`, `succCorr`, `logAgree`, `logSuccCorr` | `a(n) = [f(n)=f(n+1)]`, `A(N)`, `E_N = #{a(n)=a(2n)=1}`, `C(N) = 2A − N`, log masses |
| Deficit | `twoScaleDeficit`, `ZeroDefect` | `D_N = C(2N+1) − σ(1) + C(N) + N`; `E_N ≡ 0` |
| Lag `h` | `shiftSign`, `agreeAt`, `logAgreeAt`, `ZeroDefectAt` | `f(n)f(n+h)` |
| Unimodular | `CMUnit`, `unitSuccPhase`, `logUnitCorr`, `CMSign.toCMUnit` | `|f| = 1`, phase `f̄(n)f(n+1)` |
| Twins | `chi3Twin`, `chi4Twin`, `legTwin`, `twoTwin`, `altSign` | character off one prime, free value there; `(−1)^{v₂}`; `(−1)^n` control |
| Finite-field sums | `charSuccCorr`, `kloosterman` | `Σχ(x)ψ(x+1)`; `Σ_{x≠0}ψ(ax + b/x)` |
| Euler factors | `eulerFactorSq`, `eulerProductSq`, `primeWindow` | `|1 − p^{−σ}e^{iτ log p}|²`, products, primes in `(x, λx]` |
| Spectral weight | `stepSpectralWeight`, `stepHalfLine`, `dyadicFreqShell` | `W_r = |𝓜(v_r|₊)|²` of the BVI Ramanujan step vector |
| Möbius polynomial | `twistedPow`, `moebiusPolySq` | `d^{−σ}e^{iθ log d}`; `|Σ_{d≤D}μ(d)d^{−σ}e^{iθ log d}|²` |
| Size-truncated form | `sizeHypercubeForm`, `sizeTwinHypercubeForm` | `R_ε(D) = Σ_{d₁,d₂≤D}μμ(d₁d₂)^{−½−ε}Φ_r(d₁/d₂)`; all signs `+1` |
| Forward dilation | `forwardDilatedPrimitive`, `forwardDilatedVector`, `forwardDilatedLimit`, `weightedForwardVector`, `weightedBackwardVector`, `weightedForwardDilatedLimit` | `G_{ε,D}(x) = Σ_{d≤D}μ(d)d^{−1−ε}C_r(⌊dx⌋)`, `D_d v_r` combinations |
| Folded profile | `foldedZeroDampingProfile`, `naturalDilationLimit` | `ε = 0, r = 2` profile; cutoff-independent head profile |
| Prime shells | `shellCut`, `primeShell`, `shellTrig`, `fejerCosKernel`, `desingLogProd` | `⌊e^{e^j}⌋` shells; shell cosine sums; Fejér kernel; desingularized log Euler product |
| Constants | `sqrtEulerConst`, `twinHalfSlope`, `roughPrimeProd` | `c₀ ∈ [1,3]`; `I_r = c₀√rΠ_{p|r}(1 − p^{−½}) > 0`; `Π_{r<p≤X}p` |

`C_r(n)` = real part of RHTower `pmRamanujanPrimitive r n`; `Φ_r` = `pmRamanujanDilationProfile`; `Q_ε` = BVI
`hypercubeDilationDirichletForm` (divisors of squarefree `P`).

## 3. Language

- **Floor**: universal lower bound on logarithmic agreement density over all CM signs; **sharp** when a twin attains it.
- **Junction**: steps adjacent to a multiple of the conductor, where the twin's free value enters.
- **Bias**: mean successor sign (`−1/p` for prime-conductor twins).
- **Quantization**: a signed quantity equal to a nonnegative integer multiple of a fixed quantum.
- **Prime-support vs size truncation**: `d | P` versus `d ≤ D`. Only size truncation is a receiver.
- **Damping** `ε`, `σ = ½ + ε`; half damping `ε = ½` is the line `Re s = 1`.
- **Pole-driven**: forced by PNT/the pole of `ζ` at 1, independent of zeros.

## 4. Mechanisms

**Successor calculus**
1. Telescoping over the dilated block `mn, …, mn+m` gives the cocycle; `f(m)² = 1` removes prime values. The
   cocycle at all primes characterizes CM successor signs; `signOfSucc` reconstructs `f`.
2. Cocycle at `m = 2` ⇔ per-step count `a(2n) + a(2n+1) + a(n) = 1 + 2a(n)a(2n)`. Summing over the pairs
   `{2n, 2n+1}` gives the exact two-scale identity; weighting by `1/n` gives the one-third log floor.
3. Lag `h`: same count along progressions. Odd `h`: positions `2n`, `2n+h` are disjoint ⇒ floor `1/3`. `h = 2`:
   positions overlap; replaced by "three signs contain an agreeing pair" + `a₂(2m) = a(m)` ⇒ floor `1/4`.
4. Twins are extremal: periodic structure gives exact counts (`A(3J+1) = J`, `A(4J) = 2J`), zero doubling
   defect, and exact correlations `C(pJ) = −J + (1+χ(−1))εM(J)` with self-similar `M(pJ) = εM(J)`.
5. Unimodular case: `(Re u + Re v)² ≤ 2(1 + Re uv)` + Cauchy–Schwarz ⇒ floor `−½`.
6. Zero defect forces values at small primes by chasing `σ(n) = 1 ⇒ σ(2n) = −1` through factorizations.

**Finite fields**
7. `S(χ,ψ) = χ(−1)J(χ,ψ)`; orthogonality gives `S(χ,χ⁻¹) = −1`, `|S|² = q`, `Σ_a|K(a,b)|² = q(q−1)`.

**Hypercube forms**
8. Mellin unitary turns dilation into modulation: `Φ_r(c) = ∫W_r(ξ)cos(2πξ log c)`, `W_r ≥ 0`, `∫W_r = Φ_r(1) > 0`.
   Divisor expansion: `Σ_{d₁,d₂|P}μμ(d₁d₂)^{−σ}cos(θ log(d₁/d₂)) = Π_{p|P}|1 − p^{−σ}e^{iθ log p}|²` ⇒
   `Q_ε(P) = ∫W_r·eulerProductSq(½+ε, 2πξ)`. Size truncation instead gives `∫W_r|Σ_{d≤D}μ d^{−σ}e^{…}|²`.
9. Below `σ = 1`: PNT fills a prime window `(x, λx]`; at heights `τ ≈ (2πj+π)/log x` all phases sit near `π`, so
   the window product is `≫ x^{1−σ}/log x` on a ball of radius `≍ 1/log x` — divergence against any weight with
   mass (Lebesgue differentiation removes regularity).
10. At `σ = 1` (all Möbius-signed forms bounded): Mertens rate `M(n) ≪ n/log⁴n` + Abel summation on floor shells
    (size form); `log` Euler product controlled by `log ζ` at `1 + 1/log z`, pole sandwich `−log|u| + O(1)`,
    two-squares cosine majorant `(17/24 − cos θ + ⅓cos 2θ ≥ 0, ≥ −2cos θ)`, double-exponential prime shells with
    Fejér-kernel `L²` decay `e^{−j}`, superlevel decay `e^{−6n/5}` ⇒ uniform exponential integrability; `W_r` decay
    `(1+|ξ|)^{−4/3}` from the convexity bound `ζ(½+it) ≪ t^{1/3}` (prime-divisor form).
11. `+1` twins at `σ = 1`: test vector `δ(n) = 1/√n − 1/√(n+1)` cancels the main term by `Σ_{b|r}μ(b) = 0`, leaving
    `I_r·H_X`; Cauchy–Schwarz ⇒ `≥ c log X`.
12. Forward–backward normality (`Φ_r` symmetric) ⇒ `R_ε(D) = ∫_0^∞G_{ε,D}(x)²dx/x²` with summable weights; exterior
    `(1,∞)` bounded by `(B_r ζ(1+ε))²`; interior `= ∫_1^D G_{ε,D}(1/u)²du` carries the difficulty.
13. Sieve functional equation `Σ_m m^{−1−ε}G_ε(mx) = C_r(⌊x⌋)` (fiberwise `Σ_{d|j}μ = [j=1]`); Fourier modes on
    `[0,r]` are triangular in the dilation index ⇒ harmonic uniqueness ⇒ Möbius uniqueness.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Cocycle characterization of CM successor signs | `exists_cmSign_iff_primeCocycle`, `dilation_cocycle` | unconditional |
| Exact two-scale identity; signed form | `two_scale_identity`, `signed_two_scale_identity` | unconditional |
| One-third log floor, sharp (χ₃ twins) | `one_third_log_floor`, `neg_third_log_floor`, `one_third_floor_sharp` | unconditional |
| Odd-shift floor `1/3`, attained by `T` for all odd `h` | `odd_shift_log_floor`, `odd_shift_floor_sharp` | unconditional |
| Lag-two floor exactly `1/4` | `lag_two_quarter_floor`, `lag_two_floor_sharp` | unconditional |
| Bias `−1/p` of Legendre twins; `C(pJ) = −J` for `p ≡ 3 (4)` | `succCorr_legTwin`, `succCorr_legTwin_of_three_mod_four`, `abs_succCorr_legTwin_add_div_le` | unconditional |
| Deficit quantization `D_N = 4E_N` | `twoScaleDeficit_eq`, `twoScaleDeficit_lt_four_iff`, `zeroDefect_iff` | unconditional |
| Zero defect ⇒ `f(2) = −1`; `T` zero-defect, not a χ₃ twin | `zeroDefect_two_eq_neg_one`, `zeroDefect_twoTwin`, `twoTwin_ne_chi3Twin`, `zeroDefect_branches` | unconditional |
| Complex floor `∈ [−½, −⅓]`; Catalan obstruction | `complex_floor_bracket`, `no_cubeRoot_successor_coloring` | unconditional |
| `|S(χ,ψ)|² = q`; Kloosterman second moment | `norm_sq_charSuccCorr`, `sum_normSq_kloosterman` | unconditional |
| Partial Euler products unbounded in the strip | `exists_aligned_window`, `spectralHypercube_unbounded_of_integrable` | unconditional |
| `Q_ε` unbounded for `−½ ≤ ε < ½` | `hypercubeDilationDirichletForm_unbounded` | unconditional |
| `R_{½}` bounded; `+1` twins diverge; sign split | `sizeHypercubeForm_half_bounded`, `tendsto_sizeTwinHypercubeForm_half_atTop`, `half_damping_sign_split` | unconditional |
| `Q_{½}` bounded over all squarefree `P`; subset ceiling `(log z)^{17/24}` | `hypercubeDilationDirichletForm_half_bounded`, `hypercubeDilationDirichletForm_half_subset_le_rpow_log`, `hypercube_roughPrimeProd_half_damping_sign_split` | unconditional |
| `W_r` bounds: `L^∞`, dyadic decay, `(1+|ξ|)^{−4/3}` | `stepSpectralWeight_ae_le`, `stepSpectralWeight_dyadic_shell_le`, `stepSpectralWeight_ae_le_inv_rpow` | unconditional |
| Head + tail decomposition; forward/backward normality | `sizeHypercubeForm_eq_head_add_tail`, `norm_sq_weightedForwardVector_eq_backward`, `sizeHypercubeForm_eq_integral_Ioi_forwardDilatedPrimitive` | unconditional |
| Sieve functional equation; Möbius uniqueness | `hasSum_forwardDilatedLimit_mul`, `eq_moebiusReal_of_sieve_functional_equation` | unconditional |
| Receiver: bounded `R_ε` ⇒ admission / zero-free strip / RH | `mem_receiverDampings_of_bounded_sizeHypercubeForm`, `re_le_of_bounded_sizeHypercubeForm_on_Ioo`, `riemannHypothesis_of_cofinal_bounded_spectral_moebiusPolySq` | **conditional criterion** |
| Subsequence suffices; forward `L²(1,D)`; `r = 2` Möbius windows ⇒ RH | `mem_receiverDampings_of_frequently_bounded_sizeHypercubeForm`, `riemannHypothesis_of_cofinal_frequently_bounded_forwardDilated_Ioo`, `riemannHypothesis_of_cofinal_bounded_alternating_moebius_Ioo` | **conditional criterion** |

## 6. Tools

**Developed**
- Successor algebra: telescoping `prod_succSign_range`, `prod_shiftSign_progression`, pair splits `sum_Icc_two_mul_add_one`, `sum_Icc_two_mul_add_two`.
- Twin constructions for any prime conductor (`legTwin`) with periodic value lemmas.
- Spectral transport: `dilationProfile_eq_integral`, `hypercube_cos_sum_eq_eulerProductSq`, `sizeHypercubeForm_eq_integral`.
- Prime-window/alignment kit: `eventually_theta_window_ge`, `cos_le_of_aligned`, `eulerProductSq_window_ge`.
- `σ = 1` Euler-product kit: `eulerProductSq_one_le_exp`, `exists_neg_sum_cos_div_primesLE_le`, `sum_cos_div_prime_le_of_zeta_upper`, `exists_subset_neg_two_cos_le_pole_free`, `two_squares_cos_majorant`, `exists_unit_L2_primeShell_le`, `exists_integral_exp_desingLogProd_unit_le`.
- `W_r` integrability: `integrable_stepSpectralWeight_mul_fourthRoot`, `_mul_log_pow`, `_mul_nearZero_rpow`.
- Forward-dilation kit: `integral_Ioi_one_forwardDilatedPrimitive_le`, `integral_Ioo_zero_one_forwardDilatedPrimitive_eq`, `forwardDilatedLimit_add_natCast`, `eq_zero_of_tsum_pmRamanujanPrimitive_floor_eq_zero`.

**To build**
- Uniform bound of `R_ε(D)` for some `0 < ε < ½` — equivalently of `∫_1^D G_{ε,D}(1/u)²du`.
- A single-scale power-saving signed successor estimate for `λ` or `μ` with explicit receiver transfer.
- `Σ_{a≠0}`-balanced Kloosterman bilinear forms matching the BVI cross-scale Gram.

## 7. Open questions

1. Lift the floor for `λ` above `1/3` using `λ(p) = −1` at infinitely many `p ≡ 1 (mod 3)` (twin `ε = −1` agrees with `λ` below 7).
2. Classify zero-defect signs (`f(2) = −1` forced; χ₃ twins and `T` known).
3. Even-shift floors for `h ≥ 4`; exact complex floor in `[−½, −⅓]`.
4. Successor calculus for `μ` (squarefree support breaks the cocycle).
5. Boundedness of `R_ε` below half damping (first rung = zero-free strip; cofinal = RH). Structure available: sieve
   functional equation, Möbius uniqueness, terminal dyadic window = Möbius harmonic tail, ε = 0 folded profile.
6. Pointwise (not mode-wise) meaning of the `ε = 0` folded sieve identity.

## 8. Traps

| Trap | Fact |
|---|---|
| Floor = Chowla-type cancellation | Density bound over all CM signs, attained by pretentious twins |
| Cocycle constrains prime values | They cancel; constraints identical for all CM signs |
| Every shift has floor `1/3` | Odd shifts only; lag two is exactly `1/4` |
| Bias `−1/p` = failed cancellation | Pretentious main term, quantized by the conductor |
| `𝔽_q` square-root counts transfer to `ℤ` | Periodic data acquire junctions and biases; law `|S|² = q` has no `ℤ` analogue |
| Prime-divisor form boundedness is quasi-RH | Unbounded below `½` unconditionally (pole); bounded at `½` unconditionally |
| `σ = 1` boundedness is strip progress | It uses only `Re s ≥ 1` information (Mertens, convexity, nonvanishing on the 1-line) |
| Prime-support and size truncation interchangeable | Only size truncation is the receiver |
| Summable forward weights remove the difficulty | Exterior is trivial; interior `∫_1^D G(1/u)²` carries it |
| Receiver criteria are results | `riemannHypothesis_of_*` take the boundedness as hypothesis |
| Folded `ε = 0` identity is pointwise | Proved per sine mode only |
| Lean: `(u : ℤˣ)^k` with `pow_add` | Use term-mode `pow_add ε _ _`; `open _root_.RHTower` inside the namespace |

## 9. Context

| Direction | Programmes (import counts) |
|---|---|
| Uses | RHTower 10 (Sieve: Mertens rates, harmonic/squarefree bounds, prime windows, ζ pole box, `MoebiusSmoothLogPower`; `ZetaConvexityBound`; `PMRamanujanBandMellin`; discrete packets), BezoutValuationIncidence 4, HTGeometry 3 (`HalfLineMellinMultiplier`, `FourierTailSup`, `NearZeroTruncatedPower`), PNTPlus 1 |
| Used by | ArithmeticCorrelationGeometry 1 (`TheSuccessorDilationCocycle`), MainTheorems |

| Neighbour | Interface |
|---|---|
| BezoutValuationIncidence | supplies `Φ_r`, `hypercubeDilationDirichletForm`, twin forms, `naturalDilationDirichletForm`, residue-gap budget, threshold `hypercubeDilationDirichletForm_threshold` (`ε > ½` bounded); SSA completes the `ε ≤ ½` phase diagram and identifies the receiver |
| RHTower receiver | `receiverDampings`, `riemannHypothesis_of_accPt_zero_receiverDampings`: target of all conditional criteria |
| TransHorizonIncidenceMechanics | `pronicNorm` = receiver head energy |
| ArithmeticCorrelationGeometry | reuses the dilation cocycle |

## 10. Big picture

SSA shows precisely what the successor buys and what it does not. On the sign side, `+1` against `×` yields exact,
quantized, sharp density laws — the one-third floor, conductor-quantized biases, a deficit that is four times a
count — all attained by pretentious twins. These are density-scale facts; the square-root scale that RH needs never
appears over `ℤ`, although its finite-field shadow is literally a count.

On the form side, the programme separates pole from zeros cleanly. Prime-supported Möbius forms diverge below the
1-line for a reason that has nothing to do with zeros, and are bounded on it; everything provable at `σ = 1` comes
from the 1-line alone. The one object that carries zero information is the size-truncated form, now characterized
completely — it is the receiver, its Möbius weights are the unique solution of a sieve functional equation, and its
difficulty is isolated in one interior integral. The RH content left here is a single uniform bound strictly inside
the strip; no successor identity proved so far reaches it.
