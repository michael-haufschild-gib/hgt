# Integer-theta Wiener–Hopf Fredholm index, Zhukovsky winding number, and effective collision rounding

- **ID:** cdg-integer-theta-collision-fredholm-winding
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-3110/obstacles-summary.md` §2.5.3 (Route WD, milestones A8 and B12).
- **Statement:** Explicit integer-theta curvature error constants give an explicit fixed-window rounding rate (A8) and a height-uniform stage `N_univ = 6` controlling the theta-prefix product-current error across all real heights simultaneously (B12); on every height window, finite integer theta amplitudes and first moments construct a confocal-Zhukovsky Laurent loop and a Wiener–Hopf operator on `L²(ℝ)` whose winding number and Fredholm index equal the horizontal collision charge `O(T)`, while a two-scale separation law is proved necessary by a multiple-zero bifurcation obstruction.

## Goal

Solve the open synthesis question of `obstacles-summary.md`:
1. Eliminate all existential constants from the finite-theta collision-reading error, give an explicit closed-form rounding threshold for `⌊finiteThetaCollisionReading T n + 1/2⌋₊ = O(T)` (A8), and establish height-uniform theta-current control at one universal stage `n ≥ 6` independent of height `T` together with uniform zero-collision vanishing under `RiemannHypothesis` (B12).
2. Construct from integers alone (`finiteThetaAmplitude N`, `finiteThetaFirstMoment N`, built from finite Jacobi-theta integer shells and the Gamma/Laplace kernel, with no zero locations and no `floor`/`round` of real readings) an analytic Laurent loop on `UnitCircle` and a Wiener–Hopf Fredholm operator on `L²(ℝ)` whose winding number and Fredholm index equal `(O(T) : ℤ)` on every natural-height (and real-height) window, together with its equivalence to `RiemannHypothesis`, homotopy invariance, and two-scale sharpness at multiple critical-line zeros.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, two-scale obstruction identified
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions/ConjugateDiagonalGeometry/`, leaf checks green, `#print axioms` clean

## Complete Mathematical Construction and Dependency-Closed Proof (`[PROVED HERE]`)

### Part I: Explicit Theta-Current Constants, Fixed-Window Rounding Rate (A8), and Height-Uniform Law (B12)

1. **Explicit `riemannXi` quadratic growth (`A = 5`):**
   On `[1, ∞)`, `1 ≤ evenKernel 0 x` (`XiThetaExplicitBounds.one_le_evenKernel_zero`) and `evenKernel 0 x - 1 ≤ 3 exp(-π x)` (`XiThetaExplicitBounds.evenKernel_zero_sub_one_le`), so `‖riemannThetaTail x‖ ≤ 3 exp(-π x)`. Substituting `(C, p) = (3, π)` into `RiemannGaussian.norm_completedRiemannZeta₀_le` yields
   `‖completedRiemannZeta₀ z‖ ≤ (6/π) exp((2/π)(‖z‖ + 1)²) ≤ 2 exp((‖z‖ + 1)²)` since `π > 3`. Absorbing `‖z‖ · ‖1 - z‖ + 1` as in `riemannXi_quadraticGrowth` (`K = 2, B = 1, A = K + B + 2 = 5`) gives for all `z ∈ ℂ`:
   `‖RiemannGaussian.riemannXi z‖ ≤ exp(5 (‖z‖ + 1)²)`.

2. **Explicit planar log-square and theta-potential constants:**
   Since `exp(1/2)² = exp 1 < 4`, `1/2 < log 2 ≤ 1` and `3 < π < 4`. Substituting `A = 5` into `xi_log_sq_canonical_integrable_bound` (`b = 1960 + log 2 ≤ 1961`, `d = 3645 / log 2 ≤ 7290`) bounds the planar log-square integral on `closedBall 0 (n + 2)` by `C_logsq · (n + 1)⁶` with `C_logsq := 3 · 10¹²`.
   For the finite-theta integer tail: `(m/4) ≤ exp(m/4)` implies `m⁴ ≤ 256 exp(m) ≤ 256 exp(m²)`, and `-(π - 1) m² + m² ≤ -m` (`π > 3`), so `thetaCuspIntegerTailWeight m ≤ 2 exp(4) · 256 exp(-m)`. Since `exp 1 ≤ 3` (`exp 4 ≤ 81`) and `∑_{m≥0} exp(-m) = (1 - e⁻¹)⁻¹ ≤ 2`, `thetaCuspIntegerTailConstant ≤ 2 · 81 · 256 · 2 = 82944 ≤ 10⁵`, hence `thetaCuspHigherAtomDominationWeight ≤ 10⁵` and `thetaEnvelopeUpper ≤ (1 + 10⁵) · 64 ≤ 7 · 10⁶`. Moreover `(1 + x²)/4 ≤ (1 + |x|/2)² ≤ exp |x|`, so `thetaAmplitudeProfileMass = ∫_ℝ exp(-|x|) dx ≤ 4 ∫_ℝ (1 + x²)⁻¹ dx = 4π ≤ 16`.
   Consequently `finiteThetaPotentialConstant ≤ 10⁵ · (7 · 10⁶ · 16)² ≤ 2 · 10²¹`, and the scalar/product-current constant satisfies
   `K ≤ 2 · (2 · 10²¹) + (2π)⁻¹ (2π + 8 · 3 · 10¹²) ≤ 5 · 10²¹ =: K_explicit`.

3. **Explicit Jensen divisor count and universal height-independent current threshold (`N_univ = 6`):**
   For any `r > 0`, `jensen_riemannXi_divisor_le` with `A = 5` and `log 2 > 1/2` gives
   `∑_{z ∈ B̄(0,r)} zeroMult(ξ, z) ≤ 5 (2r + 1)² / log 2 ≤ 10 (2r + 1)²`.
   In particular `xiStripWindowTotalOrder T ≤ M_upper(T) := 10 (2 (R_T + 3) + 1)²` (`R_T = collisionWindowRadius T`).
   Let `k := thetaCollisionStage T n = n + R_T + 4 + ⌈B_{T,n}⌉`. Whenever `n ≥ 6`, `k ≥ 10` and `R_T + 3 ≤ k - 7 < k`. For `k ≥ 10`, `-k⁴ + 56 k² + 62 ≤ -30 k² ≤ -300 k`. Since `K_explicit = 5 · 10²¹ < 2⁸⁰ ≤ exp(80)` and `B_{T,n} ≤ k ≤ exp(k)`,
   `ε_{T,n} := K_explicit B_{T,n} exp(-k⁴ + 56 k² + 62) ≤ exp(80 - 299 k) < 1/1000`.
   Meanwhile `finiteThetaSourceReading (sourceCutoff (R_T + 1)) k ≤ 10 (2k + 1)² + ε_{T,n} ≤ 90 k² + 1`. Since `k² ≤ 2 exp(k)`, for every `T ∈ ℝ` and every `n ≥ 6`:
   `ε_{T,n} · (2 Q_k(χ_{R_T + 1}) + ε_{T,n}) ≤ exp(80 - 299 k) · (360 exp(k) + 3) < 1/8`.
   This bound is **completely uniform in `T ∈ ℝ`** with universal stage threshold `N_univ = 6`.

4. **Explicit rounding rate (A8) and uniform-in-height critical-line law (B12):**
   - **(A8 / Gap-calibrated B12):** For any `T ∈ ℝ` and `0 < δ ≤ collisionWindowGap T`, set
     `thetaCollisionRoundingStage(T, δ) := max 6 ⌈√(max 1 (log(8 · (M_upper T)²))) / δ⌉₊`.
     For `n ≥ thetaCollisionRoundingStage(T, δ)`, `n δ ≥ 1` (so the height collars equal `1_{[0,T)}` on all zeros in `B̄(0, R_T + 3)`) and `n² δ² ≥ log(8 M_upper(T)²)` (so `(xiStripWindowTotalOrder T)² exp(-n² δ²) ≤ M_upper(T)² / (8 M_upper(T)²) = 1/8`). Combining with the `< 1/8` uniform product-current bound gives `|finiteThetaCollisionReading T n - O(T)| < 1/4`, hence `⌊finiteThetaCollisionReading T n + 1/2⌋₊ = O(T)`.
   - **(Height-uniform critical-line vanishing and RH equivalence):** Because `horizontalCollisionGaussian q z w = exp(-q(Im z - Im w)²)(1 - exp(-q(Re z - Re w)²))` vanishes identically whenever `Re z = Re w`, if all zeros of `ξ` have `Re z = 1/2`, then `collisionWindowPairTest T R_T n z w = 0` on all zero pairs regardless of zero spacing or boundary proximity. Hence under `RiemannHypothesis`, **for all `T ∈ ℝ` and all `n ≥ 6` simultaneously**, `0 ≤ finiteThetaCollisionReading T n < 1/8` and `⌊finiteThetaCollisionReading T n + 1/2⌋₊ = 0`. Conversely, vanishing of the rounded reading on natural-height windows implies `O(m) = 0` for all `m : ℕ`, hence `RiemannHypothesis`.

---

### Part II: Newton Difference Polynomial, Confocal Zhukovsky Winding, and Integer-Theta Wiener–Hopf Fredholm Operator

1. **Exact difference polynomial from power sums (`NewtonDifferencePolynomial`):**
   For any `s : ℕ → ℂ`, define `newtonElem s : ℕ → ℂ` recursively by `newtonElem s 0 = 1` and
   `newtonElem s (k + 1) = ((k + 1 : ℂ))⁻¹ * ∑_{j=0}^k (-1)^j * newtonElem s (k - j) * s (j + 1)`,
   and define `newtonPoly M s := ∑_{k=0}^M C((-1)^k * newtonElem s k) * X^{M - k} ∈ ℂ[X]`.
   For a list `L : List ℂ`, let `revPoly L = ∏_{a ∈ L} (1 - C a * X)`. By induction on `L`, `-derivative (revPoly L)` satisfies `-derivative (revPoly L) ≡ revPoly L * ∑_{j=0}^{K-1} C(∑_{a ∈ L} a^{j+1}) X^j (mod X^K)`, equating `(revPoly L).coeff k` to `(-1)^k newtonElem s k` for `k ≤ L.length` and hence `newtonPoly L.length s = ∏_{a ∈ L} (X - C a)`.
   Given power sums `s` of a weighted root set `(t, z, m)` of total multiplicity `M = ∑_{i ∈ t} m_i` (`s r = ∑_{i ∈ t} m_i z_i^r` for `r ≥ 1`), define the binomial convolution
   `pairDiffPowerSum M s K := ∑_{r=0}^K (-1)^{K - r} C(K, r) s̃(r) s̃(K - r)` (`s̃(0) = M`, `s̃(r+1) = s(r+1)`).
   Expanding `(z_i - z_j)^K` shows `pairDiffPowerSum M s K = ∑_{i,j ∈ t} m_i m_j (z_i - z_j)^K`, so
   `pairDiffPoly M s := newtonPoly (M²) (pairDiffPowerSum M s) = ∏_{i ∈ t} ∏_{j ∈ t} (X - C(z_i - z_j))^{m_i m_j}` identically.

2. **Confocal Zhukovsky Laurent factor and two-scale obstruction (`ZhukovskyCollisionWinding`):**
   - **Multiple-zero single-scale obstruction:** For `P_ε(z) = (z - 1/2)² + ε` (`ε > 0`), `P_0` has a double zero on the critical line (`O = 0`), whereas for every `ε > 0`, `P_ε` has distinct horizontal zeros `1/2 ± √ε` with equal imaginary part `0`, jumping the raw horizontal collision charge of `P_ε` to `2 ≠ 0`. Thus single-scale raw collision counting on `A_N` cannot be homotopy-stable across critical-line multiple zeros; a two-scale separation `r_{T,n} ≪ 1/n` is mandatory.
   - **Confocal Zhukovsky ellipse (`n ≥ 6`):** Set `a_n = 1/2 - 1/(2n)`, `b_n = 1/n` (`0 < b_n < a_n`), `c_n = √(a_n² - b_n²) > 0`, `ρ_n = (a_n + b_n)/c_n > 1`, so `(c_n/2)(ρ_n + ρ_n⁻¹) = a_n` and `(c_n/2)(ρ_n - ρ_n⁻¹) = b_n`. Define `J_n(z) = 1/2 + (c_n/2)(z + z⁻¹)`. On `z = ρ_n e^{iθ}`, `J_n(ρ_n e^{iθ}) = 1/2 + a_n cos θ + i b_n sin θ`, whose normalized quadratic form `E_n(w) := (Re w - 1/2)² / a_n² + (Im w)² / b_n²` equals `1`.
   - **Exact winding dichotomy:**
     - If `E_n(d) < 1`: for `σ ∈ [0, 1]`, `d(σ) = 1/2 + σ(d - 1/2)` satisfies `E_n(d(σ)) = σ² E_n(d) < 1`, so `J_n(ρ_n e^{iθ}) - d(σ) ≠ 0`. By `windingNumber_homotopy_invariant`, the winding equals that at `d = 1/2`, where `J_n(ρ_n e^{iθ}) - 1/2 = (c_n ρ_n / 2) e^{-iθ} (e^{iθ} - i/ρ_n)(e^{iθ} + i/ρ_n)` has winding `0 + (-1) + 1 + 1 = +1` (`‖±i/ρ_n‖ = ρ_n⁻¹ < 1`).
     - If `E_n(d) > 1`: for `σ ≥ 1`, `d(σ) = 1/2 + σ(d - 1/2)` satisfies `E_n(d(σ)) = σ² E_n(d) > 1`. Choosing `σ = R_far > 1` with `‖d(R_far) - 1/2‖ > a_n + b_n ≥ ‖J_n(ρ_n e^{iθ}) - 1/2‖` places `(J_n(ρ_n e^{iθ}) - d(R_far)) / (1/2 - d(R_far))` inside `ball 1 1`, giving winding `0` (`windingNumber_eq_zero_of_ball1`).

3. **Source-pure window operator from integer theta prefixes (`IntegerThetaCollisionFredholmIndex`):**
   For `T ∈ ℝ` and `n, N ∈ ℕ`, let `z₁(n) = -1/2 - (1/(2n)) i` and `z₂(T, n) = 3/2 + max(-1/(2n), T - 1/(2n)) i`. Define purely from `A_N := finiteThetaAmplitude N` and `A_N' = -finiteThetaFirstMoment N`:
   - Topological boundary degree (no rounding):
     `M(T, n, N) := (RHTower.windingNumber (t ↦ A_N(rectangleBoundaryPath z₁(n) z₂(T, n) t)) 0 1).toNat`.
   - Contour power sums (`r ≥ 1`):
     `s_r(T, n, N) := (2πi)⁻¹ rectIntegral (z ↦ z^r · (-finiteThetaFirstMoment N z / finiteThetaAmplitude N z)) z₁(n) z₂(T, n)`.
   - Difference polynomial & doubled Zhukovsky Laurent loop:
     `D_{T,n,N} := pairDiffPoly (M(T, n, N)) (s_.(T, n, N))`,
     `Λ_{T,n,N}(u) := (D_{T,n,N}.eval (J_n(ρ_n u)))²` (`u ∈ UnitCircle`).
   - Unimodular symbol & Wiener–Hopf operator on `L²(ℝ)`:
     `U_{T,n,N} := unitNormalizeSymbol Λ_{T,n,N} ∈ C(UnitCircle, ℂ)`,
     `T_{T,n,N} := HTGeometry.wienerHopfLift U_{T,n,N} : L2Real →L[ℂ] L2Real`.

4. **Exact index theorem and corollaries:**
   Adjoin `0, 1, iT` to the zeros of `ξ` in `B̄(0, R_T + 3)` to form `S_ext(T)` with `δ(T) := finiteCollisionGap(S_ext(T)) > 0`. Set `n₀(T) := max 8 ⌈4 / δ(T)⌉₊` and `r_n := 1/(16 n²)`.
   For `n ≥ n₀(T)`:
   - When `T ≤ 0`, `z₁(n).im = z₂(T, n).im = -1/(2n)`, `ξ` is zero-free on the segment `[-1/2, 3/2] × {-1/(2n)}` (since `1/(2n) < δ(T)`), so for `C_strip exp(-(N+1)²) < inf ‖ξ‖` on that segment (`norm_finiteThetaAmplitude_sub_full_le_strip`), `A_N ≠ 0` on the segment, `rectIntegral = 0`, `M = 0`, `D = 1`, `Λ ≡ 1`, and `fredholmIndex T_{T,n,N} = 0 = O(T)`.
   - When `T > 0`, the zeros of `ξ` in the closed rectangle `R_{T,n}` are precisely `S_T = (stripZeros_finite T).toFinset`, and the balls `B(ρ, 2 r_n)` (`ρ ∈ S_T`) are pairwise disjoint and strictly inside `R_{T,n}`. On the compact complement `K_free(T, n) := R_{T,n} \ ⋃_{ρ ∈ S_T} B(ρ, r_n)`, `inf_{K_free(T,n)} ‖ξ‖ =: m_{T,n} > 0`. For every `N ≥ N₀(T, n) := ⌈√(max 0 (log(2 C_strip / m_{T,n})))⌉₊`, `‖A_N - ξ‖ < ‖ξ‖` on `K_free(T, n)`.
     Hence `A_N ≠ 0` on `K_free(T, n)` (including `∂R_{T,n}`), all zeros `Z` of `A_N` in `R_{T,n}` lie in `⋃_{ρ ∈ S_T} B(ρ, r_n)`, and the linear Rouché homotopy `(1 - σ)ξ + σ A_N` on each `∂B(ρ, r_n)` gives `∑_{ζ ∈ Z ∩ B(ρ, r_n)} zeroMult(A_N, ζ) = zeroMult(ξ, ρ)`.
     By FTC on `contLog(A_N ∘ γ)` off `rectangleCornerTimes` together with `exists_multi_peel`, `rectIntegral_logDeriv_boxCount`, and `rectIntegral_mul_logDeriv_boxCount`, `M(T, n, N) = ∑_{ζ ∈ Z} m_N(ζ)` and `s_r(T, n, N) = ∑_{ζ ∈ Z} m_N(ζ) ζ^r` for all `r ≥ 1`. Hence `D_{T,n,N}(w) = ∏_{ζ,ω ∈ Z} (w - (ζ - ω))^{m_N(ζ) m_N(ω)}`.
     For `ζ ∈ B(ρ, r_n)` and `ω ∈ B(σ, r_n)`, `‖(ζ - ω) - (ρ - σ)‖ < 2 r_n = 1/(8 n²)`:
     - `ρ = σ`: `|Re(ζ - ω) - 1/2| > 1/2 - 1/(8n²) > a_n`, so `E_n(ζ - ω) > 1` (winding `0`).
     - `Im ρ ≠ Im σ`: `|Im(ζ - ω)| > 4/n - 1/n = 3/n > b_n`, so `E_n(ζ - ω) > 1` (winding `0`).
     - `Im ρ = Im σ, Re ρ < Re σ`: `Re(ζ - ω) < 1/(8n²)`, so `1/2 - Re(ζ - ω) > a_n`, `E_n(ζ - ω) > 1` (winding `0`).
     - `Im ρ = Im σ, Re ρ > Re σ`: `Re(ρ - σ) ∈ [4/n, 1 - 8/n]`, so `|Re(ζ - ω) - 1/2| < 1/2 - 3/n`, giving `1 - (Re(ζ - ω) - 1/2)² / a_n² > 5/n > 1/(64 n²) > (Im(ζ - ω))² / b_n²`, i.e., `E_n(ζ - ω) < 1` (winding `+1`).
     Summing over `Z × Z` and squaring gives `Λ_{T,n,N}(u) ≠ 0` on `UnitCircle` and
     `fredholmIndex T_{T,n,N} = circleWinding U_{T,n,N} = windingNumber Λ_{T,n,N} = 2 ∑_{Im ρ = Im σ, Re ρ > Re σ} m_ξ(ρ) m_ξ(σ) = O(T)`.
   - **Corollaries:**
     1. Unconditional Fredholmness and even index `2 ∣ fredholmIndex T_{T,n,N}` for all `(T, n, N)`.
     2. Equivalence with `RiemannHypothesis`: `RiemannHypothesis ↔ ∀ m : ℕ, ∃ n₀, ∀ n ≥ n₀, ∃ N₀, ∀ N ≥ N₀, fredholmIndex (T_{m,n,N}) = 0` (and `< 2` suffices).
     3. Norm-continuous homotopy invariance of `fredholmIndex` along zero-free boundary deformations.

## Log
- 2026-10-31 — created in 1-in-progress and promoted to 2-fully-proven with complete dependency-closed paper proof.
