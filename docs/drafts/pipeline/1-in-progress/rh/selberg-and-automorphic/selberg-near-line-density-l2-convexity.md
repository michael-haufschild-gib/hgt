# Selberg-type zero density near the line by L² convexity from the Levinson gate

- **ID:** R1-SELBERG-DENSITY
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), Lean in progress
- **Source:** route1 producer loop (cycles 69–72); user directive "build the Ingham machinery, then push the critical-scale producer with Selberg-type density"
- **Statement:** there is `C` such that for every `a ≥ 1`, eventually in `U`, admissible heights
  `T₁ ∈ (U/4, U/4+1)`, `T₂ ∈ (U/2−1, U/2)` exist with
  `#{ρ : ζ(ρ)=0, Re ρ ≥ 1/2 + 2a/log U, T₁ ≤ Im ρ ≤ T₂} ≤ (T₂−T₁) log U · C (1/a² + e^{−a/600}/a) + O(log² U)`.

## Goal
Near-line density with no power-of-log loss: the proportion of critical-scale right discs
(radius `2a/log U`) that contain a zero tends to `0` as `a → ∞`, uniformly in `U`. This is the
large-`a` complement of the `HD(1)` proportion producer (`XiCriticalScaleDiscSeamProportion`).
Classical content: Selberg 1946 (exponential decay `e^{-a/4}`); no external novelty claimed.

## Corpus assets (audited 2026-09-26)
- Consumer: `exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide`
  (`ZetaZeroDensityRightShiftedLine`), valid for `1/4 ≤ σ₀ < 2`:
  `2πΔ·N_{≥σ₀+Δ} ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`.
- Left gate: `exists_highBlock_bound_productAFE` (`ZetaGateProductAFEHighBlock`), mollifier
  `Ψ = Σ_{n≤N} μ(n) log(N/n)/log N · n^{-s}`, `N = ⌊U^{1/100}⌋`, on `σ = 1/2 − d`,
  `d log U ∈ [R,2R]`; its proof actually gives `(c₀+ε)(v−a+2a^{95/100})` (the stated `εa` is a
  simplification that is useless for windows of length `≪ a`).
- `barbanVehovCoeff_eq_vonMangoldt`: for `1 < n ≤ N` the coefficient of `ζΨ` is `Λ(n)/log N`.
- Heights: `exists_horizontal_slices_avoiding_entire_zeros`.
- Crude bounds: `norm_riemannZeta_le_quarter` (`|ζ| ≤ 2 + 8|t|`, `Re ≥ 1/4`, `|t| ≥ 2`).
- MVT: `dirichlet_meanValue_theorem` (error `4N(1+log N)Σ|a|²`).
- Chebyshev: `chebyshevPsi_le_six_mul_self_of_one_le`.

## Paper proof
Notation: `L = log U`, `N = ⌊U^{1/100}⌋`, `σ_L = 1/2 − 1/L`, `σ₀ = 1/2 + a/L`, `σ_R = 3`,
`H = U^{99/100}`, `P(s) = Σ_{n≤N} Λ(n)/log N · n^{-s}`, `f = ζΨ − 1 − P`.

1. **Dirichlet tail.** On `Re s > 1`, `ζΨ = Σ c_n n^{-s}`, `c_n = Σ_{d|n, d≤N} μ(d)log(N/d)/log N`.
   `c_1 = 1`, `c_n = Λ(n)/log N` for `1 < n ≤ N`, `|c_n| ≤ d(n) ≤ n`. Hence
   `f(s) = Σ_{n>N} c_n n^{-s}` and `|f(3+it)| ≤ Σ_{n>N} n^{-2} ≤ 1/N`.
2. **L² three lines.** `F` holomorphic on the open strip `σ_L<Re<σ_R`, continuous and bounded on its
   closure, `σ₀ ∈ [σ_L,σ_R]`, `λ = (σ₀−σ_L)/(σ_R−σ_L)`. If every translate satisfies
   `∫_A^B |F(σ_L + i(y+t))|² ≤ S_L` and `∫_A^B |F(σ_R + i(y+t))|² ≤ S_R`, then
   `∫_A^B |F(σ₀+it)|² ≤ S_L^{1−λ} S_R^λ`.
   Proof: `Φ(z) = ∫_A^B F(z+it) conj F(σ₀+it) dt` is holomorphic and bounded;
   Cauchy–Schwarz gives `|Φ| ≤ √(S_{L/R} I)` on the edges, `Φ(σ₀) = I`; Hadamard gives
   `I ≤ √I S_L^{(1−λ)/2} S_R^{λ/2}`.
3. **Windowed field.** `F_τ(z) = exp((z−iτ)²/H²) · ((z−1)/z) · f(z)` (entire on `Re z > 0` after
   pole clearing). `|exp(...)| = exp((σ² − (t−τ)²)/H²)`.
   - Right edge: `S_R ≤ 4H/N²`.
   - Left edge, translates within `U/8` of `τ ∈ [U/4, U/2+H]`: the window lies in `[U/8−H, U]`,
     refined gate + `1` + MVT for `P` give `S_L ≤ C₁H`. Far translates: Gaussian
     `e^{−U^{1/50}/256}` beats the crude `N² U³`.
   - Center: `|F_τ|² ≥ e^{−2}/2 · |f|²` on `|t−τ| ≤ H`, `|t| ≥ 1`.
   - `λ ≥ (a+1)/(3L)`, `(4/N²)^λ ≤ e^{−(a+1)/300}`, so
     `∫_{τ−H}^{τ+H} |f(σ₀+it)|² ≤ C₂ H e^{−a/300}`.
4. **Cover** `[T₁,T₂]` by `⌈(T₂−T₁)/2H⌉` windows: `∫_{T₁}^{T₂}|f(σ₀+it)|² ≤ C₂ e^{−a/300}(T₂−T₁)`.
5. **Low primes.** MVT + dyadic Chebyshev: `Σ_{n≤N} Λ(n) log n · n^{−1−2δ} ≤ C/δ²`, `δ = a/L`,
   `log N ≥ L/200`, so `∫_{T₁}^{T₂}|P(σ₀+it)|² ≤ C₃ (T₂−T₁)/a² + o(U)`.
6. **Mean square.** `|1+g|² ≤ (1+κ) + (1+1/κ)|g|²`, `κ = √η`: `Msq ≤ (T₂−T₁)(1 + 3√η + 2η)`,
   `η = C₃/a² + C₂e^{−a/300} + o(1)`.
7. **Density.** Consumer with `Δ = a/L`.
8. **Producer.** Bad critical-scale discs of radius `2a/L` ≤ zeros with `Re ≥ 1/2 + 2a/L`; the
   ratio to the `(T₂−T₁)L/(6a)` discs is `≤ C(1/a + e^{−a/600})`.

## Lean plan
- `HTGeometry/StripSquareMeanConvexity.lean` — step 2 (generic).
- `RHTower/ZetaMollifiedDisplacedWindowMeanSquare.lean` — refined gate.
- `RHTower/BarbanVehovMollifiedZetaTail.lean` — step 1.
- `RHTower/VonMangoldtMollifierPolynomialMeanSquare.lean` — step 5.
- `RHTower/SelbergNearLineMollifiedErrorMeanSquare.lean` — steps 3–4.
- `RHTower/SelbergNearLineZeroDensity.lean` — steps 6–7.
- `RHTower/XiCriticalScaleDiscSeamSelbergDensity.lean` — step 8.

## Log
- 2026-09-26 — created; corpus audit found the consumer and the gate already formal; paper proof above.

## Lean status (2026-09-26)
All modules check with `lake env lean`, no `sorry`, no warnings:
- `HTGeometry/StripSquareMeanConvexity.lean` — `integral_normSq_le_of_three_lines` (step 2).
- `RHTower/ZetaMollifiedDisplacedWindowMeanSquare.lean` — `exists_highBlock_window_bound_productAFE`
  (gate with loss `2a^{95/100}` instead of `εa`).
- `RHTower/BarbanVehovMollifiedZetaTail.lean` — `norm_hbMollifiedTail_le` (`‖ζΨ−1−P‖ ≤ 2/N`, `Re ≥ 3`).
- `RHTower/VonMangoldtMollifierPolynomialMeanSquare.lean` — `tsum_vonMangoldt_div_rpow_le_six`,
  `sum_vonMangoldt_sq_rpow_le` (`≤ 5/δ²`), `integral_normSq_edPoly_displaced_le`.
- `RHTower/SelbergNearLineGaussianField.lean`, `SelbergNearLineWindowBounds.lean`,
  `SelbergNearLineWindowConvexity.lean` — windowed field, edge bounds, one-window three-lines.
- `RHTower/SelbergNearLineMollifiedErrorMeanSquare.lean` —
  `exists_eventually_integral_hbMollifiedTail_rightShift_le`:
  `∫_{T₁}^{T₂}‖ζΨ−1−P‖²(1/2+a/log U+it) ≤ C e^{−(a+1)/300}(T₂−T₁+2U^{99/100})`.
- `RHTower/SelbergNearLineZeroDensity.lean` — `exists_selberg_nearLine_zeroDensity`,
  `tendsto_selbergNearLineRate`.
- `RHTower/XiCriticalScaleDiscSeamSelbergDensity.lean` —
  `exists_criticalScale_badDisc_proportion_le`: for every `ε>0` there is `a₀` with, for `a ≥ a₀` and
  large `U`, bad discs of radius `2a/log U` in `[T₁,T₂] ⊂ [U/4,U/2]` `≤ ε ·` discs in the window.
Deviation from the plan: the von Mangoldt head gives `η_P ≤ 400000/a²` (not exponential), so the
proportion decays like `1/a`; Selberg's `e^{−a/4}` needs σ-adapted sieve weights (not built).

## Long-mollifier barrier (2026-09-26)
- `RHTower/ZetaGaussianTwistedMoment.lean` — `norm_integral_twistedZeta_gauss_sub_diag_le`: Gaussian-windowed
  twisted first moment of `ζ`; errors `27√T n e^{1−R²/H²} + 2n(√(πH²/2)e^{1−H²/(128n²)} + e^{1−R²/H²}√(πH²))`.
- `RHTower/MollifiedMeanSquareGaussianPrimeFloor.lean` —
  `exists_eventually_integral_normSq_zetaMollified_rightShift_ge_of_lt_one`: for `a>0`, `0<θ<1`, mollifier length
  `y ≤ T^θ`, `b₁=1`, `|b_d|≤1`: `∫_T^{2T}|ζΨ(½+a/log T+it)|² ≥ (1+(1−θ)e^{−2a}/16)T`. Axioms: propext,
  Classical.choice, Quot.sound.
- Consequence: fixed-`a` density `o(1)` via the Littlewood consumer needs mollifiers of length `≥ T^{1−o(1)}`.
