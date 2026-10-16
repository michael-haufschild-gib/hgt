# CHMD: pole-density law and Chebyshev-discrepancy transport of the Klein–Gordon prime wave

- **ID:** chmd-pole-density-transport
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/cmhd-plan.md (Steps 1–2 of the light-cone roadmap) · STATUS MUST-1566
- **Statement:** `∫_ℝ K_y(s) e^{s/2} ds = chmdPoleWave y`, hence
  `chmdPrimeWave y = chmdPoleWave y + T(y) − S(y)` with `T(y) = Σ_n (Λ(n)/√n) K_y(log n) − ∫_0^∞ K_y(s) e^{s/2} ds`
  the Klein–Gordon transport of the exact `√`-weighted Chebyshev discrepancy measure and `|S(y)| ≤ 8/π`;
  `RH ⟺ T` bounded below on `[0,∞)` `⟺ T` bounded above.

## Goal
The light-cone route writes the prime wave as `L[P₀]` with `P₀ > 0` of exact growth `e^{y/2}`; the
pole counterterm `L[(2/cos²(1/4)) cosh(·/2)] = chmdPoleWave` is bounded, but the roadmap's Step 3
("exponential lower-order bound on `L[P₀]`") was still formulated against `P₀`, an object of exact
exponential growth, so no kernel bound could ever close it. The obstruction removed here is
structural: the prime-number-theorem density `e^{s/2} ds` itself is transported by the Klein–Gordon
prime kernel exactly onto the pole wave. After that exact transport no object of growth `e^{y/2}`
remains; the one-sided bound of the route is carried entirely by the arithmetic discrepancy measure
`Σ_n (Λ(n)/√n) δ_{log n} − e^{s/2} ds` paired with the uniformly bounded kernel `|K_y| ≤ 4/π`.
Nothing in the construction uses zeros, positivity premises or hypotheses.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof (below), no open dependency
- [x] 2 → 3  formalized: `RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport`,
  `lake --old env lean` clean, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), wired into `RHTower.lean`
- [ ] 3 → 4  publication-ready (not pursued; RH-only policy)

## Approach
1. **Cosecant-square partial fractions at a real point.** For `0 < x < 1`,
   `π²/sin²(πx) = 1/x² + Σ_{n≥0} (1/(x−(n+1))² + 1/(x+(n+1))²)`: differentiate mathlib's cotangent
   Mittag-Leffler series `π cot(πz) − 1/z = Σ (1/(z−(n+1)) + 1/(z+(n+1)))` termwise on the complex ball
   `|z − x| < min(x,1−x)/2` (uniform summable derivative bounds `1/(n+(1−x)/2)² + 1/(n+1)²`), compare with
   the direct derivative `−π²/sin²(πz) + 1/z²`, and descend to `ℝ`.
2. **Pole constant.** For `u > 0`, `1/sinh(πu) = 2 Σ_k e^{−(2k+1)πu}`; with `∫_0^∞ u e^{−bu} du = 1/b²`
   (Gamma integral) and Tonelli, `∫_0^∞ u cosh(u/2)/sinh(πu) du = Σ_k (1/((2k+1)π−½)² + 1/((2k+1)π+½)²)`.
   Writing `(2k+1)π ± ½ = 2π(k + x₀)`, `2π(k + 1 − x₀)` with `x₀ = ½ + 1/(4π)`, the series equals
   `(1/4π²)·π²/sin²(πx₀) = 1/(4 cos²(1/4))` because `sin(πx₀) = sin(π/2 + 1/4) = cos(1/4)`.
   Symmetrizing, `∫_ℝ D(u) e^{u/2} du = ∫ D cosh(u/2) = 2∫_0^∞ 2u cosh(u/2)/sinh(πu) = 1/cos²(1/4)`.
3. **Massless pole law.** Translating, `∫ (D(s+v) + D(s−v)) e^{s/2} ds = (e^{−v/2} + e^{v/2})/cos²(1/4) = (2/cos²(1/4)) cosh(v/2)`.
4. **Klein–Gordon pole law.** `K_y(s) = D(s+y) + D(s−y) − (y²/2) T_y(s)` with the light-cone tail
   `T_y(s) = ∫_{−1}^{1} B(2y²(1−t²)) (D(s+yt) + D(s−yt)) dt`. Inside the cone the pair is dominated by
   `16(1+|y|) e^{π|y|} e^{−(π−1)|s|}`, so `T_y(s) e^{s/2}` is integrable and Fubini (with the Bessel
   parameter clamped to `[−1,1]`) gives `∫ T_y(s) e^{s/2} ds = (2/cos²(1/4)) ∫_{−1}^{1} B(2y²(1−t²)) cosh(yt/2) dt`.
   Hence `∫ K_y e^{s/2} = (2/cos²(1/4)) [cosh(y/2) − (y²/2)∫ B cosh(yt/2)] = (2/cos²(1/4)) cos(y√(7/4)) = chmdPoleWave y`
   by the light-cone identity. Spatial form: `∫ K_y(s−u) e^{s/2} ds = e^{u/2} chmdPoleWave y`.
5. **Transport law.** `K_y` is even in `s` and `|K_y| ≤ 4/π` (total sech² mass). Splitting the pole law
   at `0`, `chmdPoleWave y = ∫_0^∞ K_y e^{s/2} + S(y)` with `S(y) = ∫_0^∞ K_y(s) e^{−s/2} ds`, `|S| ≤ (4/π)·2`.
   With `chmdPrimeWave y = Σ_n (Λ(n)/√n) K_y(log n)` this is the law; the `RH` equivalences follow
   from the corpus receiver `RH ⟺ chmdPrimeWave` bounded below (above) on `[0,∞)` and `|chmdPoleWave| ≤ 2/cos²(1/4)`.

## No-go closure
Not a no-go. Positive structural law; the remaining target of the route is the one-sided bound on the
transported discrepancy `T`, i.e. one-sided `√x` prime counting (Wall 1) in Klein–Gordon coordinates with
the pole density removed exactly rather than asymptotically.

## Lean
Module `formal/GaloisForLFunctions/RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean`
(namespace `RHTower.CHMDChebyshevTransport`): `pi_sq_div_sin_sq_eq_tsum`, `one_div_sinh_pi_mul_eq_tsum`,
`integral_Ioi_mul_exp_neg_mul`, `tsum_rate_sq_inv`, `integral_Ioi_mul_cosh_half_div_sinh`,
`integral_dAlembertReal_mul_exp_half`, `integral_dAlembert_pair_mul_exp_half`,
`masslessPrimeWave_eq_pole_add_massless_transport`, `dAlembert_pair_shift_le`, `lightConeTail`,
`integrable_chmdPrimeKernel_mul_exp_half`, `integral_lightConeTail_mul_exp_half`,
`integral_chmdPrimeKernel_mul_exp_half`, `integral_chmdPrimeKernel_sub_mul_exp_half`,
`chmdPrimeKernel_neg_right`, `abs_chmdPrimeKernel_le`, `poleShadow`, `abs_poleShadow_le`,
`chebyshevDiscrepancyTransport`, `chmdPoleWave_eq_integral_Ioi_add_poleShadow`,
`chmdPrimeWave_eq_chmdPoleWave_add_transport`, `riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow`,
`riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddAbove`.
Audit: `lake --old env lean` on the module (olean produced), `#print axioms` on all main theorems in a
scratch file: only `propext`, `Classical.choice`, `Quot.sound`. Wired in `RHTower.lean` after
`CHMDLightConeBesselZeroAndIntegrationByParts`. No full or umbrella build was run.

## Log
- 2026-10-16 — created directly in 3-formalized (paper proof and Lean module completed in one pass); STATUS MUST-1566.

## Function form (second module)
Module `formal/GaloisForLFunctions/RHTower/CHMDChebyshevDiscrepancyDerivativeTransportLaw.lean`
(same namespace). With the space derivative `∂_sK_y(s) = D'(s+y) + D'(s−y) − (y²/2)∫B(2y²(1−t²))(D'(s+yt)+D'(s−yt))dt`
(`kernelDeriv`, `hasDerivAt_chmdPrimeKernel_right`), the classical step `Ψ(s) = Σ_{log n < s} Λ(n)/√n`
(`chebyshevStep`, Chebyshev bound `chebyshevStep_le`) and `Δ = Ψ − 2e^{s/2}` (`chebyshevDiscrepancy`):
- `tsum_chmdPrimeWeight_mul_kernel_eq`: `Σ_n (Λ(n)/√n) K_y(log n) = −∫_0^∞ ∂_sK_y Ψ` (Stieltjes IBP over prime powers;
  `K_y(ℓ) = −∫_ℓ^∞ ∂_sK_y`, Tonelli with `Σ n·n^{−(π−1)} < ∞`).
- `integral_Ioi_kernelDeriv_mul_two_exp_half`: `∫_0^∞ ∂_sK_y · 2e^{s/2} = −2K_y(0) − ∫_0^∞ K_y e^{s/2}`.
- `chmdPrimeWave_eq_pole_add_derivative_transport`: `chmdPrimeWave y = chmdPoleWave y + 2K_y(0) − poleShadow y − ∫_0^∞ ∂_sK_y Δ`,
  `|2K_y(0) − poleShadow y| ≤ 16/π`; `chebyshevDiscrepancyTransport_eq`.
- `riemannHypothesis_iff_integral_kernelDeriv_mul_discrepancy_bddAbove` / `_bddBelow`.
Analytic inputs: `D'` via the analytic complex kernel `2/S` (`dAlembertDeriv`, explicit formula off the origin,
`|D'(v)| ≤ C(1+|v|)e^{−π|v|}` by compactness near 0 and `sinh x ≥ e^x/4` beyond), decay `e^{−(π−1)|s|}` of `K_y`
and `∂_sK_y` (`exists_abs_chmdPrimeKernel_le`, `exists_abs_kernelDeriv_le`). Audit: `lake --old env lean` clean,
`#print axioms` standard, wired after the first module. STATUS MUST-1567.

## Log (continued)
- 2026-10-16 — function-form module added; STATUS MUST-1567.

## Uniform derivative bound (third module)
Module `formal/GaloisForLFunctions/RHTower/CHMDPrimeKernelDerivativeUniformBound.lean` (same namespace).
- `hasDerivAt_chmdPrimeKernel_fourier`, `kernelDeriv_eq_kernelDerivFourier`: `∂_sK_y(s) = −(1/π)∫ cos(y√(r²+2)) sech²(r/2) r sin(rs) dr`
  (dominated differentiation with bound `|r| sech²(r/2)`, then uniqueness of derivatives against the light-cone form).
- `kernelDeriv_neg`, `kernelDeriv_zero`: odd in `s`.
- `integral_abs_mul_sechSqHalf`: `∫ |r| sech²(r/2) dr = 8 log 2` via `G(r) = 4r eʳ/(1+eʳ) − 4 log(1+eʳ)`.
- `abs_kernelDeriv_le`: `|∂_sK_y(s)| ≤ 8 log 2/π` for all `y, s`; `abs_chmdPrimeKernel_sub_le`: uniform Lipschitz bound.
- `abs_setIntegral_kernelDeriv_mul_discrepancy_le`: `|∫_{(0,L]} ∂_sK_y Δ| ≤ (8 log 2/π)∫_{(0,L]}|Δ|` for every `y`.
Limit of the estimate: under RH `Δ(s) = O(s²)`, so the window bound grows with `L`; the one-sided bound still needs
cancellation in the pairing. Audit: `lake --old env lean` clean, standard axioms, wired. STATUS MUST-1568.
- 2026-10-16 — uniform derivative bound module added; STATUS MUST-1568.
