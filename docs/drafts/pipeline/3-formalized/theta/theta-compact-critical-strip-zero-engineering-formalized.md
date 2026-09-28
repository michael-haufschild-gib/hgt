# Compact theta perturbations placing a zero inside the Xi strip — Lean certificate

- **Paper card:** `theta-compact-critical-strip-zero-engineering.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaCompactStripZeroEngineering` (compact version,
  claims 1–5), `GaloisForLFunctions.RHTower.ThetaAnalyticStripZeroEngineering` (real-analytic
  variant, relative tail, compact-open convergence, entire Fourier transforms),
  `GaloisForLFunctions.RHTower.ThetaSourceSurgeryToolkit` (strong log-concavity of `k`, strip
  evaluation, critical charge of `k`, nonvanishing of `Ξ` on horizontal lines); general layers
  `GaloisForLFunctions.HTGeometry.OscillatoryPacketFourier` (Riemann–Lebesgue packet limits, real
  2×2 solve, packet derivative bounds), `GaloisForLFunctions.HTGeometry.EvenAnchorProjection`
  (anchor independence, invertible Gram matrix, projection); corpus
  `HedenmalmThetaSourceSpectrumExact` (`Ξ = ∫ e^{-izx} k`), `XiHorizontalStripDecay`,
  `ThetaCuspKernelLogConcavity`, `ThetaPrimeDeletionMellin`/`ThetaPrimeDeletionSpectralEscape`
  (deletion floor `D_S k ≥ a₁`), `ThetaCuspComplexStrip` (strip continuation of `k`),
  `ThetaZeroDivisionSource` (`ExpMomentSource`, entire `sourceTransform`), `Sieve.EulerExpansion`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`, no hypotheses
  beyond the card's own quantifiers (`0 < v < 1/2`, moment depth `J`).

Dictionary: `k = thetaCuspFullSource`, `N = J/2`, `ψ = compactWeight` (compact) /
`surgeryGaussWeight = k e^{-x²}` (analytic), anchors `A_i = evenAnchor N i`, `Π = anchorProj`,
`G = anchorGram`, `E_u(b) = stripEval v u b = ∫ e^{-i(u+iv)x} b`, `g_u = compactSurgerySource N v u`
(compact) / `gaussSurgerySource N v u` (analytic), `r_u = gaussRelative`, continuation
`gaussSurgeryC`, `D_S = thetaPrimeDeletion S`, `h = a₁ = thetaCuspSourceTerm · 1`.

| Card item | Lean theorem |
|-|-|
| anchors `1, x², …, x^{2N}, cosh(x/2)` independent on any interval; Gram matrix invertible; `Π` kills all anchors, preserves evenness | `evenAnchor_combination_eq_zero`, `AnchorWeight.isUnit_det`, `dotProduct_anchorGram_mulVec`, `integral_evenAnchor_mul_anchorProj`, `anchorProj_neg` |
| anchor coefficients of the packets vanish; `E_u(Π(ψ cos)) → ½∫ψe^{vx}`, `E_u(Π(xψ sin)) → -(i/2)∫xψe^{vx}` | `tendsto_anchorMoments_cos`, `tendsto_anchorMoments_sin`, `tendsto_anchorCoef`, `tendsto_stripEval_compactCosDirection`, `tendsto_stripEval_compactSinDirection` (general: `tendsto_packet_cos`, `tendsto_packet_sin`, `tendsto_packet_fixed`, `tendsto_integral_mul_cos`, `tendsto_integral_mul_sin`) |
| `A > 0`, `B = 2∫₀^∞ xψ sinh(vx) > 0` | `integral_exp_mul_compactWeight_pos`, `integral_exp_mul_id_mul_compactWeight_pos` |
| uniformly invertible real 2×2 system; `|α_u| + |β_u| = O(e^{-u/4})` | `exists_compactSolve`, `exists_coeff_decay`, `real_combination_eq`, `exists_real_solve_bound` |
| 1. `g_u = k` outside the fixed `[-2, 2]` | `compactSurgerySource_eq_of_two_le_abs` |
| 1. `g_u > 0`, globally strongly log-concave (`(log g_u)'' ≤ -2`); `(log k)'' ≤ -4` | `compactSurgerySource_pos_logConcave`, `thetaCuspLogConcavityNumerator_le`, `iteratedDeriv_two_log_eq` |
| 2. `∫ x^j g_u = ∫ x^j k`, `j ≤ J`; `∫ e^{x/2} g_u = ∫ e^{x/2} k = 1/2`; evenness | `integral_pow_mul_compactSurgerySource`, `integral_exp_half_mul_compactSurgerySource`, `integral_exp_half_mul_thetaCuspFullSource`, `compactSurgerySource_neg` |
| 3. `g_u → k` in every Schwartz seminorm | `compactSurgerySource_schwartz` (bounds: `exists_bound_iteratedDeriv_compactPerturbation`, `abs_iteratedDeriv_mul_cos_le`) |
| 4. entire `F_{g_u}` with `F_{g_u}(u + iv) = 0` | `stripEval_compactSurgerySource_eq_zero`, `differentiable_sourceTransform_compactSurgerySource`, `sourceTransform_eq_stripEval` |
| 4. genuine change at arbitrarily large `u` (`Ξ(u + iv) ≠ 0` there) | `exists_compactSurgerySource_ne`, `exists_XiC_horizontal_ne_zero` |
| 5. `D_S g_u(x) > 0` for all `x ≥ 0`, all finite prime sets `S` at once | `thetaPrimeDeletion_compactSurgerySource_pos`, `abs_thetaPrimeDeletion_le_of_support`, `thetaCuspSourceTerm_one_le_thetaPrimeDeletion` (corpus) |
| compact theorem, all claims together | `compact_critical_strip_zero_engineering` |
| analytic variant: same anchors, forced zero, evenness, positivity, strong log-concavity | `analytic_critical_strip_zero_engineering`, `integral_pow_mul_gaussSurgerySource`, `integral_exp_half_mul_gaussSurgerySource`, `stripEval_gaussSurgerySource_eq_zero`, `gaussSurgerySource_pos_logConcave` |
| analytic variant is real analytic, `g_u = k(1 + r_u)` | `analyticAt_gaussSurgerySource`, `gaussSurgerySource_eq` |
| analytic variant `→ k` in Schwartz topology | `gaussSurgerySource_schwartz` (Cauchy estimates: `abs_iteratedDeriv_gaussRelative_le`, `norm_gaussRelativeC_le`, `iteratedDeriv_re_ofReal`) |
| `g_u/k - 1 = O_u((1 + |x|)^N e^{-x²/2})`, faster than every `e^{-c|x|}` | `exists_abs_gaussSurgerySource_div_sub_le`, `exists_abs_gaussSurgerySource_div_sub_le_exp` |
| holomorphic continuation converges to the theta source uniformly on compacts of `|Im z| < π/4` | `tendstoUniformlyOn_gaussSurgeryC`, `differentiableOn_gaussSurgeryC`, `gaussSurgeryC_ofReal` |
| analytic variant has entire Fourier transform | `differentiable_sourceTransform_gaussSurgerySource` |
