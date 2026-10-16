# CHMD pole-density law and Chebyshev-discrepancy transport (2026-10-16, MUST-1566 / MUST-1567)

Two modules, namespace `RHTower.CHMDChebyshevTransport`, wired in `RHTower.lean` after
`CHMDLightConeBesselZeroAndIntegrationByParts`. Card:
`docs/drafts/pipeline/3-formalized/chmd-pole-density-law-chebyshev-discrepancy-transport-2026-10-16.md`.

## Module 1: `RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport` (MUST-1566)
- `integral_dAlembertReal_mul_exp_half`: `∫ D(u) e^{u/2} du = 1/cos²(1/4)` (pole constant), via
  `one_div_sinh_pi_mul_eq_tsum`, `integral_Ioi_mul_exp_neg_mul`, `tsum_rate_sq_inv`,
  `pi_sq_div_sin_sq_eq_tsum` (csc² partial fractions at real x ∈ (0,1) from mathlib `cot_series_rep'`
  differentiated termwise with `hasDerivAt_tsum_of_isPreconnected`).
- `integral_dAlembert_pair_mul_exp_half`: massless pole law `∫ (D(s+v)+D(s−v)) e^{s/2} = (2/cos²(1/4)) cosh(v/2)`.
- `integral_chmdPrimeKernel_mul_exp_half`: KG pole law `∫ K_y(s) e^{s/2} ds = chmdPoleWave y`;
  `integral_chmdPrimeKernel_sub_mul_exp_half`: `∫ K_y(s−u) e^{s/2} = e^{u/2} chmdPoleWave y`.
- `chmdPrimeWave_eq_chmdPoleWave_add_transport`: `chmdPrimeWave = chmdPoleWave + chebyshevDiscrepancyTransport − poleShadow`,
  `|poleShadow| ≤ 8/π`, `|K_y| ≤ 4/π`; `riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow` / `_bddAbove`.

## Module 2: `RHTower/CHMDChebyshevDiscrepancyDerivativeTransportLaw` (MUST-1567)
- `dAlembertDeriv` (= Re deriv of the analytic kernel `2/S`), `hasDerivAt_dAlembertReal`, `continuous_dAlembertDeriv`,
  `dAlembertDeriv_of_ne` (explicit formula), `exists_abs_dAlembertDeriv_le` (`|D'| ≤ C(1+|v|)e^{−π|v|}`), `shift_decay_le`.
- `kernelDeriv y s = D'(s+y)+D'(s−y) − (y²/2)∫B(D'+D')`, `hasDerivAt_chmdPrimeKernel_right`, decay `e^{−(π−1)|s|}` of
  `K_y` and `∂_sK_y` (`exists_abs_chmdPrimeKernel_le`, `exists_abs_kernelDeriv_le`), limits, integrability.
- `chebyshevStep s = Σ_{log n < s} Λ(n)/√n` (tsum with finite support), `chebyshevDiscrepancy = Ψ − 2e^{s/2}`,
  `chebyshevStep_le` (Chebyshev bound via `Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le`), monotone ⇒ measurable.
- `tsum_chmdPrimeWeight_mul_kernel_eq`: `Σ_n w_n K_y(log n) = −∫_0^∞ ∂_sK_y Ψ` (Stieltjes IBP over prime powers).
- `integral_Ioi_kernelDeriv_mul_two_exp_half`: `∫_0^∞ ∂_sK_y·2e^{s/2} = −2K_y(0) − ∫_0^∞ K_y e^{s/2}`.
- `chmdPrimeWave_eq_pole_add_derivative_transport`: `chmdPrimeWave = chmdPoleWave + 2K_y(0) − poleShadow − ∫_0^∞ ∂_sK_y Δ`;
  `chebyshevDiscrepancyTransport_eq`; `riemannHypothesis_iff_integral_kernelDeriv_mul_discrepancy_bddAbove` / `_bddBelow`.

Meaning: the KG propagation of the PNT density `e^{s/2}ds` is exactly the ζ-pole wave; after this exact transport
the prime wave contains no `e^{y/2}` object, and the light-cone route's one-sided bound is the pairing of the classical
√-weighted Chebyshev discrepancy with the exponentially localized odd kernel `∂_sK_y` (Wall 1 in KG coordinates).
## Module 3: `RHTower/CHMDPrimeKernelDerivativeUniformBound` (MUST-1568)
- `kernelDeriv_eq_kernelDerivFourier`: `∂_sK_y(s) = −(1/π)∫ cos(y√(r²+2)) sech²(r/2) r sin(rs) dr`; `kernelDeriv_neg`, `kernelDeriv_zero`.
- `integral_abs_mul_sechSqHalf`: `∫|r| sech²(r/2) dr = 8 log 2` (primitive `sechMomentPrimitive`).
- `abs_kernelDeriv_le`: `|∂_sK_y(s)| ≤ 8 log 2/π` uniformly in y, s; `abs_chmdPrimeKernel_sub_le` (uniform Lipschitz);
  `abs_setIntegral_kernelDeriv_mul_discrepancy_le` (window estimate, uniform in y).
Open: Step 3 of cmhd-plan = one-sided uniform bound on `∫_0^∞ ∂_sK_y Δ`; under RH Δ = O(s²) so window bounds grow — cancellation needed (Wall 1).

Lean notes: clamp the Bessel parameter (`clampUnit`) for Fubini on the restricted product measure; give `(f := …)` to
`norm_integral_le_of_norm_le`; `(μ := volume)` for `integral_sub_right_eq_self`; `IntegrableOn.congr_fun` must be called with
an explicitly typed `IntegrableOn` (the `.const_mul` result displays as `Integrable` and field notation fails);
`linarith` treats `8/π` and `2*(4/π)` as different atoms — add the ring identity; use `Pi.mul_apply` before linarith on
`integral_Ioi_of_hasDerivAt_of_tendsto` outputs.
