# CHMD pole-density law and Chebyshev-discrepancy transport (2026-10-16, MUST-1566)

Module `formal/GaloisForLFunctions/RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean`
(namespace `RHTower.CHMDChebyshevTransport`), wired in `RHTower.lean` after
`CHMDLightConeBesselZeroAndIntegrationByParts`. Card:
`docs/drafts/pipeline/3-formalized/chmd-pole-density-law-chebyshev-discrepancy-transport-2026-10-16.md`.

Results (unconditional, standard axioms):
- `integral_dAlembertReal_mul_exp_half`: `∫ D(u) e^{u/2} du = 1/cos²(1/4)` (pole constant), via
  `one_div_sinh_pi_mul_eq_tsum`, `integral_Ioi_mul_exp_neg_mul`, `tsum_rate_sq_inv`,
  `pi_sq_div_sin_sq_eq_tsum` (csc² partial fractions at real x ∈ (0,1), from mathlib `cot_series_rep'`
  differentiated termwise with `hasDerivAt_tsum_of_isPreconnected`).
- `integral_dAlembert_pair_mul_exp_half`: massless pole law `∫ (D(s+v)+D(s−v)) e^{s/2} = (2/cos²(1/4)) cosh(v/2)`.
- `integral_chmdPrimeKernel_mul_exp_half`: KG pole law `∫ K_y(s) e^{s/2} ds = chmdPoleWave y`;
  `integral_chmdPrimeKernel_sub_mul_exp_half`: `∫ K_y(s−u) e^{s/2} = e^{u/2} chmdPoleWave y`.
- `chmdPrimeWave_eq_chmdPoleWave_add_transport`: `chmdPrimeWave = chmdPoleWave + chebyshevDiscrepancyTransport − poleShadow`,
  `|poleShadow| ≤ 8/π` (`abs_poleShadow_le`), `|K_y| ≤ 4/π` (`abs_chmdPrimeKernel_le`).
- `riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow` / `_bddAbove`.

Meaning: the Klein–Gordon propagation of the PNT density `e^{s/2} ds` is exactly the ζ-pole wave; after
this exact transport the prime wave contains no `e^{y/2}` object, and the light-cone route's one-sided
bound is a statement about the exact √-weighted Chebyshev discrepancy measure against a bounded kernel
(Wall 1 in KG coordinates). Open next step: IBP to `−∫ ∂_sK_y Δ(s) ds` with `Δ(s) = Σ_{n≤e^s}Λ(n)/√n − 2e^{s/2}`
(needs `D'` decay bounds and `K_y(s) → 0`).

Lean notes: clamp the Bessel parameter (`clampUnit`) for Fubini over the product with a restricted
measure; give `(f := …)` to `norm_integral_le_of_norm_le`; `(μ := volume)` for `integral_sub_right_eq_self`.
