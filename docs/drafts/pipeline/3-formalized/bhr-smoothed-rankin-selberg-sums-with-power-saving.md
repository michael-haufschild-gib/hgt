# BHR — smoothed Rankin–Selberg sums with a power saving

- **ID:** bhr-cusp-smoothed-rankin-selberg-power-saving
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** step towards Rankin's bound for the cusp coefficients (power saving in the mean-square law of
  `bhr-the-mean-square-law-of-the-cusp-modes.md`).
- **Statement:** For `g ∈ S(λ)`, `f(m) = |ρ(m)|² + |ρ(−m)|²`, `A = (24/π²)cosh(πt)‖g‖²`, `φ_g = (s−1)L_f(s)` the
  normalized Rankin–Selberg function, and `φ_Δ(u) = G(log u/Δ)/Δ`, `G(y) = e^{−y²/4}/(2√π)`:
  1. `|φ_g(s)| ≤ C(1+|Im s|)^N` on every strip `a ≤ Re s ≤ 5/4`, `a > ½`;
  2. there are `K, N` with, for all `0 < Δ ≤ 1`, `y > 0`:
     `|Σ_m f(m)φ_Δ(my) − A e^{Δ²} y^{−1}e^{−y}| ≤ K Δ^{−(N+1)} y^{−3/4}`.

## Paper proof
1. *Growth.* `c(s) = π^{−s}ζ(2s)2^{s−3}Γ(s/2+ν)Γ(s/2)²Γ(s/2−ν)(2π)^{−s}/2` (the `Γ(s)` of `G` cancels against `ξ(2s)`).
   With `|Γ(σ+iy)|^{−1} ≤ C(1+|y|)e^{π|y|/2}` on `0 ≤ σ ≤ 1`, `|y| ≥ 1` (corpus sharp bound), `|1/ζ(2s)| ≤ 1+1/(2a−1)`
   and `|t/2+t₀| + 2|t/2| + |t/2−t₀| ≤ 2|t| + 2|t₀|`: `|1/c(s)| ≪ (1+|t|)^4 e^{π|t|}` for `|t| ≥ 2|t₀|+2`. With
   `|Λ_g| ≪ (1+|t|)^N e^{−π|t|}` (vertical-decay card) and `φ_g = (s−1)Λ_g/c`: polynomial growth; compact box near the axis.
2. *Weight.* `𝓜φ_Δ(w) = ∫ e^{wx}G(x/Δ)dx/Δ = ∫G(v)e^{(wΔ)v}dv = e^{Δ²w²}`; `φ_Δ` is continuous, Mellin-convergent
   everywhere, and `e^{Δ²w²}` is integrable on vertical lines, so `φ_Δ = 𝓜^{−1}_c e^{Δ²w²}` (Mellin inversion).
3. *Fubini.* For `c > 1`: `S_Δ(y) = Σ f(m)𝓜^{−1}_c(...)(my) = 𝓜^{−1}_c(L_f·e^{Δ²w²})(y)`, since
   `Σ_m ∫ f(m)(my)^{−c}e^{Δ²(c²−t²)} dt < ∞`. Also `y^{−1}e^{−y} = 𝓜^{−1}_cΓ(w−1)(y)` (corpus Gamma inversion at `c−1`).
4. *Regular part.* `Ψ_Δ = dslope(φ_g e^{Δ²w²} − Ae^{Δ²}Γ) 1` (`φ_g(1) = A`); on `Re w > 1`,
   `Ψ_Δ = L_f e^{Δ²w²} − Ae^{Δ²}Γ(w−1)`. `Ψ_Δ` is holomorphic on `Re w > ½`, and on closed substrips
   `|Ψ_Δ| ≪_Δ (1+|t|)^N e^{−π|t|/2}` (using `−Δ²t² ≤ π²/(16Δ²) − π|t|/2`), so it is a regular strip on `(½, 5/4)`.
5. *Shift.* `S_Δ − Ae^{Δ²}y^{−1}e^{−y} = 𝓜^{−1}_{9/8}Ψ_Δ = 𝓜^{−1}_{3/4}Ψ_Δ`, and
   `|𝓜^{−1}_{3/4}Ψ_Δ(y)| ≤ (2π)^{−1}y^{−3/4}∫|Ψ_Δ(¾+it)|dt`.
6. *Explicit Δ.* On `Re w = 3/4`, `|w−1| ≥ ¼`, `|e^{Δ²w²}| ≤ e·e^{−(Δt)²}`, `(1+|t|)^N ≤ Δ^{−N}(1+|Δt|)^N`, so
   `∫|Ψ_Δ| ≤ 4e(CΔ^{−N}∫h(Δt)dt + A∫|Γ(¾+it)|dt) = 4e(CΔ^{−N−1}J + AJ_Γ)`, `h(v) = (1+|v|)^N e^{−v²}` integrable
   (`(1+|v|)^N ≤ N!e^{1+|v|}`, `|v| − v²/2 ≤ ½`).

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheGrowthOfTheRankinSelbergLFunction.lean` (namespace `CuspRSL`) and
`.../TheSmoothedRankinSelbergSums.lean` (namespace `CuspSRS`), wired into `BlackHoleRingdown.lean`, checked with
`lake --old env lean`, no messages. Axioms of `exists_rsPhi_poly`, `norm_smSum_sub_le`: `propext`, `Classical.choice`,
`Quot.sound`.

| Claim | Theorems |
|---|---|
| 1 | `CuspRSL.rsFactor_eq_gamma`, `exists_norm_inv_Gamma_le_lin`, `exists_norm_inv_rsFactor_le`, `exists_rsPhi_poly` |
| 2 weight | `CuspSRS.lgW`, `integrable_exp_mul_lgW`, `mellinConvergent_lgW`, `mellin_lgW`, `continuousAt_lgW`, `norm_exp_sq`, `verticalIntegrable_exp_sq`, `lgW_eq_mellinInv` |
| 2 Fubini | `smSum`, `smSum_eq_mellinInv`, `mellinInv_gamma_sub_one` |
| 2 regular part | `numR`, `regR`, `numR_one`, `regR_eq`, `differentiableAt_regR`, `regR_eq_sub`, `gauss_le_exp`, `mellinRegularStrip_regR` |
| 2 shift, bound | `smSum_sub_eq`, `integrable_poly_gauss`, `exists_line_integral_le`, `norm_smSum_sub_le` |

## Scope
With `X = 1/y`: `Σ_m f(m)φ_Δ(m/X) = A e^{Δ²} X e^{−1/X} + O(Δ^{−N−1}X^{3/4})` — the horocyclic energy of a ringdown
mode, read through a log-Gaussian window of width `Δ` around frequency `X`, matches the equipartition value up to a
power saving that degrades only polynomially in `1/Δ`. This uniformity is what localizes the energy of single
harmonics (Rankin's bound, next card). The exponents `N` are not explicit (they come from the Phragmén–Lindelöf and
Gamma-bound constants).

## Log
- 2026-11-08 — created and formalized.
