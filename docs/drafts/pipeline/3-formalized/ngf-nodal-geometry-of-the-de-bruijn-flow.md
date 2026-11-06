# Nodal geometry of the de Bruijn flow (NGF)

- **ID:** ngf-programme
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.7.1
- **Statement:** Parabolic tools for route ZCG below the saddle: frequency, zero number, blow-up, local Dyson law, maximum principle for gaps, depth law with its crowd; the central inequality is proved above the horizon and on density-one heights above every `κ/log X`.

## Goal
ZCG's first tools below `½/log X` that do not rest on size. Lean folder `formal/GaloisForLFunctions/NodalGeometryOfTheDeBruijnFlow/`; foundations in its README.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: all modules checked with `lake --old env lean`, no `sorry` or added axiom

## Results and proofs

**Frequency and order.** `∫‖u_{t₀+σ}(x + iy₀)‖²G_σ(x − x₀)dx = Σ(2σ)ⁿ/n! ‖∂ⁿu_{t₀}(z₀)‖²` (`hasSum_fock`), so `N(σ)` is half a mean Taylor degree; tilting an exponential family raises its mean (`frequency_le_frequency`), and the order is at most `2N` (`order_le_two_mul_frequency`).
Above the horizon, `F(σ) ≤ CP²` and `F + D/α² ≥ cP²` (`exists_energy_bounds`); `F(rσ) ≥ r^{2N}F(σ)` (`exp_frequency_mul_lineEnergy_le`) and the exact growth of `P` force `F ≥ c'P²` (`exists_lineEnergy_lower`). Doubling gives `k ≤ (1 + δ)σ log²(X/2π)/2 + K` (`exists_order_le_at_horizon`), so `k ≤ (3300/9991 + ε) log X` at `t₀ = 0` (`exists_mult_le_log`), and linear decay in `τ = t₀ log(X/2π)` (`exists_order_le_of_time`).

**Nodal structure.** Sturm drop law in moving buffered windows (`BufferedWindow.realZeroCount_eq_add_sum_windowCollisionMass`), no caps (`no_real_zero_near_backward_of_even`), Hermite blow-up (`blowup_forward`, `blowup_backward`, `exists_close_zeros_forward`).

**Local Dyson law.** `V = H″/H′` along paths (`hasDerivAt_zero_path`); exact gap law (`gap_rate_eq`); opening at most `8t` outside the Jensen disc (`exists_gap_sq_le_of_paths`, `exists_gap_sq_le_of_collision`). At a mesh pair the compression is below the lattice value (`sum_inv_mul_le_of_sep`), so the rate is at least `16/n − 4Kg²` (`mesh_pair_rate_ge`). Isolated clusters spread at the exact rate `2n²(n − 1)` (`exists_cluster_spread_law`, `exists_cluster_spread_of_collision`): the singular forces cancel in pairs (`sum_mul_sum_inv_eq`).

**Local repulsion.** First touch over packets (`gap_barrier_of_rate`): gaps in a real cylinder stay above the barrier if they do so on the parabolic boundary (`exists_gap_maximum_principle`). With a local count `n` and exterior energy `E` the rate at the touching pair is `16/n − 4(2E + K)g²` (`local_pair_rate_ge`), so the barrier rises at `8/n` up to `1/(n(2E + C log B))` (`exists_gap_maximum_principle_of_count`): the central form away from crowds. With the horizon gaps as top boundary and compactness at low heights: `g_t² ≥ min(c a(t − a), c a², g₁)` for `Λ < a ≤ t ≤ 5a/4` (`exists_uniform_mesh_above_newman`).

**Central inequality.** It implies RH and bounded multiplicities (`riemannHypothesis_of_centralInequality`, `mult_add_one_le_of_centralInequality`). At a zero the amplitude is in the derivative, `|H′| ≫ αP`, and `|H| ≪ P` on discs of radius `1/α`; Cauchy gives `g ≫ 1/α` (`gap_ge_of_disc_bound`, `exists_central_inequality_above_horizon`). The same holds at typical heights for `κ ≤ t log(x/2π) ≤ 1`, with `c` absolute (`exists_densityOne_central_inequality`).

**Depth law.** Reverse saddle with the exact zero energy: `t|V| ≤ cd`, `tR₂(z) ≤ c`, `t log X ≤ cd` give a zero within `d` (`exists_zero_near_of_no_crowd`); `t(R₁ + log X) ≤ cd` suffices (`exists_zero_near_of_potential`); normal density gives `t A log X log(72/d) ≤ cd` (`exists_zero_near_of_normal_density`). Polynomial truth: `(Im z)² < 8nt`, sharp at the Hermite cluster (`im_sq_lt_of_forward_real`, `exists_root_depth_eq`).

**Depth moments.** `E₂` dissipates through collisions (`exists_uniform_heatLocalizedQuarticEnergy_evolution`); nonreal time budget (`exists_sum_nonrealTime_le`), Selberg's fourth moment of the depths (`exists_sum_mult_im_pow_four_le`), rarity (`exists_card_nonrealTime_gt_le`).

**Scales and limits.** Crystal symbol `ξ(2π − ξ)/g²` (`lattice_eigen`). The shifted flow satisfies the same laws and has zeros of unbounded depth (`shiftKernel_superGaussian`, `caloric_shiftKernel`, `exists_deep_zero_shift`).

## Open
The central inequality at `t log X → 0` on density-one heights; control of the local count and energy in a cylinder; compression of non-mesh pairs; the local count around a deep zero; lateral control of nonreal zeros; nonlinear relaxation for the actual source.

## Log
- 2026-11-06 — formalized

## Next target: the central inequality at the critical scale

**Claim.** For every `δ > 0` there is `κ₀` such that for large `T`, outside a set of `X ∈ [T, 2T]` of measure `≤ δT`: for `κ₀/log²X ≤ t ≲ 1/log X`, real zeros near `X` are `≫ 1/log X` apart. So the crystal is formed at `τ = t log²X ≥ κ₀`, the scale of GUE relaxation, on a density-one set.

**Inputs in the corpus.**
- `ZetaLogDerivScaleData t R B`, `exists_volume_not_zetaLogDerivScaleData_le_uniform_level`: exceptional measure `≪ T((log T/B) e^{−κ/120000} + 1/(BR)²)`, `κ = R log T`. Take `BR = κ^{1/4}`: then `B√τ ≍ κ^{−1/4}` and `B/α ≍ κ^{−3/4}`.
- `exists_volume_zetaZeroShadowScaled_le`: heights within `κ′(Re ρ − ½)` of a zero of depth `≥ a`, measure `≪ κ′ T/(a log T)`, all depths at once.
- `two_mul_re_logDeriv_xi_eq_tsum_pair`: `2 Re ξ′/ξ = Σ P(r, a, u)`, `P = (r−a)/((r−a)²+u²) + (r+a)/((r+a)²+u²)`.

**Mechanism.** Put `ZeroKeeping`: every zero of depth `|a| > R₀` has `|u| > 4|a|`.
1. `P = 2r v/(v² + e²)`, `v = r² + u² − a²`, `e = 2|a||u|`. Under `ZeroKeeping`, for `r ≥ √2 R₀`: `v ≥ e`, so `P ≥ 0` and `P/r` is nonincreasing. Hence `Re ξ′/ξ(r₂) ≤ (r₂/r₁) Re ξ′/ξ(r₁)`: the slope at a single scale bounds all larger scales (upper tail, no dyadic chain).
2. `g(q) = (q + c)² + e²` is convex in `q = r²` and `g(R²) ≥ g(0)` when `R² + 2u² ≥ 2a²`: so `|ξ(½ + w + iY)| ≤ |ξ(½ + R + iY)|` for `0 ≤ w ≤ R` (lower strip, tail factor `1`). Proof: finite near set `N`, tail of the pair sum nonnegative, compare `log|ξ|` with `½ Σ_N ψ_q`; zero on the segment by density of generic `Y` and continuity.
3. Half-Gauss with `u = v + 2τβ`: box `[u/3, 5u/4]` inside `[3R/4, 6R]` for `u ∈ [9R/4, 9R/2]`. Relative errors: lower tail `e^{−(2/9)uα}`, upper tail `e^{−uα/32}`, strip `e^{−uα/6 + small}`, top `e^{−c uα}`, model `2B√τ e^{…}`.
4. Abstract gap theorem `gap_ge_of_quadrature_data`, the typical version as a corollary.
5. Exceptional set: shadow at `(R₀, κ′ = 5)` plus scale data at all dyadic `R_j = 2^j R₀ ≤ 1/16` with `BR = κ_j^{1/4}`: total `≪ T(1/κ₀ + κ₀^{−1/2})`.
Modules: `TheSlopeOfXiIsAPoissonSum`, `TheHalfGaussAtTheCriticalScale`, `TheCentralInequalityAtTheCriticalScale`.
