# Explicit height for the Weyl heat horizon

- **ID:** explicit-weyl-heat-height
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A19; `docs/reports/review-1311/route-obstacles.md` S4 (A19).
- **Statement:** For `0 < ε ≤ 1` and `0 < t ≤ 1/8`, every zero `z` of `H_t` with `|Re z| ≥ exp(10²⁰/ε⁴)` and `|Re z| ≥ 2π exp((3/2+ε)/t)` is real and simple. For `ε > 1` the height is `exp(10²⁰)`.

## Lean
`ZeroConfigurationGeometry/HeatScaleRepulsion/TheExplicitHeightOfTheWeylHorizon.lean`:
`riemannHeat_zeros_real_simple_weyl_explicit`, `riemannHeat_zeros_real_simple_weyl_explicit_of_pos`.
Parametric forms of the existing proof: `norm_riemannZeta_le_subconvex_of_segment`
(`RHTower/ZetaSubconvexStripBound.lean`), `norm_xiLine_le_strip_weyl_of_bounds`,
`riemannHeat_zeros_real_simple_weyl_of_params` (`RHTower/KiKimLeeWeylHorizon.lean`).

## Proof

The horizon `riemannHeat_zeros_real_simple_weyl` has three non-explicit constants.

1. **Segment constant** (`norm_zetaEntire_half_segment_le`). The Phragmén–Lindelöf constant of the
   interpolated Weyl bound needs `‖(s−1)ζ(s)‖ ≤ K₀` on `s = ½+iy`, `|y| ≤ 8`. The eta series gives
   `‖(1−2^{1−s})ζ(s)‖ ≤ ‖s‖/Re s` and `‖1−2^{1−s}‖ ≥ √2−1 ≥ 2/5`, so `‖ζ(s)‖ ≤ 5‖s‖` on the critical
   line and `K₀ = 362`. Then `‖ζ(σ+it)‖ ≤ (16800e^{1/4}/η) t^{ρ(1+η−σ)}` on `½ ≤ σ ≤ 1+η`, `t ≥ 8`
   (`norm_riemannZeta_le_subconvex_explicit`).
2. **Euler anchor** (`one_third_le_norm_riemannZeta_of_three_halves_le_re`). `‖ζ(s)‖ ≥ 1/3` on
   `Re s ≥ 3/2` from `ζ(s)·Σμ(n)n^{−s} = 1` and `Σ n^{−3/2} ≤ 3`. Strip constant
   `K(η) = 100800 e⁶e^{1/4}/η` (`weylStripConstant`, `norm_xiLine_le_strip_weyl_explicit`).
3. **Error threshold** (`weyl_errors_small`). With `A = 1/η+3` and `3c₀/4 − 1 − η ≥ 1/8`, for
   `α ≥ max(50000A²e⁸, 3600πK/(m/80)³)` each of the six decaying terms is `≤ 1/25`:
   the tails by `e^{E} ≤ 1/N` for `E ≤ 1−N`; the model error by `√(20/α) ≤ 1/(50Ae⁴)`; the strip term by
   `e^{−x} ≤ 6/x³`; the far and boundary terms by `α ≤ e^α` and `α² ≥ 450000α`.

Parameters for `0 < ε ≤ 1`: `c₀ = 3/2+ε`, `η = ε/36`, `m = 2ε/3` (margin
`(2−2ρ)c − 2(1+η) ≥ 2ε/3` and `2ρc ≥ 1` for `c ≥ c₀`, `ρ = (1/6+η)/(1/2+η)`). Then `K ≤ 2·10⁹/ε`, both
slope conditions hold at `α₀ = 4·10¹⁹/ε⁴`, and the height `2πe^{2α₀}` is at most `exp(10²⁰/ε⁴)`.

## Log
- 2026-11-13 — formalized.
