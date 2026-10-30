# The heat detection rate is quadratic in the depth

- **ID:** heat-detect-quadratic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #1; `reboot-final.md` §4.B, WP-B3, WP-A3
- **Statement:** For `t ≥ e^{1600}`, every off-line zero `½ + δ + it` and every `κ ∈ (0, δ²/200]`, some
  heated slice coefficient `T_n(κ/log t, 0, t)` has negative real part.

## Lean
Module `RHTower/Heat/TheHeatDetectionRateIsQuadraticInTheDepth.lean` (namespace `RHTower`):
- `hasSum_le_rpow_mul_rpow` — log-convexity of nonnegative power series;
- `heatedSliceReal_le_pow_mul_half` — local degree: `H(R) ≤ D (2R/δ)^M H(δ/2)` on `[δ/2, 3/2]`;
- `heatedSliceReal_le_relative_growth` — `H(R) ≤ D H(δ/2) e^{(A + 2M/(eδ))R + 2R²}`, all `R > 0`;
- `re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic` — the statement;
- `DeBruijn.sq_re_sub_half_lt_of_heat_rate_pos` — every-height positivity at rate `κ` above
  `max(t₀, e^{1600})` forces `(Re ρ − ½)² < 200κ`;
- `DeBruijn.le_wdHeatThreshold_of_offLine_zero_quadratic`,
  `DeBruijn.le_newmanConstant_of_offLine_zero_quadratic` — `Λ ≥ (Re ρ − ½)²/(200 log Im ρ)` for every
  zero with `Re ρ > ½`, `Im ρ ≥ e^{1600}`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
Let `a_n = Re T_n(λ, 0, t) ≥ 0`, `H(y) = Σ a_n yⁿ` (the Gaussian average of `f_t`), `F = f_t(3/2)`,
`A = log t + K₀`, `M = ⌈(3A + 20 + 2A²λ)/log 2⌉`, `D = 4√2 e^{3A/2 + 9/2 + 2A²λ}`.

1. **Log-convexity.** For `0 ≤ θ ≤ 1`, weighted AM–GM on `u_n = a_n r₁ⁿ/H(r₁)`, `v_n = a_n r₂ⁿ/H(r₂)`
   gives `a_n(r₁^{1−θ}r₂^θ)ⁿ ≤ H(r₁)^{1−θ}H(r₂)^θ((1−θ)u_n + θv_n)`; summing,
   `H(r₁^{1−θ}r₂^θ) ≤ H(r₁)^{1−θ}H(r₂)^θ`.
2. **Endpoints.** Three radii: `(δ/3)^M F/4 ≤ H(δ/2)`; envelope: `H(3/2) ≤ √2 F e^{3A/2+9/2+2A²λ}`.
   Hence `H(3/2) ≤ D(3/δ)^M H(δ/2)`.
3. **Local degree.** For `δ/2 ≤ R ≤ 3/2` put `θ = log(2R/δ)/log(3/δ) ∈ [0, 1]`; then
   `R = (δ/2)^{1−θ}(3/2)^θ` and `(3/δ)^θ = 2R/δ`, so step 1 and `D^θ ≤ D` give
   `H(R) ≤ D(2R/δ)^M H(δ/2)`.
4. **Relative growth.** `x ≤ e^{x/e}` gives `(2R/δ)^M ≤ e^{2MR/(eδ)}`. For `R ≥ 3/2` the envelope with
   `F ≤ 4(3/δ)^M H(δ/2)` and `3/δ ≤ 2R/δ` gives the same bound; for `R < δ/2`, `H(R) ≤ H(δ/2)`. So
   `H(R) ≤ D H(δ/2) e^{αR + 2R²}`, `α = A + 2M/(eδ)`, for all `R > 0`.
5. **Hermite tail** (`re_xiSliceHeatTransfer_neg_of_relative_growth`): with `f_t(δ) = 0` this is
   impossible once `log(6D) + 2αδ + 16δ² + 32α²λ < (δ²/(4λ)) log(3/2)`. With `λ = κ/L`, `L = log t ≥ 1600`,
   `200κ ≤ δ²`: `A ≤ 1.01L`, `A²λ ≤ L/700`, `M ≤ 4.43L`, `log(6D) ≤ 8.5 + 3A/2 + 2A²λ`,
   `2αδ ≤ A + 4M/2.7`, `32α²λ ≤ 64A²λ + 64q²λ` with `q = 2M/(eδ)` and `q²λ ≤ 0.054L`. The left side is
   `≤ 12.5 + 12.7L`, the right side `≥ 50L/3` (`quadraticRate_numerics`).

## What it changes
- The corpus rate `δ²/(200(log(3/δ)+1))` loses `log(3/δ)` by comparing `H(δ/2)` with the Euler value
  `F` at radius `3/2`. Log-convexity moves the deficit at `δ/2` to every radius `R`, with loss
  `(2R/δ)^M` depending on `R/δ` only. The detection rate is now uniform in `δ`.
- The remaining `δ²` (versus the linear rate under regular growth) is exactly the local degree
  `M ≍ log t` of `H` at radius `≍ δ`: the cluster loss. Head repair at heat `32R²/N(t,R)`
  (`ArithmeticLocalDivisorGeometry.coeffNonneg_heat_localDivisorPolynomial_radiusHead`) has the same
  shape `δ²/N` with `N ≍ log t` retained copies, so the order `δ²` is the natural cluster scale.

## Log
- 2026-10-30 — created; paper proof; formalized.
