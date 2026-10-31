# A signed Weyl bump attains the size-only method floor 27/40

- **ID:** signed-weyl-bump-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #15; `reboot-final.md` §7, WP-B1
- **Statement:** For `0 ≤ s ≤ 1`, `A = e^{θL}`, `g(x) = cosh(Lx) − A cosh(sLx)` satisfies the two-profile
  size bound (first profile `t^{−(p + s(½ − |a|))}`, any `c₂ ≤ 1`, `θ ≤ ½ + 2η − p − s/2`) and the
  Euler-point bound `g^{(n)}(x₀) ≥ g(x₀)Lⁿ/4`. Its Gaussian heat at `κ/L` has all Taylor coefficients
  `≥ 0` iff `κ(1 − s²) ≥ 2θ`; below, the `x²` coefficient is negative for large `L`. At
  `p = s = 1/9`, `θ = 1/3`: threshold `27/40`. `g(0) < 0`.

## Lean
Module `RHTower/Heat/ASignedWeylBumpAttainsTheMethodFloor.lean` (namespace `RHTower.DeBruijn`):
`signedBumpModel`, `signedBumpModel_zero_lt_zero`, `signedBumpModelC`, `norm_cosh_combination_le`,
`norm_signedBumpModelC_le`, `norm_signedBumpModelC_le_profiles`, `iteratedDeriv_signedBumpModel`,
`signedBumpModel_mul_pow_le_iteratedDeriv`, `signedBumpHeat`, `signedBumpHeat_eq`,
`signedBumpHeatCoeff`, `hasSum_signedBumpHeatCoeff`, `signedBumpHeatCoeff_nonneg`,
`signedBumpHeatCoeff_two_neg`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
`‖cosh(μ(a + ic))‖ ≤ cosh(μa) ≤ e^{|μa|}`. The background is placed under the second profile as in
the positive bump; the bump `Ae^{sL|a|}` is `≤ 4g(½+2η)e^{−L(p + s(½−|a|))}` because
`θ + s|a| ≤ ½ + 2η − p − s(½ − |a|)`, and `g(½+2η) ≥ e^{L(½+2η)}/4` by the hypothesis on `A`. Euler
points: the subtracted derivative is `≤ A(sL)ⁿe^{sLx₀} ≤ ALⁿe^{sLx₀} ≤ Lⁿe^{Lx₀}/4`. Heat: four Gaussian
moment generating functions. Threshold: the `x^{2m}` coefficient has the sign of
`e^{κL/2}L^{2m} − e^{θL + s²κL/2}(sL)^{2m}`; for `κ(1 − s²) ≥ 2θ` the exponent and `s ≤ 1` give `≥ 0`;
for `κ(1 − s²) < 2θ`, at `m = 1`, `e^{(θ − κ(1−s²)/2)L}s² > 1` once `L > 1/(εs²)`.

## What it changes (WP-B1, §7)
The corpus low-order repair (`exists_xiSliceHeatTransfer_pos_low_order_interior`) needs exactly the gap
`κ(1 − s²) > 2θ` for its first profile, `κ > 27/40`. The model shows that this gap is necessary for
any argument from the same inputs: `27/40` is the genuine floor of size-only repair without the
sign of the slice on the real axis. With the sign (`S(t, x) = |ξ(½ + x + it)|² ≥ 0`), the positive
bump of `a-weyl-bump-breaks-size-only-repair.md` gives the floor `≥ 2/3`. The interval `[2/3, 27/40]`
is exactly what real-axis positivity can buy. Mechanism: the slope `s` of the size profile enters
through the Gaussian tilt `e^{s²κL/2}`. A nonnegative function cannot carry a negative `cosh(sLx)`
component of centre size, so with positivity only the flat part of the profile at the centre counts.

## Log
- 2026-10-31 — created; proved; formalized.
