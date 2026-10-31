# A Weyl bump keeps a nonreal zero of the de Bruijn flow below the horizon 4θ

- **ID:** weyl-bump-debruijn-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #22; frontier map WD
- **Statement:** `F(z) = cos(Lz/2) + A e^{−z²/L²} = ∫ cos(zu) dμ(u)` with `μ ≥ 0`; its deformation
  `H_t = ∫ e^{tu²} cos(zu) dμ = e^{tL²/4} cos(Lz/2) + A(1 − 4t/L²)^{−1/2} e^{−z²/(L²−4t)}`. For
  `0 < θ ≤ ½`, `0 ≤ κ < 4θ` and all large `L`, `H_{κ/L}` with `A = e^{θL}` has a zero with `Im z > 0`.
  `‖F(x + iy)‖ ≤ cosh(Ly/2) + A e^{y²/L²}`.

## Lean
Module `RHTower/Heat/AWeylBumpKeepsANonrealHeatZero.lean` (namespace `RHTower.DeBruijn`):
`cosBumpModel`, `cosBumpHeat`, `cosBumpHeat_zero`, `gaussKernel_heat_eq`,
`integral_gaussKernel_heat_mul_cos`, `cosBumpHeat_eq_integral`, `norm_sin_sq`, `norm_cos_sq`,
`norm_cos_le_cosh_im`, `sinh_im_le_norm_sin`, `two_div_pi_mul_norm_le_norm_sin`,
`norm_cosBumpModel_le`, `differentiable_cosBumpHeat`, `exists_nonreal_zero_cosBumpHeat_of_cosh`,
`exists_nonreal_zero_cosBumpHeat`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
`E = e^{tL²/4}`, `B = A(1 − 4t/L²)^{−1/2}`, `cosh a = B/E` (IVT; `2 ≤ a ≤ L` once `(θ − κ/4)L ≥ 2`,
`L ≥ 22`). `G(z) = E cos(Lz/2) + B` vanishes at `z* = (2/L)(π + ia)`. On `|z − z*| = 1/L`:
`G = −2E sin u sin w`, `‖w‖ = ¼`, `Im u ≥ a − ¼`; `‖sin w‖² = sin² Re w + sinh² Im w` gives
`‖sin w‖ ≥ 1/(2π)`, `‖sin u‖ ≥ sinh(a − ¼) ≥ e^a/4`, so `‖G‖ ≥ e^a E/(4π)`. And
`‖H_t − G‖ = B‖e^{−z²/(L²−4t)} − 1‖ ≤ 36B/L² ≤ 36Ee^a/L² < e^aE/(4π)` (`L² > 144π`). Rouché gives a
zero of `H_t` in the disc, which lies in `Im z ≥ (2a − 1)/L > 0`. The kernel identity is the complex
Gaussian moment generating function.

## What it changes (WD)
With `A = e^{L/6}` (the centre size Weyl's `μ(½) ≤ 1/6` allows for `Ξ` at height `X = e^L`, against a
cosine of size `1`), the model keeps a nonreal zero at height-scale `X` up to heat `(2/3 − ε)/log X`.
That is exactly the reality horizon of the corpus (`KiKimLeeTwoThirdsHorizon`,
`2π e^{(2/3+ε)/t}`). So the constant `2/3` in `N(t) ≤ C R log R`, `R = 2π e^{(2/3+ε)/t}`, cannot be
lowered by size bounds and positivity of the Fourier kernel alone. This parallels the slice side
(`a-weyl-bump-breaks-size-only-repair.md`, floor `4μ(½)` attained by
`size-only-repair-near-the-weyl-floor.md`). The WD route's subcritical target
(`the-heat-count-ladder-at-inverse-logarithmic-heat.md`: `N(t) ≤ exp(A t^{−a})`, `a < 1`) therefore
needs an input that bounds depths.

## Log
- 2026-10-31 — created; proved; formalized.
