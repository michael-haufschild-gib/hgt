# An off-line pair survives the heat flow up to heat δ/L

- **ID:** pair-survives-heat-depth
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #23
- **Statement:** For `F(z) = (z² + δ²) cos(Lz/2)` and `H_t(z) = ∫ g_t(u) F(z + iu) du` (Gaussian of
  variance `2t`): `H_t(iy)` is real, equal to
  `(e^{tL²/4}/2)(e^{Ly/2}(δ² − 2t − (y + Lt)²) + e^{−Ly/2}(δ² − 2t − (y − Lt)²))`; if `t > 0`, `L ≥ 0`,
  `0 < δ ≤ 2` and `(Lt)² + 2t < δ²`, then `H_t(iy) = 0` for some `y > 0`.
  `‖F(x + iy)‖ ≤ (x² + y² + δ²) cosh(Ly/2)`.

## Lean
Module `RHTower/Heat/AnOffLinePairSurvivesTheHeatFlowToItsDepth.lean` (namespace `RHTower.DeBruijn`):
`pairModel`, `pairModelHeat`, `norm_pairModel_le`, `forwardPolyHeat_C_sub_X_sq`,
`pairModelHeat_mul_I`, `exists_pos_pairModelHeat_mul_I_eq_zero`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
On `z = iy`, `F(i(y + u)) = (δ² − (y + u)²) cosh(L(y + u)/2)` is real. The tilted Gaussian average
`∫ g_t(u) e^{±Lu/2} p(y + u) du = e^{tL²/4} (e^{tD²}p)(y ± Lt)` with `e^{tD²}(δ² − X²) = δ² − 2t − X²`
gives the closed form. At `y = 0` it is `e^{tL²/4}(δ² − 2t − (Lt)²) > 0`. At `y = δ + 1` the first
bracket is `≤ −(2δ + 1)`, the second `≤ δ²`, and `δ² < 2δ + 1` for `δ ≤ 2`, so it is negative. The
intermediate value theorem gives a zero `y ∈ (0, δ + 1)`.

## What it changes (WD, B)
In `κ = tL` the pair stays off the real line while `κ² + 2κ/L < δ²`, i.e. up to `κ → δ`. With `δ` up
to `½`, the model has Lindelöf-size slices (no centre bump), so size bounds at the Lindelöf level
cannot place the de Bruijn reality horizon below `κ = ½`. That is the value of the corpus method with
`E ≡ 0` (`KiKimLeeTwoThirdsHorizon`, `(c − w)² > 4cE(w)` on `[0, ½]`). With the Weyl exponent the bump
of `a-weyl-bump-keeps-a-nonreal-heat-zero.md` raises the floor to `4μ(½) = 2/3`, and the corpus
reaches it. So the method is sharp at both levels. A single isolated pair at depth `δ` in a regular
background survives to `κ = δ` (de Bruijn) and needs slice heat `δ/2` (cosh model); a dense row at
depth `d` survives to `2d`.

## Log
- 2026-10-31 — created; proved; formalized.
