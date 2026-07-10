# The window threshold is sharp: coverage and obstruction meet at ‖b‖ = 2+√2

- **ID:** window-threshold-sharp
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Source:** two-sided capstone of the window program; pairs `u0_phiB_independence` (coverage)
  with `U0WindowObstruction.filledJulia_meets_unit_disk` at the interval endpoint.
- **Statement:** (i) For EVERY `‖b‖ > 2+√2`, `u₀` and the Böttcher window branch `phiB b` are
  algebraically independent over `ℂ(z)` in the germ field of the window annulus.  (ii) There is
  a parameter of modulus EXACTLY `2+√2` — `b = −(2+√2)` — whose filled Julia set meets the
  closed unit disk, so the window route is void there.  The uniform threshold of the window
  method is exactly `2+√2`.

## Goal

Upgrades the window capstone from a sufficient condition to a provably optimal one: the constant
is not an artifact of the estimates but the modulus where the first-step clearance
`‖b‖ − 1 − xStar ‖b‖` vanishes AND where the negative-real obstruction interval `[−2−√2, −2]`
ends.  The obstruction witness at the endpoint is `x₀ = 1` — sitting exactly ON the natural
boundary circle of `u₀` — with finite orbit `1 ↦ −(1+√2) ↦ 1+√2 ↦ 1+√2`.  Coverage and
impossibility, machine-checked at the same constant.

## Lean surface

- `U0WindowSharpness.window_threshold_sharp` — the conjunction.
- Card: `FullyProvenNewTargets.window_threshold_sharp_card` (`WindowThresholdSharpTarget`).
- Files: `formal/GaloisForLFunctions/U0/U0WindowSharpness.lean` (pair),
  `U0MonotoneEscape.lean` (linear escape above the fixed point `xStar`),
  `U0LogBoundGeneral.lean` (general-radius log estimate).

## Proof shape

Coverage: the sharp pass — far field `{‖w‖ > xStar ‖b‖}` (exactly invariant by the fixed-point
identity `xStar² = xStar + B`, uniform series ratio `rMax = B/(B+xStar) < 1`), b-dependent
window disk `rB b = min(21/20, √(1 + clearance/2))`, one-step entry past the fixed point, then
linear monotone escape (`g^[n] t ≥ t + n(t − xStar)`) to exceed the abstract Böttcher far
bound — no rate constant, which is what survives at the degenerating threshold.  Obstruction:
the explicit finite orbit of the window-obstruction interval at its endpoint.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proof carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — proven and registered (`window_threshold_sharp_card`); dichotomy companion at
  fixed modulus in `window-dichotomy-modulus-three`.
- 2026-07-02 — geometric upgrade: `U0CurveSectors.viable_of_gt_sharp` shows the closed unit
  disk escapes for EVERY direction above 2+√2 (not only that the window capstone holds), and
  `rho_pi_pinned` makes the threshold the exact maximum of the critical curve ρ(arg b).
