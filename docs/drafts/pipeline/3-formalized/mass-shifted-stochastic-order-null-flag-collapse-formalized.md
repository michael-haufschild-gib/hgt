# Mass-shifted stochastic-order null-flag collapse — formalized closure

- **ID:** `mass-shifted-stochastic-order-null-flag-collapse-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./mass-shifted-stochastic-order-null-flag-collapse.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio` (umbrella `GaloisForLFunctions.HTGeometry`)
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryStochasticOrderNoGo`
  (umbrella `GaloisForLFunctions.RHTower`)
- `GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass` (Conjecture 32 classification)

## Formal theorem chain

1. `HTGeometry.integral_monotoneLikelihoodKernel_eq_two_mul_gap` — equation `(1)`: for integrable
   `f, h` and integrable `g·f, g·h` on an s-finite measure space,
   `∫∫ (g(y)−g(x))(h(x)f(y)−h(y)f(x)) = 2((∫gf)(∫h) − (∫gh)(∫f))`.
2. `HTGeometry.monotoneLikelihoodKernel_ae_eq_zero_of_equal_mass_moment` — equation `(2)`: equal
   mass and equal `g`-moment together with a.e. kernel nonnegativity force the kernel to vanish
   almost everywhere.  This is the FAIL 1 saturation.
3. `HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel` — the division-free order
   consequence that the saturation collapses.
4. `RHTower.squaredFactorialCarrierNoGoAdaptiveTest_not_monotoneOn` and
   `…_not_antitoneOn` — FAIL 2: the adaptive observable `t²P♯(t) = t²(t−9)/36` is neither
   monotone nor antitone on `[0,∞)`, witnessed by the exact values at `0, 3, 6, 9`.
5. `RHTower.squaredFactorialCarriers_not_upperTailComparable` — FAIL 3: the two exact common-face
   carriers `μ₊ = (48/49)δ_{3/4} + (1/49)δ₁₃` and `μ₋ = (12/13)δ_{1/2} + (1/13)δ₇` have crossing
   strict upper tails at thresholds `5/8` and `1`, so neither first-order dominates the other.
6. `RHTower.squaredFactorialCarrierStochasticOrderOrientationNoGo` — the closed no-go: identical
   visible size-two moment face, crossing upper tails, an observable outside both monotone cones,
   and opposite exact Krein crossings `37/144` and `−19/72`.
7. `HTGeometry.finiteHankelBoundaryMonicRemainder_eq_firstUnseenMomentError` — the Conjecture 32
   classification: on a positive flat Hankel face the monic boundary remainder *is* the first
   unseen moment error, so a higher-order order hypothesis signing it assumes the open coordinate.

## Verification

- `lake env lean` clean, no warnings, on both modules.
- `#print axioms` on statements 1–7: `propext`, `Classical.choice`, `Quot.sound` only.
- Both umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: standalone novelty and parent-theory audit incomplete
