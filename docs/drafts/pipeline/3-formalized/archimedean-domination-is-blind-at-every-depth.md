# Archimedean domination is blind at every depth

- **ID:** domination-blind-every-depth
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #7; `reboot-final.md` §3.4 (M4)
- **Statement:** For `ξ ≥ e^{100}`, every `a > 0` with
  `horizonExponent(e^{2a}) + 2S_{½}(a) < log(1 + πξ/4)` (the domination range,
  `S_δ(a) = sinh(2δa)/(2δ) − a`), and every `δ ∈ (0, ½]`, the isolated off-line pair of depth `δ` at
  height `ξ` in an on-line background of density `L = (1/2π) log(ξ/2π)` has Hodge defect `0` at
  aperture `a`.

## Lean
`ArithmeticCastelnuovoSeveri/ArchimedeanDominationIsBlindAtEveryDepth.lean`:
`hodgeDefectAt_isolatedPair_eq_zero_of_dominance`, `sinh_mul_le_mul_sinh`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Paper proof
The isolated pair is invisible at aperture `a ≤ L/2` iff `sinh(2δa)/δ ≤ 2L + 2a`
(`hodgeDefectAt_isolatedPair`). Since `sinh(θx) ≤ θ sinh x` for `θ ∈ [0, 1]` (odd power series),
`sinh(2δa)/δ ≤ 2 sinh a ≤ e^a`. Domination gives `68e^a < log(1 + πξ/4) ≤ log ξ`, while
`L ≥ log ξ/(4π)` for `ξ ≥ e^{100}`; so `e^a ≤ 2L`, and `a ≤ e^a ≤ log ξ/68 ≤ L/2`.

## What it changes
The domination proof pays exactly the pair energy `S_{½}` of the boundary depth `½`. Everything it
certifies at height `ξ` is satisfied by a configuration with an off-line pair of any depth at that
height: bounded-scale positivity carries no information on depths below `½`. The visible range of the
isolated pair starts at `S_δ(a) > L`, i.e. aperture `≈ (1/(2δ)) log(4δL)`, which exceeds the domination
range `a ≈ log log ξ − 4.2` by the factor `1/(2δ)`.

## Log
- 2026-10-31 — created; proved; formalized.
