# Every finite prime flip has a tilted-spline threshold

- **ID:** every-finite-prime-flip-has-a-tilted-spline-threshold
- **Stage:** 3-formalized
- **Statement:** Every nonempty finite prime set `S` has a positive finite
  resolution threshold for `tiltedUnitSpline`. Below it, the complete flipped
  Weil matrix is eventually positive definite. Above it, a unit Ramanujan
  packet has eventually negative complete Weil form.

## Proof

The existing finite-set theorem uses the periodic trial
`∏_{p∈S}(1−2·1_{p|n}+2·1_{p²|n})`, whose square is one.
Its exact local correlations give negative limiting flipped energy.
Its finite Ramanujan expansion and the decay of conductor energies at large
overlap produce a negative packet. The resolution-bottom theorem then supplies
the positive finite threshold and both strict-side conclusions.

For the fixed tilted spline, `contDiff_tiltedUnitSpline`,
`tiltedUnitSpline_eq_zero`, and `paperFT_tiltedUnitSpline_real_ne_zero`
discharge every profile condition in that theorem. No boundary sign at the
threshold itself is asserted.

## Lean

`RenormalizedArithmeticPotentialTheory/EveryFiniteFlipSetHasAnExactResolutionThreshold.lean`:

- `finiteFlip_resolutionThreshold_spec` — existing general theorem.
- `tiltedUnitSpline_finiteFlip_resolutionThreshold_spec` — explicit-profile specialization.

Direct Lean check passed. Both declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The module is already imported by its umbrella.
