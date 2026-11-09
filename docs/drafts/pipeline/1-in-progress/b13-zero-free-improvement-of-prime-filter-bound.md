# Zero-free-region improvement of the arithmetic filter bound

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

For fixed `σ<1`, `a>0`, finite `F`, and degree `d` of the divisor filter,
prove independently of a finite-layer assumption that, eventually in `t`,

`|A_{P_h}(t)| ≤ C h^d (1+t)^N`
`  · exp(a(1−σ)t/2 − b t/log(2t))`, uniformly for `0≤h≤1`,

with `b>0`. This would include the previously missing contraction boundary
`dκ=a(1−σ)/2`: the raw prime filter would still tend to zero there.
It would not close the fixed rate gap to an exceptional zero `β<1`.

## Local contour argument

Use the proved complete Euler integral, initially on `Re z=1+ε` with
`ε>0` chosen small relative to `1/a`. Truncate its Mellin height at
`|v|≤t/2`. Throughout this rectangle the zeta height lies in `[t/2,3t/2]`,
so the pole is outside. Shift the middle segment to
`Re z=1−η/log(2t)` inside the known zero-free region.

The logarithmic derivative is `O(log²t)` on this rectangle. The shifted
Gaussian kernel saves `exp(−aη t/(2log(2t)))`. Each filter factor still
contributes `h` uniformly across the rectangle. Horizontal edges and the
unshifted Euler tails have Gaussian decay at `|v|≥t/2`; choosing `ε`
small makes their exponential rate strictly lower than `a(1−σ)/2`.
No pole regularization or zero subtraction is required for this local shift.

## Dependencies and status

- Proved integral and coarse upper bound: `EulerBoundsForDampingFilters.lean`.
- Actual zero-free and logarithmic-derivative inputs:
  `RHTower/Sieve/ZetaLogDerivRegionBound.lean`.
- Stronger candidate: `ZetaLittlewoodArbitraryConstant.lean` may permit
  every fixed `b>0`, after changing the constants and starting height.

Uniform strip filter bounds, truncated contour estimates and the final
diagonal inequality remain to be formalized. No improved bound claimed yet.
