# Zero-free-region improvement of the arithmetic filter bound

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

For fixed `σ<1`, `a>0`, finite `F`, and degree `d` of the divisor filter,
independently of any finite-layer assumption, eventually in `t`,

`|A_{P_h}(t)| ≤ C h^d (1+t)^(d+3)`
`  · exp(a(1−σ)t/2 − b t/log(2t))`, uniformly for `0≤h≤1`,

for every prescribed `b>0`, with constants depending on `b`. This includes the contraction boundary
`dκ=a(1−σ)/2`: the raw prime filter tends to zero there.
It does not close the fixed rate gap to an exceptional zero `β<1`.

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

Concretely, take `ε=min(1/16,1/(16a))`, `η=2b/a`, and use the
Littlewood arbitrary-constant zero-free and derivative bounds. The fixed
kernel strip is `[(1−σ)/2,9/8−σ]`; eventually it contains the contour.
After polynomial weights are absorbed, the Gamma envelope is `exp(−|v|/2)`.
Truncation at `t/2` then costs `exp(−t/8)`, and each horizontal edge
costs `exp(−t/4)`. Since `aε/2≤1/32`, both errors are absorbed by
`exp(a(1−σ)t/2−bt/log(2t))` eventually. The left segment has precisely
this exponent; its length and `log²(2t)` cost only three polynomial powers.

## Dependencies and status

- Proved integral and coarse upper bound: `EulerBoundsForDampingFilters.lean`.
- Actual arbitrary-width inputs: `RHTower/Sieve/ZetaLittlewoodArbitraryConstant.lean`.
  Both zero-freeness and the logarithmic-derivative bound have audited transitive
  axioms `propext`, `Classical.choice`, `Quot.sound`.

The uniform strip filter bound is kernel-checked in `EulerBoundsForDampingFilters.lean`.
`ExceptionalLayerTheory/ZeroFreeBoundsForDampingFilters.lean` passes its direct source
audit without warnings. Its six audited declarations have exactly the same three
standard axioms. Capstones:

- `exists_primeDampingFilter_local_shift_bound`: shifted contribution plus exponential tail.
- `exists_primeDampingFilter_zero_free_bound`: the stated bound for every `b>0`.
- `tendsto_primeDampingFilter_zero_of_critical_contraction`: decay including equality.

## Critical contraction

For every fixed `n` and `b>0`, `(1+t)^n exp(−bt/log(2t))→0`.
Indeed put `u=log(2t)`. The known limit `u²exp(−u)→0` implies
`(n+1)u²≤bt` eventually. Since `1+t≤2t=exp(u)`, the expression is
at most `exp(nu−bt/u)≤exp(−u)→0`.

Substituting `h=exp(−κt)` therefore proves decay whenever
`dκ≥a(1−σ)/2`, including equality. The exceptional-layer lower rate
remains separated by `a(1−β)/2+π/4`; no contradiction to B13 follows.

## Novelty boundary

The zero-free region, Mellin inversion and Gamma decay are existing inputs.
The contribution is their uniform estimate for the complete prime-only divisor
filter, retaining every spacing factor through the contour shift, and the
resulting unconditional critical-contraction decay.
