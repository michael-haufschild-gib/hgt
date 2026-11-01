# Critical multiple of one isolated pair in the RVM model

- **ID:** rvm-isolated-pair-critical-multiple
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A3.
- **Statement:** Set `L=log(γ/(2π))/(2π)`, `0<δ≤1/2`, `γ>2π`.
  At `1<K≤exp L`, the degree-`log K/2` Hodge defect is zero exactly when
  `(K^δ−K^(−δ))/(2δ)≤2L+log K`; otherwise it is one.
  If `δL≥16`, its first visible multiple lies in
  `[(4δL)^(1/δ),(6δL+1)^(1/δ)]`.
  For every positive density, the edge equals `exp(min(x/δ,L))`, where
  `x>0` uniquely solves `sinh x−x=2δL`. The defect is zero through this
  multiple and one above it. When `δL≥16`, one has `x<δL`.

## Proof [PROVED HERE]

Substitute `a=log K/2` in `hodgeDefectAt_isolatedPair` and expand `sinh`.
The corpus's RVM invisibility bound applies below
`a₋=log(4δL)/(2δ)`; its visibility bound applies strictly above
`a₊=log(6δL+1)/(2δ)` and below `L/2`.

Write `x=δL≥16`. Since `exp x≥x²/2>6x+1`, one has `a₊<L/2`.
Thus the lower-multiple region lies below the Nyquist aperture.
For any `K>(6δL+1)^(1/δ)`, use aperture `min(log K/2,L/2)`:
it exceeds `a₊`, hence has defect one. Monotonicity of the degree filtration
and the total defect bound one give defect one at `log K/2` as well.
The infimum of visible multiples is therefore bounded by the two displayed
powers; the upper bound follows by approaching the upper power from above.

For the exact transition, `f(x)=sinh x−x` is continuous and strictly increasing
on `[0,∞)`, since `f′(x)=cosh x−1>0` for `x>0`. It vanishes at zero.
For `t=δL≥16`, `exp t>6t+1` and `exp(−t)≤1`, so `f(t)>2t`.
The intermediate value theorem gives a unique root `x∈(0,t)` of
`f(x)=2t`. Below `K=exp L`, the exact visibility inequality is
`f(δlog K)≤2δL`, equivalent to `K≤exp(x/δ)`.
At `K=exp L` the defect is already one, and monotonicity preserves it
for larger `K`. Thus the visible set is exactly `(exp(x/δ),∞)`.

For arbitrary `t>0`, apply the same upper estimate at `max(16,t)` to
obtain the unique positive root. The sub-Nyquist law still gives the
root threshold. The [lattice-null interpolation proof](isolated-pair-visible-immediately-above-nyquist.md)
gives defect one at every aperture strictly above `L/2`, including when
the root lies beyond Nyquist. Hence the threshold is capped at `exp L`.

This is the isolated-pair RVM model, with `K=exp(2a)`. It asserts no atomic
finite-horizon identification for the actual zeta configuration.

## Gates

- [x] Dependency-closed paper proof.
- [ ] Exact Lean theorem, direct compilation, standard-axiom audit, umbrella import.
