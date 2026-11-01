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

This is the isolated-pair RVM model, with `K=exp(2a)`. It asserts no atomic
finite-horizon identification for the actual zeta configuration.

## Gates

- [x] Dependency-closed paper proof.
- [ ] Exact Lean theorem, direct compilation, standard-axiom audit, umbrella import.
