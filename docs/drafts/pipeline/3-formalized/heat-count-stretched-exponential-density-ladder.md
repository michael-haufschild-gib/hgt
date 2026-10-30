# The stretched-exponential rung of the heat-count ladder

- **ID:** heat-count-stretched-exponential-density-ladder
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `review-3010/obstacles-summary.md`, A8
- **Statement:** `N(t)≤exp(A t^(−α))` near zero implies
  `#F≤C log X exp(K(log X)^(4α))` for every finite multiplicity-exact Ξ-zero
  set in `[X,2X]` of depth at least `δ>0`. If `α<1/4`, then `#F≤X^ε`
  eventually for every `ε>0`.

## Proof

Fix `0<δ≤1/2`. The proved persistence/counting theorem supplies `C>0`
and a horizon such that `#F≤C log X N(t)` for
`0<t≤δ²/(C log⁴ X)`. Set `t=δ²/(C log⁴ X)`.
For any `t₀>0`, this time lies in `(0,t₀]` once
`log X≥max(1,δ²/(Ct₀))`: here `log⁴ X≥log X`.

The exact real-power identity

`t^(−α)=(C/δ²)^α (log X)^(4α)`

therefore gives the first bound with `K=A(C/δ²)^α`.
Put `b=4α<1`. Since `y^(b−1)→0`, eventually
`K(log X)^b≤(ε/2)log X`. Also `C log X≤X^(ε/2)` eventually.
Exponentiating the first inequality and multiplying proves `#F≤X^ε`.
Both bounds are uniform over all finite zero-copy sets in the window.

The heat-count envelope is the antecedent of this implication, not an asserted
bound for the actual heat count. No new analytic estimate is assumed.

## Existing rungs

`finite_nonreal_zeros_iff_exists_nonrealZeroCount_le` gives the bounded-count
equivalence. `polylog_deep_density_of_polynomial_nonrealZeroCount` gives the
polynomial rung with exponent `4a+1`. The new implication completes the
stretched-exponential row without asserting any improvement of `N(t)` itself.

## Verification

`RHTower/Heat/TheHeatCountGrowthLadder.lean` passes the direct Lean check.
`exists_deep_window_bound_at_logarithmic_heat`,
`stretchedExponential_deep_density_of_nonrealZeroCount`,
`subpower_deep_density_of_subcritical_nonrealZeroCount`, and the existing polynomial
rung depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The new module is imported by `RHTower.lean`.
