# Near Gamma and downward cancellation have polynomial growth

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

For `c≥1`, `c/N≤1/3`, each cancelled near-pair coefficient has size
at most `E_m c`: the exact Mangoldt divisor identity removes `log j`,
leaving a bounded archimedean remainder, `log(N/j)−log c`, and the
bounded Ramanujan divisor jet. Small-width geometry bounds `N/j` by
`2e²c`, while `log c≤c`. The near-row squared mass is therefore
`O(c⁵)` by the polynomial geometry estimate.

Exterior products lie in the exact strip `[N+1,N+ceil(ec)]`; only rows
within `ceil(ec)` of the horizon receive them. Their full signed
Mangoldt divisor mass is at most `ϕ(m)log ℓ`, and `log ℓ/√ℓ≤2`.
Consequently the actual exterior squared mass is at most
`(ceil(ec)+1)(2ϕ(m)ceil(ec))²=O(c³)`.
The normalized full cancellation thus has squared norm `O(c⁵/log N)`.
Near-center entries have size `O(c)`, giving the same fifth-power bound.

## Lean status

`NearGammaDownwardCancellationHasPolynomialGrowth.lean` proves the
coefficient, interior, exterior, full-cancellation and near-center bounds.
Final direct Lean audit passed without warnings; all five axiom audits
contain only `propext`, `Classical.choice`, `Quot.sound`. No separate count.
