# Completed conductor quasimodes have polynomial error

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

Each fixed positive conductor has an actual complete Weil residual
squared norm at most `K_m c¹⁰/√(log N)`, simultaneously for `c≥1` and
`4(e+3)²c²≤N`, beyond one horizon independent of overlap.

Use the exact eight-term decomposition. The normalized prime-ratio
residual is `O(1/log N)` by the horizon-uniform arithmetic budget.
The self term is `O(c²/N²)`; center, pole and cross terms are
`O((c²+c⁴)/log N)`. Full near-Gamma/downward cancellation and near
center cost `O(c⁵/log N)`. The actual upward residual costs
`O(c¹⁰/√(log N))`. Conductor normalization introduces only a fixed
factor. The horizon condition implies `c/N≤1/3` and every required
small-width condition. Since `c≥1`, `log N≥1`, and
`√(log N)≤N²`, each squared term fits the claimed common bound.
The squared norm of the eight-term sum is at most eight times their
squared-norm sum. The explicit tilted spline discharges every profile
regularity, support and positive-mass premise.

## Lean status

Formalization follows directly. Supporting full actual quasimode bound;
no separate contribution count.
