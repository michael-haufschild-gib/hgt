# Completed conductor quasimodes are uniform on bounded overlap

- **ID:** completed-conductor-quasimodes-are-uniform-on-bounded-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For every nonzero compact `C²` unit profile, fixed positive conductor `m`,
and `K≥1`, the literal complete residual
`‖W_N(c)r̂_m−E_m(c)r̂_m‖` tends to zero uniformly for `1≤c≤K`.

## Proof [PROVED HERE]

Use the exact complete residual identity. Its eight terms are the ratio
prime residual, self remainder, charge-preserving center residual,
separated cross error, two-pole error, full near-Gamma/downward difference,
near center block, and upward shell defect. The ratio prime residual is
independent of `c`; each other source has the common bounded-overlap norm
estimate proved on its supporting card. The two unnormalized conductor
source errors carry the fixed factor `1/√ϕ(m)`. The triangle inequality
therefore gives a single smallness horizon for their finite sum.
The tilted unit spline discharges all profile conditions explicitly.

## Lean status

`CriticalArithmeticCorrelationTheory/CompletedConductorQuasimodesAreUniformOnBoundedOverlap.lean`
proves the general residual law and its explicit tilted-spline specialization.
Final direct Lean check passed; both axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella import is wired.
Supporting quasimode law; no separate contribution count.
