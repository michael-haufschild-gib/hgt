# The tilted-spline conductor floor has polynomial decay

- **ID:** tilted-spline-conductor-floor-has-polynomial-decay
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement

Put `M=∫φ²`, where `φ` is the explicit tilted unit spline, and
`D=1+(3π/4)²`, `C=sinh(1)⁸/(64D⁴)>0`. For every `c≥1`,

`∫_(t>c)|φ̂(2πt)|²dt ≥ C/c⁷`.

Consequently every positive conductor satisfies
`E_m(c) ≥ (2C/M)/c⁷`.

## Proof [PROVED HERE]

The existing boosted-spline estimate is
`|Û(r)|≥sinh(1)⁴/(1+r²)²`. Translation has unit Fourier modulus,
and the unit-profile dilation gives `|φ̂(r)|=|Û(r/8)|/8`.
On `[c+1,2c+1]`, one has `t≤3c` and
`1+(πt/4)²≤D c²`. Therefore `|φ̂(2πt)|²≥C/c⁸` throughout
this interval. It has length `c` and lies inside `(c,∞)`;
integrating gives the claimed tail lower bound. The already proved
coprime-tail formula bounds every completed conductor by `2/M` times
this same tail.

## Lean status

`CriticalArithmeticCorrelationTheory/TheTiltedSplineHasAPolynomialConductorFloor.lean`
proves the explicit tail floor and its conductor consequence. Final direct
Lean check passed; both axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella import is wired.
Supporting estimate only; counted with the actual growing-overlap source
theorem, if that theorem is proved.
