# Prime–pole cancellation uniform over all Haar details

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** SC arithmetic mixed-source control.

Let `R(Y,a,b)` be the literal full prime-window coupling minus both mixed
pole terms, divided by `√Y`. For each fixed positive coarse index `b`,
conjecture

```text
sup_{X,d : Σ_{a=1}^X haarMass(a)d_a² ≤ 1}
  |Σ_{a=1}^X d_a R(Y,a,b)| → 0.
```

This removes every cutoff on the detail indices and permits arbitrary
signed sections normalized in their original `L²` mass. It does not remove
the `√Y` normalization or prove an upper bound for the complete Weil index.

## Proposed proof

On `u≥log 2`, support restricts the full trace to prime powers
`m≤2Y(b+1)e^(−u)`. Weighted Chebyshev therefore gives
`0≤T_(Y,b)(u)/√Y≤C√(b+1)e^(−u/2)`.
Window PNT gives pointwise convergence to
`4(√(2b+2)−√(2b))e^(−u/2)`. Squared dominated convergence on this half-line
then gives `L²` convergence of the trace. Cauchy–Schwarz controls its pairing
with every normalized Haar section simultaneously.

The remaining normalized pole is `2 A(h)B(q_b)/Y`. The existing exact
inequality `|A(h)|²≤Σ haarMass(a)d_a²` controls it uniformly as well.
The full prime support identity identifies this analytic pairing with the
literal source remainder.

A quantitative extension would combine the classical Chebyshev error on
`u≤(log Y)/2` with the exponential majorant on the complementary tail.
It predicts `O(√b exp(−c√log Y))` for each trace norm, hence uniform
coarse sections of indices `b≤exp(c'√log Y)` for sufficiently small `c'>0`.
The quantitative transfer remains unproved.

## Audit

Corpus search found fixed-family and growing-square packet cancellation,
the pointwise window limit, and the bounded Haar pole functional. No
all-detail `L²` operator limit was found. The refined trace majorant and
the operator limit are not yet formalized. External priority is unchecked.
