# Two-prime difference lags in local windows

- **Stage:** 3-formalized
- **Source:** review-0911 §11.6, A65.

## Statement

For distinct primes `p,q` and every fixed `r>0`, RH is equivalent to a
uniform lower bound for the cubic-spline correlation `c_B` on the lags
`log(p^a q^b)−log(p^a' q^b')` inside arbitrarily late windows
`|u−T|≤r√T`.

## Proof

The difference lags form the dense group `ℤ log p+ℤ log q`. Continuity
extends each local lower bound to the open interior of its window, hence
to the closed window of half the radius. The continuous square-root
window criterion excludes every positive zero depth. Conversely RH
bounds the correlation at every real lag by its value at zero.

No maximal zero depth or attainment hypothesis is needed.

## Lean

`SurfaceOfSpecZ/ScaleLocality/TwoPrimeLocalWindows.lean`:
`riemannHypothesis_iff_twoPrime_squareRoot_windows`.
Direct audit passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.
