# Actual stationary pole equations and the remaining value moment

Status: in progress. RH remains open.

Proof chain: actual prime–Gamma pole positivity → integrated Chebyshev square-root control → bounded critical resolvent → RH. Unique late even-gap minima are already formal; their values remain unsigned.

## Conjecturing loop

1. Expand the actual first derivatives. The cross slope should reduce exactly to the pointwise Chebyshev error plus reciprocal-Mangoldt and Gamma corrections.
2. Prove a uniform exponential bound for the diagonal slope after radius two, retaining the boundary slope. At any stationary even test, this should force a genuine square-root bound on the actual pointwise Chebyshev error there.
3. Test whether these instantaneous moments determine the stationary value. The cross value contains a weighted logarithmic sum absent from its derivative. Candidate positive weights on prime powers 2,3,4 preserve total and reciprocal mass but change that logarithmic sum. If this obstruction survives, formalize its exact positive survivor: the missing value moment and the source equation still required to control it.
4. No inference from stationarity to nonnegative value is accepted without that actual arithmetic comparison.

Corpus: `CCMRestrictedWeilPolePrimeChamber`, `CCMRestrictedWeilPoleBoundaryDifferential`, `CCMRestrictedWeilPoleDiagonalBounds`, `CCMRestrictedWeilPoleGapShape`, `CCMRestrictedWeilPoleEntryAgeSource`.

## Work and audit

- [ ] Exact first jets and actual stationarity equation.
- [ ] Boundary/diagonal slope bounds and stationary Chebyshev estimate.
- [ ] Weighted-log value moment and finite support audit.
- [ ] Foreground scratch checks, named leaf builds, axiom audit, lint and umbrella wiring.
- [ ] Current frontier and universal knowledge updates.
