# PW singular neutral-orbit boundedness no-go

- **ID:** PW-SNOB
- **Stage:** 3-formalized
- **Type:** PW-B ROUTE-CLASS NO-GO
- **Chain killed:** `PW endpoint winding -> unique singular FE carrier -> bounded fixed-neutral realization -> partner balance -> shared Ward -> RH`

## Result

For source-forced gain `a(x)=x⁻¹ exp(x-x⁻¹)`, reciprocal gauge covariance and boundary blow-up imply `g(x)→∞`, `a(x)→∞`, and amplification of `(0,1)` tends to infinity. Hence no finite `C` uniformly bounds positive-scale blocks in neutral energy—or in any fixed source-independent energy coercive against neutral norm. This covers every fixed two-channel Hilbert norm.

## Sharp survivor

Each block still conserves exact positive source-adapted energy. Only unbounded/domain-sensitive realization or source-dependent weighted completion survives.

## Certificate

- Lean: `pwSingularNeutralOrbit_boundedness_noGo`
- Module: `ThetaCuspHawkingParikhWilczekSingularNeutralOrbitBoundednessNoGo`
- Direct check: PASS
- Targeted build: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Corpus duplicate search: none
- Literature audit: general unbounded weighted-composition theory exists; no exact PW/Gamma singular-carrier theorem found.
