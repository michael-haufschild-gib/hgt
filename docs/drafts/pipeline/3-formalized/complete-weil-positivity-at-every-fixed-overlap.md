# Complete Weil positivity at every fixed overlap

- **ID:** complete-weil-positivity-at-every-fixed-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statements

For every nonzero compact `C²` unit profile, fixed `c>0`, and conductor `m≥1`,
the normalized Ramanujan vector is an actual complete-Weil norm quasimode:

`‖W_N(c) r̂_m − completedConductorEnergy(φ,c,m) r̂_m‖₂ → 0`.

For the explicit tilted unit spline and each fixed `c>0`, there is `e_c>0`
such that every eigenvalue of the complete Weil matrix is at least `e_c`
for all sufficiently large `N`. In particular, the complete matrix is
eventually positive definite; every corresponding real atomic test has
nonnegative literal complete Weil form. The horizon may depend on `c`; this makes
no claim about a prescribed growing-overlap sequence or RH.

## Proof [PROVED HERE]

The complete residual plus the upward defect already tends to zero in norm
by `TheCompleteWeilResidualIsTheUpwardDefect`. The literal upward norm theorem
identifies its action with `shellCorrection·r_m`. Passing to the normalized
Ramanujan mode multiplies that residual by `1/√ϕ(m)`; linearity is exact on
the horizon coordinates. Subtracting the vanishing upward defect proves the
complete norm-quasimode limit with the completed conductor energy.

For the tilted spline, the actual complete form retains a positive multiple
of the prime-edge defect up to bounded mass cost. The completed conductor
energies have a common positive floor `e`. Spectral assembly combines these
facts: the reserve captures every low-energy unit vector in a fixed finite
Ramanujan space, while the norm quasimodes make every coordinate in that
space small on the spectral subspace below `e/2`. This contradicts the
coordinate capture bound. Hence every eigenvalue is eventually at least
`e/2>0`.

All inputs concern the literal complete matrix or its actual source
residuals. The quasimode hypothesis of the prior assembly theorem is
discharged, not retained as an assumption.

## Inputs

- `TheUpwardPrimeRowsRealizeTheCompletedShellCorrection`;
- `TheCompleteWeilResidualIsTheUpwardDefect`;
- `MacroscopicOverlapTiltedSplineReserve`;
- `MacroscopicOverlapConductorFloor`;
- `MacroscopicOverlapSpectralAssembly`.

## Lean status

Leaf: `CriticalArithmeticCorrelationTheory/TheCompleteWeilFormIsPositiveAtEveryFixedOverlap.lean`.

- `tendsto_completeWeilMatrix_completedConductor_residual_norm`;
- `exists_tiltedUnitSpline_completeWeil_eigenvalue_floor`;
- `eventually_tiltedUnitSpline_completeWeilMatrix_posDef`;
- `eventually_tiltedUnitSpline_weilQuad_atomicTest_nonneg`.

Final direct no-olean check passed without warnings. All four transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
CACT umbrella import registered. This answers fixed-overlap positivity
problem I1 of the 29 October review; prescribed growing-overlap positivity
remains open.
