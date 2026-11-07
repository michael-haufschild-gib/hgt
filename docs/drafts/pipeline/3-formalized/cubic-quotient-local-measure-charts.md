# Local measure charts on the cubic quotient

- **ID:** cubic-quotient-local-measure-charts
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** Projection to the actual cubic quotient is a covering map and preserves the restricted invariant measure on every measurable set where it is injective.

Frobenius energy satisfies `F(gh)≤F(g)F(h)` and `F(g⁻¹)=F(g)`.
Consequently `F(g)≤F(gw)F(w)`. Compact source and target sets bound both
factors, so integral Frobenius sublevel finiteness makes the action properly
discontinuous. The verified level-three freeness gives a covering projection.

An injective measurable chart has disjoint group translates. Partitioning
those translates by the measurable fundamental selector identifies its
quotient measure with its hyperbolic volume. Thus the quotient admits actual
local measure-preserving charts, without an assumed volume normalization.

Source: external OpenAI `CubicSieve/LiteralSources.lean`.
Lean `TheCubicQuotientHasLocalMeasureCharts.lean` proves proper discontinuity,
`integralOrbitProjection_quotientCovering`, `kernelProjection_measurePreserving_on`,
and `kernelL2_continuous_compact_approx`. Direct source check passed; all four
transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

`SmoothCutoffsOnTheCubicQuotient.lean` proves
`kernelQuotient_chartCutoff_exists`: every quotient point has a smooth compact
cutoff equal to one at a lift, with range in `[0,1]` and injective support.
Its support carries the exact restricted quotient measure. The proof chooses
a bump inside a positive-height chart neighborhood. Direct source check passed;
all three transitive axiom audits contain only the same standard axioms.

Sources for cutoffs and coordinates: external OpenAI
`Eisenstein/LocalCutoffs.lean`, `MeanSquare/TransformedColumns.lean`, and
`GaussSum/ReflectedBranches.lean`. Sobolev bounds remain separate analytic inputs.

`CompactCutoffCharts.lean` proves `kernelCompact_finite_compactCharts`:
the open images of `{χ>1/2}` cover the quotient, hence finitely cover every
compact subset. Each supporting chart is measure preserving and its Euclidean
energy mass projection is compact by Rellich. Direct source and transitive
axiom checks pass with only standard axioms. This does not yet bound chart
energy by global quotient energy.
