# Mass-shifted super-apex degree persistence

- **ID:** mass-shifted-super-apex-degree-persistence
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** §9.3 positive-variation frontier

## Frozen conjecture

Inside one finite positive block, every current Gauss node has a strictly larger node at next
degree.  Hence, at fixed positive mass, source-first super-apex null-flag positivity cannot disappear
when admission degree increases.

## Falsifiers

- Must use finite `PositiveMomentFormBelow`, not global representing measure.
- Need outer-node interlacing, not ordinary between-node interlacing.
- Persistence applies at fixed mass only.  It does not control diagonal degree--mass schedules.
- Current-node positivity is needed to exclude a negative large-magnitude residue masquerading as
  positive square flag; record exact assumption.

## Attack

Choose maximal current finite Gauss node, factor current monic admission by all simple nodes, prove
its cofactor positive at maximum, use finite confluent Christoffel--Darboux to transfer positivity to
preceding admission, then finite three-term recurrence and eventual monic positivity to produce next
root above maximum.  Feed threshold persistence into exact nodewise null-flag theorem.

## Log

- 2026-08-13 — frozen after completed-source/nodal bridge isolated positive variation as missing
  quantity and corpus search found only global outer-node theorem.
- 2026-08-13 — proved finite outer interlacing from finite positive moment block only.  Maximal
  current node has positive cofactor; finite confluent Christoffel--Darboux makes preceding
  admission positive there; three-term recurrence makes next admission negative there; monic
  eventual positivity and IVT produce a next node strictly above it.
- 2026-08-13 — transported outer-node theorem into generic source-first super-apex null flag and
  literal shifted-Xi completed-source null flag.  This proves fixed-mass positivity is upward-closed
  under one degree step.

## Exact survivor

For a finite positive block with `m + 2 < N`,

```text
∃ z ∈ gaussNodes s (m + 1), ∀ x ∈ gaussNodes s m, x < z.
```

Consequently, for positive current nodes, `y > 0`, and positive Poisson height,

```text
0 < NullFlag(s,m,y,a,eta) -> 0 < NullFlag(s,m+1,y,a,eta).
```

The literal shifted-Xi theorem uses only a finite Hankel positive-definite block and the exact
completed-source/Gauss identification.  Degree renewal therefore cannot discharge a positive
super-apex source defect at fixed mass.  Any closing budget must carry an explicit mass-boundary
flux; a scalar degree reporter cannot close the route.

## Lean

- `formal/GaloisForLFunctions/HTGeometry/FiniteExtremeNodePersistence.lean`
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionNullFlagDegreePersistence.lean`
- wired into both umbrellas
- direct checks and targeted final builds pass
- axiom audit for all four public theorems: `propext`, `Classical.choice`, `Quot.sound` only
- no computation, representing measure, infinite extension, RH premise, or added axiom

## Remaining boundary

This is not a global budget.  It identifies directionality of missing producer: degree creates or
preserves positive defect, while only mass evolution can transport it through moving apex.  Open
core is quantitative two-dimensional degree--mass flux law compatible with arithmetic source
balance, not another orientation theorem.
