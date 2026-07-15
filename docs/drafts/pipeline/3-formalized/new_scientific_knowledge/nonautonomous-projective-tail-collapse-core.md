# Nonautonomous projective-tail rank-collapse core

- **ID:** nonautonomous-projective-tail-collapse-core
- **Stage:** 3-formalized
- **Type:** FORMALIZATION
- **Scientific status:** `[FORMALIZATION]` of a `[NOVELTY UNVERIFIED]` paper theorem
- **Paper theorem:** `nonautonomous-rational-complete-tail-orbifold-classification`
- **Lean module:** `GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTailCollapse`

## Formalized surface

The module proves without placeholders:

- `affineConnection_shiftedResidue_transport`;
- `projectiveConnection_exponentDiscriminant_transport`;
- `affineConnection_projectivization_transport`;
- `parabolicHolonomyOrder_dvd_twelve`;
- `genusZero_markedFiber_cardinality_budget`;
- `threeTrappedFibers_degree_add_two_le_exceptionalCard`;
- `nonOrbifoldFiberCard_eventually_constant`;
- `stableExceptionalFibers_are_singletons`;
- `stableExceptionalFibers_are_totallyRamified`;
- `projectiveOrbifold_excess_degree_budget`;
- `hurwitzGap_degree_le_exceptionalBudget`;
- `projectiveHyperbolicTail_eventually_absent`;
- `nonOrbifoldFiberCard_eventually_le_two`;
- `projectiveTail_eventually_nonhyperbolic_with_twoPointSkeleton`.

`ParabolicOrbifoldTwelveCharge.lean` additionally formalizes the six parabolic sphere signatures,
their finite cone orders, and the universal divisibility of every phasewise holonomy order by
`12`.

Together these certify the exact local affine/projective ramification arithmetic, the
Riemann--Hurwitz obstruction to three trapped fibres, stabilization of the exceptional skeleton,
the algebraic `1/42` cutoff, and the simultaneous late surface

```text
bad-fibre cardinality <= 2  and  not hyperbolic.
```

The proof uses static prefix-degree constraints only.  It contains no `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe` declaration and performs no numerical experiment.

## Deliberate paper boundary

Lean does not yet encode rational projective connections as geometric structures on `P1`, the
finite faithfully flat deck equalizer, Casale's classification, local logarithmic-monodromy
descent, or the classification of spherical/Euclidean orbifold coverings.  These inputs remain
visible in the paper theorem rather than being hidden as axioms.  The formalized conclusion is the
combinatorial and algebraic rank-collapse core conditional on their explicit geometric budgets.

## RH impact audit

The formal theorem rules out a hyperbolic projective tail once an RH protocol supplies the stated
degree and exceptional budgets.  The current RH tree supplies no such rational protocol, so this
is a reusable exclusion theorem rather than an RH proof step.

## Verification

Serialized direct compilation of `NonautonomousProjectiveTailCollapse.lean` and
`ParabolicOrbifoldTwelveCharge.lean` succeeds.  Only the missing/stale exact-module object for the
new twelve-charge leaf was built; no umbrella, theorem-area, full, or concurrent build was run.

## Gates

- [x] exact local transport identities
- [x] non-Galois fibre-cardinality argument
- [x] eventual two-point/non-hyperbolic global budget theorem
- [ ] formal geometric descent from rational projective connections to the budget hypotheses
- [ ] formal spherical/parabolic orbifold-cover classification
