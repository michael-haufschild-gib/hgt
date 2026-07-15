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
their finite cone orders, and:

- `ParabolicSphereSignature.holonomyOrder` and `isCompact`;
- `ParabolicSphereSignature.eq_of_holonomyOrder_eq_isCompact_eq`;
- `parabolicHolonomyOrder_no_two_strict_enlargements`;
- `dvd_holonomyOrder_of_le`;
- `parabolicHolonomyOrder_eventually_constant`;
- `parabolicSphereTower_has_protocol_charge`;
- `parabolicSphereSignature_eventually_constant`.

Thus the formal surface now distinguishes the sharp protocol-specific charge `<=6` from the
precommitted universal charge `12`, and proves the finite-poset core of the single-enhancement and
signature-freezing laws.

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
new twelve-charge leaf was built earlier.  The holonomy-freezing extension was checked by direct
leaf compilation because its object already existed; no umbrella, theorem-area, full, or
self-concurrent build was run.

## Gates

- [x] exact local transport identities
- [x] non-Galois fibre-cardinality argument
- [x] eventual two-point/non-hyperbolic global budget theorem
- [x] single holonomy enhancement and eventual signature-freezing finite-poset core
- [ ] formal geometric descent from rational projective connections to the budget hypotheses
- [ ] formal affine crystallographic lift and covering-degree index factorization
