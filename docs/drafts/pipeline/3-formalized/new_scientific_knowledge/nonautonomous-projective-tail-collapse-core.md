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
- `markedFiber_cardinality_budget_with_genus`;
- `threeTrappedFibers_degree_add_two_le_exceptionalCard_add_twoGenus`;
- `genusZero_markedFiber_cardinality_budget`;
- `threeTrappedFibers_degree_add_two_le_exceptionalCard`;
- `nonOrbifoldFiberCard_eventually_constant`;
- `stableExceptionalFibers_are_singletons`;
- `stableExceptionalFibers_are_totallyRamified`;
- `projectiveOrbifold_excess_topological_capacity`;
- `projectiveCurvature_requires_extensive_topology`;
- `modularTriangle_projectiveCapacity_exact`;
- `modularTriangle_projectiveCapacity_saturates`;
- `modularProjectiveStorage_order_iff`;
- `hurwitzGap_degree_add_eightyFour_le_genus`;
- `hurwitzTriangle_projectiveCapacity_exact`;
- `hurwitzTriangle_projectiveCapacity_saturates`;
- `hurwitzProjectiveStorage_order_iff`;
- `projectiveOrbifold_excess_degree_budget`;
- `hurwitzGap_degree_le_exceptionalBudget`;
- `projectiveHyperbolicTail_eventually_absent`;
- `nonOrbifoldFiberCard_eventually_le_two`;
- `projectiveTail_eventually_nonhyperbolic_with_twoPointSkeleton`.

`HurwitzOrbifoldGap.lean` proves the previously external discrete curvature input:

- `triangleOrbifoldExcess`;
- `hyperbolicTriangle_excess_ge_one_over_fortyTwo`;
- `hyperbolicTriangle_no_excess_below_one_over_fortyTwo`;
- `triangleOrbifoldExcess_two_three_seven`.

Thus the interval `(0,1/42)` is formally empty for ordered integral hyperbolic triangle
signatures, and `(2,3,7)` formally attains its endpoint.

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
genus-plus-puncture capacity law, the Riemann--Hurwitz obstruction to three trapped fibres,
stabilization of the exceptional skeleton, the algebraic `1/42` cutoff, and the simultaneous late
surface

```text
bad-fibre cardinality <= 2  and  not hyperbolic.
```

They also formalize the positive sharp phase on the other side of the fixed-source obstruction.
The universal integral-orbifold gap first gives the compact threshold

```text
degree + 84 <= 84 genus.
```

A torsion-free cover of the `(2,3,7)` triangle orbifold attains equality exactly, formalizing the
absolute `1/42` topology density.  For a torsion-free cover of the modular `(2,3,infinity)`
orbifold, the local ramification counts and Riemann--Hurwitz imply

```text
degree = 6(2 genus + cuspCard - 2),
```

so the general capacity inequality is saturated and strict ordering by correspondence degree is
equivalent to strict ordering by Euler capacity.  The paper card
`projective-constraint-topological-capacity-phase-law` supplies the geometric triangle/modular
curve and projective-minimality inputs.

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
degree and exceptional budgets.  Positively, it identifies linear genus-plus-puncture growth as
the resource required by a correspondence-based projective protocol and proves the exact
`1/42` compact threshold together with triangle and modular saturation of the arithmetic core.
The current RH tree supplies neither architecture, so this is a reusable design criterion rather
than an RH proof step.

## Verification

Serialized direct compilation of `NonautonomousProjectiveTailCollapse.lean` and
`ParabolicOrbifoldTwelveCharge.lean` succeeds.  The newly created `HurwitzOrbifoldGap.lean` first
received its one missing exact-module build and then passed direct leaf compilation.  Only the
missing/stale exact-module object for the new twelve-charge leaf was built earlier.  The
holonomy-freezing extension was checked by direct leaf compilation because its object already
existed; no umbrella, theorem-area, full, or self-concurrent build was run.

## Gates

- [x] exact local transport identities
- [x] non-Galois fibre-cardinality argument
- [x] eventual two-point/non-hyperbolic global budget theorem
- [x] genus-plus-puncture capacity, universal `1/42` threshold, and exact triangle/modular saturation
- [x] discrete integral-orbifold gap and `(2,3,7)` endpoint formalized
- [x] single holonomy enhancement and eventual signature-freezing finite-poset core
- [ ] formal geometric descent from rational projective connections to the budget hypotheses
- [ ] formal affine crystallographic lift and covering-degree index factorization
