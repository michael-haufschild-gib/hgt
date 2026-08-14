# Functional–relational phase separation for projective constraints — formalized

- **ID:** `projective-constraint-topological-capacity-phase-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `projective-constraint-topological-capacity-phase-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/NonautonomousProjectiveTailCollapse.lean` | the one-sided no-go and the storage arithmetic: `markedFiber_cardinality_budget_with_genus`, `projectiveOrbifold_excess_topological_capacity`, `projectiveCurvature_requires_extensive_topology`, `modularTriangle_projectiveCapacity_exact`, `hurwitzTriangle_projectiveCapacity_exact` and the two order laws |
| `HTGeometry/HurwitzTriangleSumBound.lean` | the sharp threshold `ε ≥ 1/42` with equality only at `(2,3,7)` |
| `HTGeometry/ProjectiveConstraintTopologicalCapacityPhase.lean` | the combined phase-separation theorem over survival witnesses |
| `HTGeometry/FreeCyclicOrbits.lean`, `HTGeometry/OrbifoldMonodromyCover.lean` | **new** — free cyclic orbit counting and the monodromy data of connected unramified covers of a sphere orbifold, with the fibre counts and the lifted-triangulation Euler characteristic |
| `HTGeometry/MonodromyCoverExamples.lean`, `HTGeometry/MonodromyVoltageLift.lean`, `HTGeometry/MonodromyVoltageExistence.lean`, `HTGeometry/HurwitzTriangleCoverTower.lean` | **new** — the explicit `(2,3,7)` cover, connected `ZMod p`-voltage lifts, their existence on hyperbolic covers, and the resulting tower of unbounded degree |
| `HTGeometry/ModularMonodromyCover.lean` | **new** — `ModularCover`: unramified covers of the `(2,3,∞)` modular orbifold, cusps as the cycles of `X·Y`, and the exact storage law `D = 6(2g + s − 2)` |
| `HTGeometry/ModularCoverTower.lean` | **new** — modular covers of unbounded degree and the modular survival witness they carry |
| `HTGeometry/VonDyckTriangleGroup.lean`, `HTGeometry/HurwitzTriangleSubgroupTower.lean` | **new** — the triangle group `Δ(a,b,c)`, sheet stabilisers of index the degree, elliptic-freeness, and unbounded index |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `projectiveOrbifold_excess_topological_capacity`, `projectiveCurvature_requires_extensive_topology`
  — the capacity inequality `(1)`–`(2)` and its consequence that an unbounded-degree projective
  phase needs `2g + s` growing linearly in `D`;
- `hurwitz_euler_defect_ge`, `hurwitz_ordered_sum_eq_iff` — `(H1)`: the universal threshold `1/42`
  and its uniqueness at `(2,3,7)`;
- `MonodromyCover.hurwitz_capacity_exact`, `MonodromyCover.hurwitz_riemannHurwitz` — `(H3)`: every
  connected unramified `(2,3,7)` cover has integral genus and `D = 42(2g − 2)`, with the fibre
  counts derived from the cover;
- `ModularCover.modular_capacity_exact` — `(3)`, `(4)`: every connected unramified cover of the
  modular orbifold satisfies `D = 6(2g + s − 2)` with `s` its number of cusps, the cusp widths
  being the cycle lengths of `X·Y`;
- `modular_storage_order_iff`, `ModularProjectiveSurvivalWitness.degree_lt_iff_capacity_lt` — `(5)`:
  ordering by degree is exactly ordering by Euler capacity;
- `exists_hurwitzCover_degree_gt`, `exists_modularCover_degree_gt` — `(H4)`, `(7)`: covers of
  unbounded degree on both sides of the phase;
- `hurwitzCoverSurvivalWitness`, `modularCoverSurvivalWitness` — both survival witnesses, now with
  degree, genus and cusp number those of constructed covering surfaces;
- `hurwitzTowerGenus_unbounded`, `modularTower_capacity_unbounded` — unbounded relational degree is
  paid for by unbounded topological capacity;
- `projectiveConstraint_functionalRelational_phaseSeparation` — the combined statement `(9)`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/OrbifoldMonodromyCover.lean
lake env lean GaloisForLFunctions/HTGeometry/HurwitzTriangleCoverTower.lean
lake env lean GaloisForLFunctions/HTGeometry/ModularMonodromyCover.lean
lake env lean GaloisForLFunctions/HTGeometry/ModularCoverTower.lean
lake build GaloisForLFunctions.HTGeometry.ModularCoverTower
```

## What closed last

The audit on the paper card found both survival witnesses content-free: their numerical fields were
met by an arbitrary integer family, so the phase theorems, while non-vacuous, carried no geometry.

The repair is a construction.  A connected unramified cover of the `(a,b,c)` sphere orbifold is a
transitive pair of permutations of the sheets whose elliptic monodromies act freely; the marked
fibres are their orbit sets, so the fibre counts and hence the Euler characteristic of the lifted
triangulation are theorems about the cover.  For the compact `(2,3,7)` signature this gives
`D = 42(2g − 2)` with an integral genus — integrality being the orientation constraint
`sign X · sign Y = sign (X·Y)`, which forces `84 ∣ D`.  Forgetting the constraint on the third
monodromy gives the modular orbifold `(2,3,∞)`, where the cycles of `X·Y` are the cusps and the
same Euler count gives `D = 6(2g + s − 2)`.

Unbounded degree comes from the mod-`p` homology of the covering surface, realised as a rank count:
a `ZMod p`-voltage lifts a cover to a `p`-fold cover of the same orbifold when its cyclic sums
vanish, and connectedly when it is not a coboundary; the constraints have rank at most
`f_a + f_b + f_c` and the coboundaries dimension at most `D − 1`, so a connected lift exists exactly
in the hyperbolic range `f_a + f_b + f_c < D`.  Iterating produces both towers, and the two witness
structures are then instantiated by actual covering surfaces.

## Boundary

- The Schwarzian common pullback along modular and arithmetic correspondences, and Kummer
  minimality (strong minimality of the order-three equation of `j`), remain the card's named
  classical inputs, carried by the `commonPullback` and `irreducible` predicates.  They are
  differential-Galois statements about the `j`-function and the `(2,3,7)` Schwarz connection and are
  not used by any theorem listed above.
- The identification of the combinatorial genus with the genus of the covering Riemann surface, and
  of elliptic-freeness with torsion-freeness in `PSL(2,ℤ)` and in cocompact triangle groups, are the
  classical covering-space statements the card cites.
- The broad specialist parent audit is external and remains open.
