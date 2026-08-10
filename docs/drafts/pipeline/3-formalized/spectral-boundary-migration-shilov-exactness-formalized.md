# Spectral boundary migration and Shilov exactness

- **ID:** `spectral-boundary-migration-shilov-exactness-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / boundary-ideal towers, Shilov boundary, C*-envelope
- **Date:** 2026-08-10
- **Paper proof:** `spectral-boundary-migration-shilov-exactness.md`

## What is formalized

The card's algebraic core — boundary ideals of a tower, the deficit calculus,
derived-limit vanishing and the migration law — was already Lean.  What this
promotion adds is the analytic layer the card had listed as *absent from
mathlib and dependency-closed only on paper*:

> "current mathlib has completely positive maps between C*-algebras but lacks
> operator systems, Shilov ideals, C*-envelopes, boundary representations, and
> locally C*-algebras."

All five are now built, unconditional, axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`), and reachable from the
`GaloisForLFunctions.HTGeometry` umbrella.

## Formal declarations

### Boundary theory (not in mathlib)

`HTGeometry/BauerMaximumPrinciple.lean`
- `isExtreme_setOf_eq_max`, `exists_extremePoint_forall_le` — Bauer's maximum
  principle.

`HTGeometry/MilmanExtremePoints.lean`
- `isCompact_convexJoin`, `isCompact_convexHull_biUnion`,
  `closure_subset_add_nhds`, `exists_mem_of_extremePoint_mem_convexHull_biUnion`,
  `extremePoints_closure_convexHull_subset` — Milman's partial converse to
  Krein–Milman.

`HTGeometry/ChoquetBoundaryFunctionSystem.lean`
- `evalPoint`, `stateBody`, `choquetBoundary`;
- `isBoundarySet_choquetBoundary` — *with no hypothesis on `S`*;
- `IsBoundarySet.re_le_of_forall_le`, `evalPoint_mem_stateBodyOn`,
  `choquetBoundary_subset_of_isBoundarySet`;
- `isBoundarySet_inter_of_functionSystem`,
  `isLeast_shilovBoundary_of_functionSystem`,
  `shilovBoundary_eq_closure_choquetBoundary`.

This discharges the `hinter` hypothesis of
`ShilovCommutativeBoundary.isLeast_shilovBoundary`.  It also **replaces** the
peak-point hypothesis `hb` of `shilovBoundary_eq_closure_peakPoints`, which is
false in general: on a non-metrizable compact Hausdorff space the peak points
can be too few for their closure to be a boundary.

### Shilov ideal and C*-envelope

`HTGeometry/ShilovIdealCommutative.lean`
- `shilovIdeal`, `isClosed_shilovIdeal`, `exists_isClosed_mem_iff_of_isClosed`;
- `le_shilovIdeal_of_isBoundaryIdeal` — maximality, **unconditional**;
- `isBoundaryIdeal_shilovIdeal`, `isGreatest_shilovIdeal`.

`HTGeometry/CommutativeCompleteBoundary.lean`
- `sandwich`, `sandwich_mem`, `sandwich_apply`, `star_sandwich`;
- `mem_cstarCone_of_forall_mem`, `sub_mem_cstarCone_of_forall_mem` — every
  boundary is a *complete* boundary, so the scalar-level Shilov ideal is
  already the complete one.

`HTGeometry/CStarEnvelopeCommutative.lean`
- `restrictStarAlgHom`, `norm_restrictStarAlgHom_eq_of_isBoundarySet`,
  `restrictStarAlgHom_surjective`, `restrictStarAlgHom_eq_zero_iff`;
- `envelopeMap`, `envelopeMap_eq_zero_iff`,
  `envelope_isometric_surjective_kernel`.

`HTGeometry/AffineFunctionSystemEnvelope.lean`
- `affineFunctions`, `stateBody_affineFunctions`,
  `image_choquetBoundary_affineFunctions`,
  `image_shilovBoundary_affineFunctions`, `envelope_affineFunctions` —
  `C*_e(A(K))` lives on `closure (ext K)`.

`HTGeometry/CommutativeGeneration.lean`
- `generates_of_separatesPoints`, `generates_envelope_image`,
  `bijective_of_isometry_envelope` — the generation input of
  `ShilovLocalBoundaryIdeal`'s comparison theorems, discharged by
  Stone–Weierstrass.

### Operator systems

`HTGeometry/MatrixModuleMultiplication.lean`, `MatrixOrderedSpace.lean`,
`OperatorSystemMatrixOrderUnit.lean`, `OperatorSystemLevelNorm.lean`,
`MatrixOrderedMap.lean`, `CommutativeOperatorSystem.lean`
- `mulLeft`/`mulRight`, `compress`, `compress_mul`;
- `IsMatrixOrdering`, `blockDiagonal_mem`, `vecCompress_mem`;
- `IsMatrixOrdering.smul_mem` — nonnegative scaling is *not* an axiom;
- `isMatrixOrderUnit_of_levelOne` — the matrix order unit axiom is redundant;
- `levelNorm`, `levelNorm_compress_le`, `levelNorm_fromBlocks` (Ruan's
  direct-sum law);
- `IsCompletelyPositive`, `isMatrixOrdering_comap`;
- `isMatrixOrdering_cstarCone`, `isOrderUnitLevelOne_one`, `levelNorm_cstarCone`.

### Boundary representations

`HTGeometry/PureStatesContinuousFunctions.lean`
- `stateBody_subset_of_isClosed_convex`, `evalPoint_mem_extremePoints_top`,
  `extremePoints_stateBody_top`, `choquetBoundary_top`, `shilovBoundary_top`.

`HTGeometry/BoundaryRepresentationCommutative.lean`
- `resMap`, `image_stateBody`, `extensionFibre`, `isExtreme_extensionFibre`;
- `mem_choquetBoundary_iff_uniqueExtension` — Arveson's unique-extension
  property holds exactly on the Choquet boundary.

### Locally C*-algebras

`HTGeometry/LocallyCStarAlgebra.lean`
- `IsCoherentTower`, `projLimit`, `projSubring`, `star_mem_projLimit`;
- `isClosed_projLimit`, `completeSpace_projLimit`;
- `norm_star_mul_self_apply`, `boundedPart`, `boundedNorm`,
  `boundedNorm_star_mul_self`.

## Scope

The boundary-representation and complete-Shilov-ideal results are proved in the
**commutative model**, which is the model the card's manuscript uses.  Their
noncommutative statements — Arveson's boundary representations for a general
operator system, and the matricial Shilov ideal of a noncommutative C*-algebra —
are not claimed here and remain open.

## Audit

- every declaration above builds under `lake build +GaloisForLFunctions.HTGeometry`;
- `#print axioms` on each headline theorem yields exactly
  `[propext, Classical.choice, Quot.sound]`;
- no `sorry`, `admit`, project `axiom`, `opaque` or `unsafe` declaration in any
  of the modules listed;
- the formal lint gate reports nothing against them.
