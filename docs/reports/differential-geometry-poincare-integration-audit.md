# DifferentialGeometry Poincaré integration audit

Date: 2026-09-28. Source revision: `7a48598d35109aa99d1cc678e2724c213cdf4ff3`
(v0.1.3, Apache-2.0). This is an integration audit, not a local certification of the
complete upstream proof.

## What the linked endpoint supplies

[`PoincareEndgame.lean:91`](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Skeleton/PoincareEndgame.lean#L91)
constructs `Nonempty (PoincareControlledExtinction M g)` from a closed oriented smooth
three-manifold, simple connectivity, and any initial smooth Riemannian metric.
Its two analytic construction inputs are discharged inside this file by
`uniformDebitSurgeryStepStrong` and `canonicalNeighborhoodsThroughSurgeryStrong`.
They are not hypotheses left to callers of the final theorem.

The inspected definitions have substantive geometric content:

- `ClosedOrientedManifold` bundles a carrier with Mathlib topology, Euclidean charts,
  smoothness, Hausdorffness, compactness, and a manifold orientation.
- `SmoothRiemannianMetric` abbreviates Mathlib's `Bundle.ContMDiffRiemannianMetric` on
  the tangent bundle.
- `PoincareControlledExtinction` contains a finite surgery history, positive terminal
  time, initial orientation-preserving diffeomorphism with metric pullback equality,
  control of the history, and an empty terminal stage. `extinctAt` explicitly means
  terminal-time equality and `IsEmpty` of the last carrier.
- `smoothPoincareConjecture_holds` at line 103 returns a diffeomorphism to the ordinary
  unit sphere in `EuclideanSpace ℝ (Fin 4)`. Its caller supplies only the usual
  manifold/topological structures, compactness, connectedness, and simple connectivity.
  The intervening proof constructs orientation and a smooth metric.
- [`Topology/ThreeManifold/Poincare.lean`](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/DifferentialGeometry/Topology/ThreeManifold/Poincare.lean)
  additionally constructs a smooth structure through Moise's theorem and returns a
  homeomorphism from a compact Hausdorff simply connected topological three-manifold to S³.

This corrects the initial integration report's overly narrow treatment of topology.
The public Poincaré theorem is not merely a reduction conditional on a supplied surgery history.

## Verification boundary and import cost

The pinned revision's [upstream CI run](https://github.com/qinz1yang/differential-geometry/actions/runs/36305635235)
completed successfully on 2026-09-27. Its checked-in workflow runs
`lake --no-cache build DifferentialGeometry`. The upstream README reports only
`propext`, `Classical.choice`, and `Quot.sound` for the advertised endpoints.
Those are upstream evidence, not an independently repeated local kernel/axiom audit.

An exhaustive recursive source-import traversal at this revision found:

| Endpoint | Upstream modules including endpoint | Source lines including comments/blanks | Distinct external import names |
|---|---:|---:|---:|
| Smooth endgame | 11,349 | 3,521,840 | 1,054 |
| Topological Poincaré | 14,197 | 4,021,103 | 1,110 |

All upstream import paths resolved. Counts exclude Mathlib source closure. They measure
the current **module import closure**, not a minimal declaration dependency closure;
unused imports or unnecessary declarations could potentially be pruned. The topological
endpoint adds 2,848 modules, including 2,497 PiecewiseLinear modules.

A scan of both complete import closures, stripping comments and strings, found no tokens
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `run_tac`, `run_elab`, or
`set_option debug.skipKernelTC`. It found two `private opaque` declarations:

- `Geometry/Flow/RicciFlow/Estimates/Distance/Barrier.lean:937`, `completeInst`.
- `Geometry/Compactness/CheegerGromov/Pointed/Compactness/Construction.lean:1266`,
  `connectedCanonicalMetricCompactness`.

Both have explicit proof/construction bodies. They are not unproved axioms. Their syntax
still conflicts with this project's current no-`opaque` lint policy if vendored unchanged.
A lexical scan does not substitute for `#print axioms` after compiling the endpoint.

Upstream pins Lean/Mathlib **4.33.1**; this workspace uses **4.32.2**. No toolchain change,
wholesale dependency, bulk copy, or local build of the upstream closure was performed.

## Concrete relevance to this codebase

| Target | Useful conclusion | Remaining bridge / boundary |
|---|---|---|
| Three-manifold classification infrastructure | Replace an input homeomorphism/diffeomorphism `M ≃ S³` by intrinsic compact Hausdorff (smooth, for the diffeomorphism) three-manifold structures and simple connectivity. Transport sphere invariants and constructions along the resulting equivalence. | Requires a compatible compiled Poincaré dependency. Poincaré assumes simple connectivity; it cannot prove it for an arbitrary source. |
| Nomological S² × N³ obstruction family | Classify the simply connected subclass of the closed oriented three-dimensional factor by S³. Sphere volume/fundamental-class infrastructure can supply a concrete nonzero three-period, preserving rather than erasing the later obstruction. | The paper already permits general closed oriented N³. This is a concrete realization/classification project, not a newly stronger version of that paper theorem. Smooth forms, integration and their compatibility with local period structures still need construction. |
| `NomologicalHomotopyGeometry/HigherPeriodSpencer.lean:33` | Build actual geometric instances of `PeriodGeometry` instead of leaving all geometry abstract. | Poincaré alone does not supply `simplexIntegral_mem_span`, `restricted_carrier`, or `smallCell_limit`. These are integration, closed-subgroup, and local asymptotic results. Use the upstream form/integration layer for these, separately from classification. |
| Existing unitary topology and integer charge | Global SU simple connectivity, sphere topology, determinant classification, explicit universal covers, phase/log lifts. | Completed in the companion integration below, without importing Ricci flow. The old arithmetic π₁ classification already existed and was reused/generalized, not rediscovered. |
| Smooth Stein autonomous-ADE three-dimensional hull argument | Classification may apply if simple connectivity is independently established. | The existing paper's minimal-Reeb-flow obstruction uses a closed orbit from Weinstein/Taubes and does not assume simple connectivity. Poincaré does not replace that missing dynamical theorem. |
| Abelian Chern–Simons finite-sector formula | Potential future link from actual manifold topology to the finite linking-data expression. | `AbelianChernSimonsAsymptotics.lean` currently takes arithmetic linking data, not a manifold. Poincaré does not by itself identify that expression with a geometric partition function. |

Local evidence: the length-three partial-flattening card in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/nomological-homotopy-geometry/`
already identifies its S² × S³ family at line 47 and general closed oriented N³ at line 124;
`smooth-stein-order-two-autonomous-ade-frequency-rank.md` in the
`2-fully-proven/02-analytic-da-entire-functions/` directory discusses the three-dimensional
Reeb-flow obstruction near line 98. Exhaustive source searches found no existing local
Poincaré endpoint or standard smooth three-manifold-to-S³ classifier to replace directly.

## Integration disposition

The substantial reusable topology integration is complete in
[its formalized card](../drafts/pipeline/3-formalized/not_new_scientific_knowledge/differential-geometry-topology-integration.md).
It is distinct from importing the full Poincaré theorem, which remains unported.

A full port needs a separate, explicit compatibility project: choose the smooth endpoint
when consumers already have smooth structures; align or backport the pinned Lean/Mathlib
interfaces; resolve the two proved opaque declarations under local lint; compile the
dependency closure; audit endpoint axioms; then build concrete manifold/form/integration
adapters. Adding a local wrapper that accepts the classification or extinction conclusion as
an argument would not discharge any premise and is not an integration substitute.
