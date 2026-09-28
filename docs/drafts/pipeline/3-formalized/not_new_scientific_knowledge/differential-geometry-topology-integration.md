# DifferentialGeometry topology integration

- **ID:** differential-geometry-topology-integration
- **Stage:** 3-formalized / not_new_scientific_knowledge
- **Type:** THEOREM (paper)
- **Source:** qinz1yang/differential-geometry, revision `7a48598d35109aa99d1cc678e2724c213cdf4ff3` (Apache-2.0).
- **Statement:** Classify finite-unitary loop classes by determinant winding, prove finite special-unitary groups simply connected, and provide simply connected finite real spheres and concrete covering consequences.

## Goal

Discharge the chart-confinement premises of existing special-unitary loop-contraction results. Expose unitary stabilization as an isomorphism. Integrate topology below the upstream Poincaré endpoint with actual local consumers, rather than importing a disconnected theorem collection.

Broader source audit found that `RHTower/PrimeAFMatrixDeterminantSplit.lean` already proves determinant injectivity and triviality of π₁(SU(n+1)); `PrimeAFMatrixOperatorKOneDirectLimit.lean` already classifies its integer charge. These are existing results, not new additions. Extract the determinant proof mechanism into reusable HTGeometry and reconnect the arithmetic endpoint to it. The actual extensions are arbitrary finite index carriers, global `SimplyConnectedSpace` and loop/path contraction interfaces, sphere topology and lifting consequences.

## Gates and work

- [x] Search prior research; inspect existing normalization, path connectedness, stabilization, open-cover loop decomposition, and covering modules.
- [x] Inspect pinned upstream circle, retraction, homotopy-equivalence and sphere proofs, plus Poincaré endpoint and smooth endgame.
- [x] Dependency-closed mathematical argument below (standard circle covering and existing local stabilization theorem are dependencies).
- [x] Formalize circle fundamental group and map infrastructure.
- [x] Extract determinant-induced finite-unitary classification; prove stabilization injectivity; extend to arbitrary nonempty finite index types.
- [x] Prove global special-unitary nullhomotopy, simple connectivity and local path connectedness, including empty index types.
- [x] Prove sphere simple connectivity in all real dimensions at least two.
- [x] Verify continuous phase/logarithm lifting on these concrete domains.
- [x] Construct global determinant product coordinates and the explicit simply connected cover of each positive-dimensional unitary group; classify fibers by integer `2π` translations.
- [x] Wire umbrella, audit axioms, run final leaf checks and formal lint; document unrelated failures precisely.

## Paper proof

1. The quotient cover ℝ → ℝ/ℤ has contractible total space and deck group ℤ. The standard circle homeomorphism identifies its basepoint with 1, giving π₁(S¹,1) ≃ ℤ.
2. Let dₙ : U(n) → S¹ be determinant. For n=1 it is a homeomorphism, with inverse the one-entry diagonal matrix. For each positive n, existing local two-chart loop decomposition proves that block stabilization U(n) → U(n+1) induces a surjection on π₁. Determinant commutes with this block stabilization. Inductively dₙ induces an injection: lift two loop classes along stabilization, compare their determinants, and apply injectivity one dimension below. The diagonal determinant section proves surjectivity. Thus dₙ induces an isomorphism for every n≥1, and stabilization is an isomorphism as well.
3. Existing normalization r(U)=U D(det U)⁻¹ continuously retracts U(n) onto SU(n). The inclusion of any SU(n) loop has constant determinant, hence is nullhomotopic by injectivity of dₙ. Compose its nullhomotopy with r to contract the original loop inside SU(n). Translation moves any basepoint to 1; existing path connectedness then gives simple connectivity. The zero-dimensional group is a singleton and is handled separately. No logarithm chart, radius, phase or selected nullhomotopy is assumed.
4. For a real unit sphere in dimension n+3, complements of antipodal points are contractible by stereographic projection. Their intersection is homeomorphic to the punctured orthogonal complement, of dimension n+2≥2, hence path connected. Existing local open-cover loop decomposition contracts loops in the union. Path connectedness and basepoint transport give simple connectivity of the full sphere. This is the upstream sphere proof mechanism, with arbitrary finite dimension and local loop-decomposition infrastructure replacing its separate van Kampen stack.
5. Existing local injectivity of connected covers over simply connected bases now applies to these concrete spaces, removing the abstract simple-connectivity premise from those instances.
6. The map U ↦ (r(U), det U) has continuous inverse (S,z) ↦ S D(z). The identities follow from determinant multiplicativity, det D(z)=z and r(SD(z))=S. It gives a homeomorphism U(ι) ≃ SU(ι) × S¹ for a chosen index. The product map id × exp from SU(ι) × ℝ is a surjective covering: a circle covering chart is multiplied by the identity on SU(ι). Products of simply connected spaces are simply connected by coordinatewise path homotopy. Composing with the inverse determinant homeomorphism therefore constructs a simply connected, surjective covering of U(ι). This explicit space-level decomposition and covering are not present in the preexisting integer-charge classification.
7. Determinant normalization is a continuous retract; a quotient of a locally path-connected space is locally path connected. Circle and complex exponential covering-lift theorems then give a unique normalized real phase and existence of a continuous complex logarithm for circle-/unit-valued continuous functions on SU(ι) and on real spheres S^(n+2).

## Audit boundaries

- The Poincaré statement in `Topology/ThreeManifold/Poincare.lean` uses ordinary Mathlib charted manifold, compactness, Hausdorffness and simple connectivity. Earlier blanket dismissal of upstream topology was unsupported.
- The complete Ricci-flow/Moise dependency closure has not been compiled locally. The follow-up [Poincaré audit](../../../../reports/differential-geometry-poincare-integration-audit.md) records the exact endpoint semantics, exhaustive import inventory, source scan, upstream CI evidence, and concrete local applications. It does not claim independent kernel verification or import of that closure.
- These classical topology results are **not new scientific knowledge**. Integration value is explicit premise discharge and stronger local classifications.
- Preserve unrelated dirty worktree changes. No full/umbrella build, heartbeat changes, computational certificates, new axioms or proof holes.

## Source-to-integration map

All upstream paths below refer to the pinned revision above.

| Upstream evidence | Local use / decision |
|---|---|
| `Topology/FundamentalGroup/Circle.lean` | Adapt integer-period quotient-cover argument; compose the circle homeomorphism directly with the covering, avoiding a separate homotopy-equivalence transport stack. |
| `Topology/FundamentalGroup/Retraction.lean` and `SimplyConnected.lean` | Use induced-map retraction and basepoint transport with existing local determinant normalization; obtain global simple connectivity and arbitrary-endpoint path homotopies. |
| `Topology/FundamentalGroup/Sphere.lean` | Generalize S²/S³ instances to every S^(n+2); reuse local `LoopOpenCoverDecomposition` instead of importing another van Kampen implementation. Existing unitary stereographic theorem now delegates to the general punctured-sphere result. |
| `Topology/Homology/MayerVietorisExactness.lean` | Inspected against local `RelativeSingularHomology`, `Excision`, and small-chain machinery. Do not duplicate the already-existing relative/excision layer in this integration. |
| `Topology/ThreeManifold/Poincare.lean` and `Geometry/Flow/RicciFlow/Surgery/Skeleton/PoincareEndgame.lean` | Verified public statement and immediate construction through Moise and controlled extinction; complete transitive proof closure remains unaudited and unported. |
| Generic universal-cover and Ricci-flow product-cover sources | Inspected relevant mechanisms; the unitary product coordinates allow a much smaller explicit cover using Mathlib's circle covering and newly constructed product sheets. No generic path-class universal-cover topology or Ricci-flow contract is imported. |

## Concrete Lean interfaces

- `FiniteSpecialUnitarySimplyConnected.lean`: all finite carriers, including empty; `finiteSpecialUnitary_loop_nullhomotopic`, `finiteSpecialUnitary_paths_homotopic`, `finiteSpecialUnitaryPathHomotopy`; simple/local path connectedness instances.
- `SphereSimplyConnected.lean`: `realSphereSimplyConnectedSpace`, `realSphere_paths_homotopic`, `realSphere_loop_nullhomotopic`; general punctured-sphere homeomorphism and contractibility.
- `FiniteUnitaryDeterminantProduct.lean`: `finiteUnitaryDeterminantProductHomeomorph`, a topological product, not a direct-product group-isomorphism assertion.
- `FiniteUnitaryUniversalCover.lean`: explicit map, covering proof, surjectivity, simply connected total space and exact fiber classification.
- `SimplyConnectedMatrixSphereLifting.lean`: unique normalized continuous real phases and continuous complex logarithms on SU(ι) and S^(n+2).
- `FiniteUnitaryFundamentalGroup.lean` and `FiniteUnitaryFundamentalGroupReindex.lean`: extracted circle-valued determinant classifier, integer equivalence, stabilization isomorphism, arbitrary finite carrier transport. Existing arithmetic classifier now delegates to this reusable topology through global SU simple connectivity.
- `FundamentalGroupContinuousHom.lean`, `CircleFundamentalGroup.lean`, `CircleProductCovering.lean`: supporting functoriality, circle classification, simply connected products and explicit product covering charts.

## Completed validation

- Final sequential `lake --old env lean <leaf> -o <olean>` checks passed for all ten new leaves, both modified existing leaves, and the downstream `PrimeAFMatrixOperatorKOneDirectLimit` consumer. No full or umbrella build ran.
- All 54 audited declarations (52 new public declarations and two existing arithmetic endpoints) report exactly `propext`, `Classical.choice`, and `Quot.sound`. A separate `/tmp` name-check file verified every new Mathlib name on this toolchain. Two compiled examples apply the existing connected-cover injectivity theorem to the new sphere and special-unitary instances.
- All new leaves and the arithmetic consumer checks have zero warnings. The old stabilization file retains 13 preexisting linter warnings; its changed stereographic lemma adds none.
- `scripts/formal_tools.py index` completed; `git diff --check` passed. Ten new leaves are wired through `HTGeometry.lean`.
- Exhaustive `rg` check found two uses of the changed punctured-sphere theorem, both in `FiniteUnitaryFundamentalGroupStabilization`; determinant injectivity has the existing same-file special-unitary consequence and the `PrimeAFMatrixOperatorKOneDirectLimit` consumer. Both consumers are included in final verification.
- `scripts/formal_tools.py lint` found no active proof holes or unwired task modules; it failed on 23 unrelated modules unreachable from area umbrellas (19 RHTower, 4 HTGeometry) in the concurrent worktree. Do not wire unrelated research drafts merely to make this gate green.
- Unrelated unreachable HTGeometry modules: `GammaHorizontalRatio`, `JensenIntegratedCountBound`, `OperatorCertificateGenealogy`, `SectorPhragmenLindelof`.
- Unrelated unreachable RHTower modules: `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `ChronologicalTailInjectivity`, `ChronologicalTailKernelLipschitz`, `ChronologicalTailProjectionPerturbation`, `ChronologicalTailRiemann`, `ChronologicalTailSampleSpace`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `MoebiusMollifiedZetaField`, `ThetaRelativeSourceRigidity`, `ThetaTailDivisorCapacity`, `ThetaTailSimpleCriticalThreshold`, `WeilPositivitySummablePerturbationRigidity`, `ZetaZeroDensityPowerSaving`.

## Log

- 2026-09-28 — Created after read-only investigation and adversarial proof review.
- 2026-09-28 — Completed ten-leaf topology integration, existing-consumer refactors and targeted kernel/axiom checks. Follow-up audit of the explicitly linked Poincaré endgame distinguishes genuine upstream construction from local portability and geometric adapter work.
