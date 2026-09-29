# Local compatibility changes

The original source hashes are recorded in `upstream-manifest.json`.

- `lakefile.toml`: use the parent project's Lean/mathlib 4.32.2 dependency; disable the
  upstream umbrella as a default target because only the declared endpoint closure is present.
- `DifferentialGeometry/Bundle/TangentSpace.lean`: expand `mvfderiv` and use the available
  `MDifferentiableAt.mfderiv` chart formula; the newer `.mvfderiv` lemma is absent locally.
- `DifferentialGeometry/Tensor/Alternating/Shuffle/Derivative.lean`: close two reflexive
  permutation-sign goals explicitly after simplification on mathlib 4.32.2.
- `DifferentialGeometry/Tensor/Multilinear/Bundle/Defs.lean`: mark the additive-monoid and
  module instance aliases reducible so the local elaborator can compare inherited structures.
- `DifferentialGeometry/Tensor/Multilinear/Bundle/Fiber.lean`: construct an additive-group
  instance extending the displayed bundle monoid before the original normed instances;
  explicitly import bounded-convergence topology. This aligns the structure projections
  needed by continuous currying while preserving the original normed structures.
  All original theorem statements remain present.
- `DifferentialGeometry/Tensor/RSTensor/Defs.lean`: construct model normed instances
  directly from Mathlib's canonical multilinear/linear-map structures, make their
  aliases reducible, reuse the proved bundle currying equivalence, and use `congr!`
  for the topology-dependent type equality. This avoids instance diamonds and a
  unification timeout without changing theorem statements or heartbeat limits.
- `DifferentialGeometry/Tensor/Alternating/Wedge.lean`: use `pow_succ` directly at
  three integer-unit sign recursions, avoiding incompatible simplifier normal forms.
- `DifferentialGeometry/Analysis/InnerProductSpace/Laplacian.lean`: use the local
  name `ENat.coe_ne_top` in the finite-regularity neighborhood argument.
- `DifferentialGeometry/Bundle/Equiv.lean`: use `LinearEquiv.ofLinear` for the
  equivalence constructed from mutually inverse fiber maps. The local API's
  argument order and inverse equations agree with the upstream construction.

## Set-predicate API backport

The six replacement names were verified in `/tmp/hgt-dg-set-api.lean` on the local
toolchain. Every source occurrence was inspected before this mechanical rename.
`Set.ofPred` becomes `setOf`; its membership, preimage, membership-set, existential
and universal lemmas use their `setOf` names. Proof statements and logic are unchanged.
All affected modules pass the final 1,284-module dependency build.

- `DifferentialGeometry/Analysis/Calculus/AbsolutelyContinuous.lean` (3 replacements).
- `DifferentialGeometry/Analysis/Elliptic/ComplexPlane/LogarithmicPotential/Distribution.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Elliptic/Regularity/Hessian/Pairing/LaplacianDomain.lean` (5 replacements).
- `DifferentialGeometry/Analysis/Elliptic/Regularity/Hessian/SmoothCase/LpClass.lean` (3 replacements).
- `DifferentialGeometry/Analysis/Elliptic/Regularity/Hessian/SmoothCase/PairingIdentification.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Chart/VariationalData.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Integration/BallBoundary.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Global/Support.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Integration/Measure/Chart/MeasureComparison.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Integration/Measure/LocalRestriction.lean` (2 replacements).
- `DifferentialGeometry/Analysis/Integration/Measure/Riemannian/Invariance.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Integration/Measure/Riemannian/Properties.lean` (1 replacements).
- `DifferentialGeometry/Analysis/ODE/Flow/LinearODE/Continuity.lean` (3 replacements).
- `DifferentialGeometry/Analysis/ODE/Flow/Uniqueness.lean` (1 replacements).
- `DifferentialGeometry/Analysis/Spectral/Scalar/Enumeration.lean` (1 replacements).
- `DifferentialGeometry/External/DeGiorgi/BallExtension.lean` (2 replacements).
- `DifferentialGeometry/Geometry/Connection/ChartFrame/RicciIdentitySmoothFrame.lean` (1 replacements).
- `DifferentialGeometry/Geometry/Exponential/GaussLemma/Basic.lean` (1 replacements).
- `DifferentialGeometry/Geometry/Geodesic/Flow/VectorField.lean` (2 replacements).
- `DifferentialGeometry/Geometry/Geodesic/Maximal/Rescaling.lean` (1 replacements).
- `DifferentialGeometry/Geometry/Metric/Comparison/DistanceScaling.lean` (1 replacements).
- `DifferentialGeometry/Geometry/Metric/Scaling.lean` (3 replacements).
- `DifferentialGeometry/Topology/Homology/CubeLocalHomology.lean` (2 replacements).
- `DifferentialGeometry/Topology/Homology/HurewiczOnePathLoopBridge.lean` (6 replacements).
- `DifferentialGeometry/Topology/Homology/RayComplementCoverEvaluation.lean` (1 replacements).
- `DifferentialGeometry/Topology/Homology/TetrahedronBoundary.lean` (9 replacements).
- `DifferentialGeometry/Topology/Homology/TriangleRayComplement.lean` (9 replacements).
- `DifferentialGeometry/Topology/Homotopy/CubeInterior.lean` (1 replacements).
- `DifferentialGeometry/Topology/Simplex/BallCoordinates.lean` (1 replacements).
- `DifferentialGeometry/Topology/Simplex/BoundaryRetraction.lean` (2 replacements).
- `DifferentialGeometry/Topology/Simplex/FaceLocalHomeomorph.lean` (1 replacements).
- `DifferentialGeometry/Topology/Simplex/RelativeHomology.lean` (2 replacements).
- `DifferentialGeometry/Topology/Simplex/Skeleton.lean` (1 replacements).

## Local-frame coefficient API backport

All seven Mathlib names were verified in `/tmp/hgt-dg-frame-coeff-api.lean`; the
complete `Bundle/Section.lean` replacement also passed a scratch check. Every
source occurrence was inspected. Use the local `localFrame_coeff` spelling
and corresponding regularity, expansion and evaluation lemmas. Upstream-owned
`localFrameCoeff_extDeriv_contMDiffAt` theorem names are preserved.

- `DifferentialGeometry/Bundle/Section.lean` (4 replacements).
- `DifferentialGeometry/Geometry/Connection/LeviCivita/Curvature/Identities.lean` (1 replacements).
- `DifferentialGeometry/Geometry/Connection/LeviCivita/Smooth/MetricFlatBasis.lean` (6 replacements).
- `DifferentialGeometry/Geometry/Connection/LocalFrameRegularity.lean` (64 replacements).
- `DifferentialGeometry/Geometry/Coordinates/NablaComponents/OneForm/Smoothness.lean` (6 replacements).
- `DifferentialGeometry/Geometry/Curvature/Components/Christoffel.lean` (4 replacements).
- `DifferentialGeometry/Geometry/Curvature/CurvatureOperator/Sections.lean` (4 replacements).
- `DifferentialGeometry/Geometry/Curvature/Riemann/Basic/Field.lean` (4 replacements).

- `Tensor/Multilinear/Bundle/TensorProduct.lean`: prove bilinearity and section product-zero pointwise, avoiding instance-sensitive model-coordinate simplification on Mathlib 4.32.2. Full-file scratch check passed.

- `Tensor/Multilinear/Bundle/DomainPermutation.lean`: zero and addition compatibility use their definitional pointwise equalities rather than instance-sensitive simplification.

- `External/CanonicalTopology/Topology/LoopSpace/SimplyConnectedTarget.lean`: replace newer `Joined.map` syntax with explicit `Nonempty.map` of `Path.map`; full-file scratch and local `Path.map` API check passed.

- `Geometry/Connection/Realization/Embedding.lean`: both newer `MDifferentiableAt.mvfderiv` calls use the already-ported `mvfderiv_apply_eq_fderivWithin_writtenInExtChartAt` evaluation lemma. Remove a trailing `rfl` after `L.fderiv` already closes the linear-map evaluation identity.

- `Geometry/Connection/TensorNabla/FixedChart/Nabla0S.lean`: remove two trailing `rfl` steps after simplification already closes their goals on Mathlib 4.32.2.

- `Bundle/PartialMfderiv/Basic.lean`: omit a trailing `rfl` after the preceding simplification closes the bracket equality on Mathlib 4.32.2.

## Continuous restriction API backport

Backported 29 inspected uses in 16 modules: `continuousOn_iff_continuous_domRestrict` → `continuousOn_iff_continuous_restrict`, `ContinuousOn.domRestrict` → `ContinuousOn.restrict`, and `Set.domRestrict` → `Set.restrict`. All three local APIs passed minimal scratch checks.

- `DifferentialGeometry/Bundle/Orientation/Cover.lean`
- `DifferentialGeometry/Bundle/Orientation/Transport.lean`
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalCharts.lean`
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalCompactHomology.lean`
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalDerivativeComparison.lean`
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalOrientation.lean`
- `DifferentialGeometry/Geometry/Connection/ChartFrame/RicciIdentitySmoothFrame.lean`
- `DifferentialGeometry/Geometry/Exponential/Defs.lean`
- `DifferentialGeometry/Geometry/Measure/Area/ManifoldMeasurable.lean`
- `DifferentialGeometry/Geometry/Metric/Family/Basic.lean`
- `DifferentialGeometry/Geometry/Metric/TensorInner/Fiber/CoerciveBilinearInverse.lean`
- `DifferentialGeometry/Topology/ClosedCover.lean`
- `DifferentialGeometry/Topology/Homology/LocalGerm.lean`
- `DifferentialGeometry/Topology/Homotopy/OpenCollapseLocalHomeomorph.lean`
- `DifferentialGeometry/Topology/Simplex/BoundaryGluing.lean`
- `DifferentialGeometry/Topology/Simplex/FaceLocalHomeomorph.lean`

- `Bundle/TangentSpace.lean`: add `DifferentialGeometry.mvfderiv_comp_apply`, proved from local `mfderiv_comp` and the definition of `mvfderiv`. The independent scratch/API check and standard-axiom audit pass; this supplies all four newer chain-rule calls in scalar calculus and tangent realization without strengthening hypotheses.

- `Geometry/Operator/Hessian/Trace/Realization.lean`: remove a trailing `rfl` after Mathlib 4.32.2 simplification already proves the differential evaluation identity.

- `Bundle/TangentSpace.lean`: add `DifferentialGeometry.mvfderivWithin_comp` from the local `mfderivWithin_comp`; the independent scratch/API check and standard-axiom audit pass. This supplies the derivative-within-set chain rule used in `Geometry/Operator/Laplacian/Minimum.lean` with unchanged hypotheses.

- `External/CanonicalTopology/Topology/Homology/AffineChains.lean` and `Topology/Homology/Subdivision/Cone.lean`: prove the two finite-tuple face identities locally by `Fin.cases` and simplification, replacing the newer `Fin.cons_comp_succ_succAbove` and `Fin.cons_comp_succ` APIs. The general tuple identity passed an independent scratch check and standard-axiom audit. Remove the now-redundant final `rfl` in `AffineChains`.

- `External/CanonicalTopology/Topology/Homology/OpenExcision.lean`: pass the already-proved small-relative comparison explicitly as `quasiIso_comp`'s second quasi-isomorphism argument. This avoids a local instance-inference failure without changing assumptions. The complete file passed a scratch check and standard-axiom audit.

- `Topology/Homotopy/LoopTopology.lean`: replace two newer `Joined.map` calls by `Nonempty.map` of explicit `Path.map` witnesses; unfold `Joined` in the inverse-homeomorphism simplification. Full-file scratch, `Path.map` API check, and standard-axiom audit pass.

- `Topology/Homotopy/CubeCompactification.lean`: the same two path-witness replacements and explicit `Joined` unfolding pass a full-file scratch check and standard-axiom audit.
- `Topology/Homotopy/TransportContinuity.lean` and `Topology/VanKampen/SelectedObjects.lean`: four further inspected `Joined.map` calls use explicit path witnesses. Both full-file checks pass in the dependency-sensitive build. The superficially similar uses in `SphereNaturality` and `SpherePrecomposition` already receive actual `Path` arguments through local `ZerothHomotopy.lift` and remain unchanged.

- `External/CanonicalTopology/Topology/Homology/RelativeFunctoriality.lean`: after left reassociation, rewrite the quotient-projection composite with the unassociated lemma. Full-file scratch check and standard-axiom audit pass; theorem statements are unchanged.

- `External/CanonicalTopology/Topology/Homology/LocalCharts.lean`: remove the trailing `rfl` after simplification already proves chart naturality on Mathlib 4.32.2. Full-file scratch check and standard-axiom audit pass.

- `Geometry/Flow/RicciFlow/Surgery/Topology/LinearOrientation.lean`: four upper-triangular predicates use the equivalent `BlockTriangular id`, with the local `det_of_upperTriangular` and `gramSchmidtOrthonormalBasis_inv_blockTriangular` lemmas. The local API probe, complete scratch file, and standard-axiom audit of `positive_linear_homotopy` pass. Its public statement is unchanged.

- `External/CanonicalTopology/Topology/Homology/RelativeMayerVietoris.lean`: close the biproduct equality by reflexivity, and use explicit congruence of quotient and homology maps where the older rewriter cannot cross reducible carrier aliases. Complete-file scratch check and standard-axiom audit pass; public hypotheses and statements are unchanged.

- `Topology/Algebra/Group/AmalgamatedProduct.lean`: apply `Monoid.PushoutI.of_apply_eq_base` directly for the identity leg; definitional equality handles the identity homomorphism where the older simplifier did not. Complete scratch and standard-axiom checks pass.

- `Topology/VanKampen/Based.lean`: remove the trailing `rfl` after simplification proves pointed delooping naturality on Mathlib 4.32.2. Full-file scratch and standard-axiom checks of both the delooping identity and the fundamental-group pushout theorem pass.

- `Topology/VanKampen/AmalgamatedProduct.lean`: three homomorphism equalities use direct proof terms, preserving definitional carrier and group aliases across Mathlib 4.32.2 elaboration. Full-file scratch and standard-axiom audit of `fundamentalGroupEquivAmalgamatedProduct` pass; statements unchanged.

- `Topology/Homology/Algebra/EulerCharacteristic.lean`: explicitly expose the definitionally equal integer alternating sums before applying the rank telescope. This avoids residual unit casts in the older simplifier. Full-file scratch and standard-axiom audit pass, with unchanged hypotheses.

- `Topology/Homology/Algebra/ExactSequenceEuler.lean`: the same explicit integer-sign target makes the exact-sequence alternating-sum identity available to linear arithmetic. Full-file scratch and standard-axiom audit of `homologyEulerChar_additive` pass.

- `Topology/Homology/EulerCharacteristic.lean`: reflexivity identifies integer powers with the values of unit powers in the finite Euler sum. Full-file scratch and standard-axiom audit pass. The exhaustive `ComplexShape.χ` source search found no further uses after these three Euler backports.

- `Topology/Homology/Algebra/CokernelHomotopy.lean`: use the general `dif_pos` simplification rule in both degree cases, allowing the older rewriter to discharge the normalized `True` condition. Complete scratch and standard-axiom checks pass.

- `Topology/Homology/Subdivision/Cone.lean`: remove the redundant final `rfl` after rewriting subtraction closes the backported cone boundary identity. The full file and standard-axiom audit of `affineCone_boundary` pass.

- `Topology/Homology/Subdivision/{Homotopy,Restriction,Singular,SingularSupport}.lean`: eight inspected chain-homotopy degree cases use general `dif_pos` simplification, matching the checked cokernel-homotopy backport. Explicit projection rewrites using `dif_pos rfl` remain unchanged. All four complete modules pass the dependency-sensitive normal build.

- `Topology/SimplicialSet/ChainColimits.lean`: prove preservation of monomorphisms degreewise using the existing constant-coproduct functor instance, avoiding ambiguous higher-functor elaboration. Its complete dependency-sensitive build and local-toolchain API probe pass.

- `Topology/Homology/Algebra/PushoutExact.lean`: explicitly reassociate and reduce biproduct projections in the cokernel universal property. The local API probe and complete dependency-sensitive build pass.

- `Topology/Manifold/Orientation.lean`: after rewriting the derivative of identity, use definitional evaluation of the identity continuous linear map. The complete dependency-sensitive build passes.

- `External/DeGiorgi/Common.lean`: replace `import Mathlib` with 30 dependency-directed Mathlib imports, retaining the tactic umbrella. The list comes from actual compiled constants in all 75 then-checked descendants, reduced using Lean's import graph. The standalone prelude probe passes and loads 5,295 modules rather than the roughly 10,400-module Mathlib closure. The file has no mathematical declarations. All 302 descendants in the selected closure now compile with the reduced imports, including both final analytic endpoints. The original manifest still records the upstream import and hash.

- `Analysis/Sobolev/Nirenberg/MasterInequality/CrossBounds.lean` and `Analysis/Elliptic/Regularity/ChartBilinear/UniformDiffQuotBoundFromDomain/DataBounds.lean`: explicitly import `Mathlib.MeasureTheory.Function.L2Space` for `MemLp.integrable_sq`, previously supplied by the Mathlib umbrella. The local-toolchain API probe passes. All 16 uses in seven modules were checked by dependency: six modules are the first file or its descendants, while the independent data-bounds branch also lacked the import in a targeted probe. Both complete modules pass the strict dependency build. No theorem body or assumption changes.

- `Analysis/Spectral/Tensor/CovGrad/Product/Scalar.lean`: prove scalar-product compact support directly with `HasCompactSupport.mono`. The compact-set argument on Lean 4.32.2 inadvertently captured `CompactSpace` and `SigmaCompactSpace` instances in `scalarSmul`, preventing six subsequent lemmas from omitting them. Direct support inclusion removes those dependencies and the unnecessary `T2Space` dependency; the two evaluation lemmas omit their now-unused `T2Space` variable. Scalar multiplication itself and all conclusions are unchanged, with no added hypotheses. The complete scratch file and three standard-axiom audits pass without warnings. No explicit `@scalarSmul` or `@scalarSmul_toSection_apply` call sites were found in the vendored closure.

- `Geometry/Connection/SourceSectionPairing.lean`: explicitly close the residual chart-representation equality by reflexivity after simplification. The complete scratch file and the standard-axiom audit of `sourceSectionCovariantDerivative_chart` pass without warnings. Statements, hypotheses and existing compiler options are unchanged.

- `Geometry/MinimalSurface/Plateau/DiskBoundaryAcceleration.lean`: restate the post-rewrite sum in the canonical tangent fibre at `U (c θ)` before bilinear simplification. This removes the older simplifier's mixed `U (c θ)` / `(U ∘ c) θ` fibre expression. Full-file scratch compilation and the standard-axiom audit pass without warnings. No assumptions or compiler settings change.

- `Geometry/Comparison/Variation/Covariant/TwoParameterFields.lean`: use direct proof terms at three product-model alias boundaries and remove a trailing reflexivity step already closed by simplification. The complete scratch file and four standard-axiom audits, including curvature commutation and the Jacobi variation equation, pass without warnings. No statement, hypothesis or compiler option changes.

- `Geometry/Metric/CurveUnitReparametrization.lean`: explicitly restate both post-chain-rule targets in the tangent fibre at `γ (φ t)` before bilinear and scalar-multiplication rewrites. Both reparametrization theorems pass a complete scratch check and standard-axiom audit, without warnings. Statements, assumptions and compiler options are unchanged.

- `Geometry/Curvature/CurveReparametrization.lean`: explicitly normalize the post-chain-rule covariant derivative to the tangent fibre at `γ (φ t)` before combining scalar multiplications. The complete scratch file and standard-axiom audit pass without warnings. No statement, hypothesis or compiler option changes.

- `Geometry/Curvature/DiskBoundary.lean`: unfold curve speed, rewrite zero velocity explicitly, and restate both zero vectors in the canonical boundary-point tangent fibre before simplification. The complete scratch file and standard-axiom audit of `diskMapBoundaryCurvature_density` pass without warnings. Statements, assumptions and compiler options are unchanged.

- `Geometry/Metric/LocalChartDistance.lean`: use Mathlib 4.32.2 `setOf_riemannianEDist_lt_subset_nhds` and explicitly expose the composed chart-derivative application before rewriting its trivialization. The complete scratch file, local API probe and both standard-axiom audits pass without warnings. The exhaustive vendored search found only this remaining `setOfPred_` identifier. No assumptions, statements or compiler settings change.
