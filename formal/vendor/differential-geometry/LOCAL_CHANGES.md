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
Endpoint compilation of the affected closure remains in progress.

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
