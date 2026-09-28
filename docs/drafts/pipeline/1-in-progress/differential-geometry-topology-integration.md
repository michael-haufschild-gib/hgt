# DifferentialGeometry topology integration

- **ID:** differential-geometry-topology-integration
- **Stage:** 1-in-progress
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
- [ ] Formalize circle fundamental group and map infrastructure.
- [ ] Classify determinant-induced finite-unitary fundamental groups; prove stabilization injectivity.
- [ ] Prove global special-unitary nullhomotopy and simple connectivity.
- [ ] Prove sphere simple connectivity and concrete covering consequences.
- [ ] Wire umbrella, audit axioms, run final leaf checks and formal lint; document unrelated failures precisely.

## Paper proof

1. The quotient cover ℝ → ℝ/ℤ has contractible total space and deck group ℤ. The standard circle homeomorphism identifies its basepoint with 1, giving π₁(S¹,1) ≃ ℤ.
2. Let dₙ : U(n) → S¹ be determinant. For n=1 it is a homeomorphism, with inverse the one-entry diagonal matrix. For each positive n, existing local two-chart loop decomposition proves that block stabilization U(n) → U(n+1) induces a surjection on π₁. Determinant commutes with this block stabilization. Inductively dₙ induces an injection: lift two loop classes along stabilization, compare their determinants, and apply injectivity one dimension below. The diagonal determinant section proves surjectivity. Thus dₙ induces an isomorphism for every n≥1, and stabilization is an isomorphism as well.
3. Existing normalization r(U)=U D(det U)⁻¹ continuously retracts U(n) onto SU(n). The inclusion of any SU(n) loop has constant determinant, hence is nullhomotopic by injectivity of dₙ. Compose its nullhomotopy with r to contract the original loop inside SU(n). Translation moves any basepoint to 1; existing path connectedness then gives simple connectivity. The zero-dimensional group is a singleton and is handled separately. No logarithm chart, radius, phase or selected nullhomotopy is assumed.
4. For a real unit sphere in dimension n+3, complements of antipodal points are contractible by stereographic projection. Their intersection is homeomorphic to the punctured orthogonal complement, of dimension n+2≥2, hence path connected. Existing local open-cover loop decomposition contracts loops in the union. Path connectedness and basepoint transport give simple connectivity of the full sphere. This is the upstream sphere proof mechanism, with arbitrary finite dimension and local loop-decomposition infrastructure replacing its separate van Kampen stack.
5. Existing local injectivity of connected covers over simply connected bases now applies to these concrete spaces, removing the abstract simple-connectivity premise from those instances.

## Audit boundaries

- The Poincaré statement in `Topology/ThreeManifold/Poincare.lean` uses ordinary Mathlib charted manifold, compactness, Hausdorffness and simple connectivity. Earlier blanket dismissal of upstream topology was unsupported.
- The complete Ricci-flow/Moise dependency closure has not been compiled locally; do not claim that it has been audited or imported.
- These classical topology results are **not new scientific knowledge**. Integration value is explicit premise discharge and stronger local classifications.
- Preserve unrelated dirty worktree changes. No full/umbrella build, heartbeat changes, computational certificates, new axioms or proof holes.

## Log

- 2026-09-28 — Created after read-only investigation and adversarial proof review.
