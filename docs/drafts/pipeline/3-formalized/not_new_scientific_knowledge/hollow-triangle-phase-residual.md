# Hollow-triangle phase residual

- **ID:** `hollow-triangle-phase-residual`
- **Stage:** 3-formalized
- **Type:** exact no-go / positive orbit classification
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED/BRIDGE]`
- **Parent:** `../../1-in-progress/source-generated-ternary-reciprocity-law.md`
- **Lean target:** `GaloisForLFunctions.HTGeometry.HollowTrianglePhaseResidual`

## Exact theorem

Let \(u_0,u_1,u_2\in\mathbb C\) satisfy the three hollow-triangle
pair-normalization equations
\[
|u_0|^2+|u_1|^2=1,\qquad
|u_1|^2+|u_2|^2=1,\qquad
|u_2|^2+|u_0|^2=1.                                      \tag{1}
\]
Then
\[
|u_0|^2=|u_1|^2=|u_2|^2=\frac12.                        \tag{2}
\]
Conversely, multiplication of any fixed half-intensity radius by three arbitrary unit complex
phases preserves `(1)`.

For unit phases \(z_0,z_1,z_2\), define
\[
R(z_0,z_1,z_2)
=\left(\overline z_0z_1,\overline z_0z_2\right).         \tag{3}
\]
Two phase triples have the same value of \(R\) exactly when they differ by multiplication by one
common unit phase.  Thus the orbit is completely classified by two relative phases.  This is the
algebraic content of
\[
\mathbb T^3/\mathbb T\cong\mathbb T^2.                   \tag{4}
\]

## Meaning and boundary

Pairwise compatibility fixes positive diagonal weights but does not fix comparison.  Static
normalization therefore cannot select a unique ternary carrier, gauge comparison, connection, or
physical law.

The theorem is elementary complex algebra.  It does not prove contextuality, derive
\(M_{2,3}(\mathbb C)\), select the Standard Model, or identify the residual phases with physical
gauge fields.  Its scientific use is as an exact minimal instance of the comparison-nonselection
obstruction.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.HollowTrianglePhaseResidual`
- **Definitions:** `HollowTrianglePairNormalized`,
  `hollowTriangleRelativePhases`, `HollowTriangleCommonPhaseEquivalent`
- **Theorems:** `hollowTriangle_intensity_rigidity`,
  `hollowTriangle_normSq_rigidity`,
  `hollowTriangle_independent_unit_phases`,
  `hollowTriangleRelativePhases_common_invariant`,
  `hollowTriangle_relativePhases_complete`
- **Direct check:** passed with
  `lake env lean GaloisForLFunctions/HTGeometry/HollowTrianglePhaseResidual.lean`
- **Target build:** passed with
  `lake build GaloisForLFunctions.HTGeometry.HollowTrianglePhaseResidual`
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`
- **Repository lint:** new module is reachable from `HTGeometry`; full lint remains red on
  pre-existing/concurrent unreachable modules outside this card
- **Excluded:** topological construction of the quotient, physical interpretation, and every
  spacetime or force claim

## Log

- 2026-07-30 — exact intensity and common-phase orbit classification proved on paper and in Lean.
