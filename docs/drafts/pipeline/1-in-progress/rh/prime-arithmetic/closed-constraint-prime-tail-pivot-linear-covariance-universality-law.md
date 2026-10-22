# Closed-constraint prime tail-pivot linear covariance universality law

- **ID:** closed-constraint-prime-tail-pivot-linear-covariance-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of closed-constraint prime tail-pivot completeness,
  entrywise-constant finite-shadow jet covariance, and invertible jet automorphisms
- **Statement:** Every finite tail-linear extension of a coordinate-independent sparse
  closed-constraint prime chart retains its complete differential relation classification after
  every invertible linear coordinate change whose actual matrix entries are differential
  constants.  Membership in the changed-family relation ideal is equivalent to membership of the
  contravariantly transformed polynomial in the original explicit pivot ideal.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `closedConstraintPrimeTailPivot_completeFiniteExtension`
- `differentialJet_matrixLinearForms_of_coefficients_constant`
- `differentialJetLinearChangeAlgEquiv`
- `differentialPolynomialEval_linearChange`
- `mem_differentialRelationIdeal_linearChange_iff`

## Proof

`[PROVED HERE]` First strengthen formal linear-change evaluation from a globally constant
coefficient field to
the necessary entrywise condition on the displayed matrix.  The finite-shadow jet identity then
shows that evaluating a polynomial after jetwise matrix substitution equals evaluating it on the
linearly changed analytic family.  For a two-sided inverse matrix this gives contravariant
relation-ideal covariance.  Finally substitute the closed-constraint prime theorem's exact
relation-ideal equality.  No computation is used.

## Strict gain over corpus endpoints

The generic covariance theorem assumes every element of the polynomial coefficient field is
differentially constant, which is false for the finite-prime rational coefficient field.  The
closed-constraint theorem classifies only its native pivot/dependent coordinates.  Their closure
gives the first correct covariance theorem for the concrete sparse-prime relation circuit over
that genuinely differential coefficient field.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ClosedConstraintPrimeTailPivotLinearCovarianceUniversalityLaw`
- Main theorem:
  `closedConstraintPrimeTailPivot_linearCovariantCompleteRelation`
- Source:
  `formal/GaloisForLFunctions/RHTower/ClosedConstraintPrimeTailPivotLinearCovarianceUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/ClosedConstraintPrimeTailPivotLinearCovarianceUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
differential relation ideals, constant-matrix differential polynomial automorphisms, and
finite-prime Dirichlet coefficient relations found general work on differential
Nullstellensätze, automorphism groups of differential polynomial rings, and Dirichlet-series
algebras, but no closed-constraint sparse-prime tail-pivot ideal and no exact contravariant
coordinate-covariance law.  Closest inspected primary sources:

- L. D'Alfonso, G. Jeronimo, and P. Solernó, *Effective Differential Nullstellensatz for Ordinary
  DAE Systems with Constant Coefficients*, <https://arxiv.org/abs/1305.6298>.
- B. Duisengalieva, A. Naurazbekova, and U. Umirbaev, *Tame and wild automorphisms of differential
  polynomial algebras of rank 2*, <https://arxiv.org/abs/2001.00375>.
- A. Brudnyi and A. Sasane, *On algebras of Dirichlet series invariant under permutations of
  coefficients*, <https://arxiv.org/abs/2404.03616>.

## Log

- 2026-07-23 — Terminal cross-folder scan exposed prime tail-pivot completeness versus linear jet
  covariance.
- 2026-07-23 — Inspection rejected globally constant finite-prime rational coefficients and
  isolated the exact entrywise-constant replacement already supported by the finite-shadow corpus.
- 2026-07-23 — Dependency-closed proof and exact Lean check passed warning-free; module wired into
  the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
