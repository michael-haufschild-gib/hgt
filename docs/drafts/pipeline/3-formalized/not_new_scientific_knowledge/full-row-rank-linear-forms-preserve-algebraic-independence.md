# Full-row-rank linear forms preserve algebraic independence

- **ID:** `full-row-rank-linear-forms-preserve-algebraic-independence`
- **Stage:** 3-formalized
- **Type:** ALGEBRAIC RANK BRIDGE
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [STANDARD PARENT THEORY]`
- **Statement:** Let `M` be a finite matrix over a field.  If its rows are linearly independent and
  `x` is an algebraically independent family in an algebra over that field, then the row linear
  forms `M x` are algebraically independent.

## Proof mechanism

Row independence gives full row rank.  The matrix linear map is therefore surjective and admits a
right inverse `N`, so `M N=1`.  Substitution of the row linear polynomials of `M` into a
multivariate polynomial has substitution by `N` as a left inverse.  A polynomial relation among
the evaluated row forms would therefore induce a relation among `x`; algebraic independence makes
the first substituted polynomial zero, and the left inverse makes the original relation zero.

## Lean realization

`GaloisForLFunctions.HTGeometry.AlgebraicIndependentLinearForms` proves:

- `aeval_toMvPolynomial_eq_matrixLinearForms`;
- `algebraicIndependent_matrixLinearForms_of_mul_eq_one`;
- `exists_matrix_rightInverse_of_linearIndependent_rows`;
- `algebraicIndependent_matrixLinearForms_of_linearIndependent_rows`.

## Boundary

This is the finite algebraic core of the facet-sewn differential Smith/rank lemma.  It does not yet
prove that polynomial differential-operator row independence makes every finite Toeplitz packet of
shifted output jets full row rank.  That differential lift remains part of the Stage 2 facet-sewn
card.

## Gates

- [x] complete paper proof
- [x] complete unconditional Lean formalization
- [x] no independent novelty claim
