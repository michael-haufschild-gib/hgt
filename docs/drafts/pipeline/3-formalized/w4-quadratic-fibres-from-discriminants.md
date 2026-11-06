# W4 — quadratic fibres from discriminants

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** The exact odd- and even-dimensional affine quadratic distributions hold for every nonsingular symmetric matrix over an odd finite field, with determinant replacing the product of diagonal coefficients.

## Proof

The symmetric matrix is exactly the associated matrix of its quadratic form. Its nonzero determinant gives nondegeneracy. An actual linear isometry identifies the form with a weighted sum of squares having nonzero coefficients, hence identifies every finite fibre.

Under this change of coordinates, the discriminant is multiplied by the square of the coordinate determinant. That determinant is nonzero because the original discriminant is nonzero. The quadratic character of its square is one. Substitution into the [diagonal distributions](w4-diagonal-quadric-counts.md) proves the formulas.

## Lean

[`QuadraticFormCounts.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/QuadraticFormCounts.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `quadraticFormCount_isometry`: actual affine fibre counts are isometry-invariant.
- `symmetricMatrix_quadratic_toMatrix`: exact associated matrix.
- `quadraticFormCount_diagonal_model`: diagonalization preserves counts and discriminant character.
- `quadraticFormCount_odd`, `quadraticFormCount_even`: discriminant formulas.
- `symmetricMatrix_quadraticCount_odd`, `symmetricMatrix_quadraticCount_even`: concrete matrix formulas.

Direct Lean check passed. The [projective scalar quotient counts](w4-projective-quadric-counts.md) are also formalized. The actual reciprocal transverse specialization remains open. These are classical quadratic-form facts, formalized for that application.
