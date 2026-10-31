# Integral power-series coefficients are closed under inversion

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** Coefficient-integral power series form a subring closed under
  inversion of principal units. Coefficient-integral determinant-one matrices
  form a subgroup, and constant reduction is integral.

## Proof

The valuation integers form an integer subalgebra of the coefficient field.
Apply the existing coefficient-subalgebra construction: sums and products
stay integral because each output coefficient is a finite sum of products.
For a series with constant term one, the audited inverse-coefficient recursion
uses only addition, subtraction and multiplication in this subalgebra, so
its inverse has integral coefficients. Multiplication by `X` shifts the
coefficients and preserves the integral condition in both directions.

Matrix multiplication uses sums of products in the same coefficient subring.
The inverse of a determinant-one matrix of size two is its adjugate, whose
entries are signed original entries. Thus these matrices form a subgroup.
Taking coefficient zero preserves the integral bounds in every entry.
If either off-diagonal residue is zero, the two diagonal residues multiply
to one. Their valuations are each at most one, so each equals one.

## Lean

`HTGeometry/LoopEisenstein/IntegralPowerSeriesCoefficients.lean`:
`invOfUnit_mem_integralPowerSeriesCoefficients`,
`X_mul_mem_integralPowerSeriesCoefficients_iff`,
`integralPowerSeriesSL2_constant_reduction`,
`integralPowerSeriesSL2_diagonal_values`. Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`,
`Quot.sound`.
