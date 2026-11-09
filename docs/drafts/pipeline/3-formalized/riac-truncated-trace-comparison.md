# Finite trace data determine signed reciprocal coefficients

- **ID:** RIAC-truncated-trace-comparison
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Actual curve cancellation](riac-curve-orientation-square-root.md)
- **Lean:** [TruncatedTraceComparison.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/TruncatedTraceComparison.lean)

## Finite-degree identity

Let `M` be any finite complex matrix and `α` a finite root family. If
`Tr(M^d)=q^d+1−Σ_i α_i^d` for `1≤d≤n`, then

`[t^n]det(1+tM) = [t^n](1+t)(1+qt)∏_i(1+α_i t)⁻¹`.

The [actual hyperelliptic theorem](riac-curve-orientation-square-root.md)
discharges every trace input from independently counted fixed points.
The matrix theorem alone does not supply those arithmetic identities.

## Proof

Schur triangulation produces one multiset `Λ`, with multiplicities,
realizing both `det(1+tM)=∏_(λ∈Λ)(1+λt)` and all trace power sums.
The multisets `Λ+Α` and `1::q::∅` have equal positive power sums through
`n`. Newton's triangular recursion identifies their elementary symmetric
functions through `n`, without equal cardinalities or simple roots.

Their elementary polynomials therefore agree through `n`. Multiplying
by the reciprocal root series preserves agreement through that degree
and gives the stated coefficient. For root radius `t≥1`, the explicit
coefficient norm is at most `(2q+2)(n+1)^(#Α)t^n`.

## Principal declarations

- `esymm_eq_of_powerSums_through` and `elementaryPolynomial_coeff_eq_through`.
- `exists_matrix_root_multiset` and `matrix_root_product_coeff_through`.
- `coeff_mul_eq_through`, `elementaryPolynomial_coe_curveP`,
  `curveP_mul_curvePinv`.
- `matrixOrientationPolynomial_coeff_curveZinv` and
  `norm_coeff_signed_curveZinv_le`.

Direct Lean check and 16 transitive axiom audits: only `propext`,
`Classical.choice`, `Quot.sound`.

## Boundary

The comparison is through a specified finite degree. It does not promote
finite-field trace data to a global determinant identity or an integer
cutoff estimate.
