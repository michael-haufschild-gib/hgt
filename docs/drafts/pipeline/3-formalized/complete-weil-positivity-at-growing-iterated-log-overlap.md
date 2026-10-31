# Complete Weil positivity at growing iterated-logarithmic overlap

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/three-frontier-questions-full-solutions.md`, Q1.
- **Statement:** For every `0<α<1/16`, the complete tilted-spline Weil matrix is
  positive definite for all sufficiently large `N`, uniformly over
  `1≤c≤(log log N)^α` and every coefficient vector.

## Proof

At `N≥Hc⁸`, nonpositive unit vectors have a fixed amount of mass on conductors
`m≤exp(C(c^16+1))+2`. This cutoff is `(log N)^o(1)` in the stated range.
Uniform residue Mertens estimates control reciprocal affine shells
for conductors bounded by powers of the logarithmic source scale.

Split complementary quotients at `2c exp(√log N)`. Signed shell transfer
controls the upper range; the linear source envelope controls its complement.
One absolute constant works for every `A≥0`, with an eventual horizon
depending on `A`, for all `m≤(log N)^A` and `N≥4(e+3)²c²`.
The literal upward residual satisfies

`‖U_res‖² ≤ K φ(m)² [c⁵/log N + c¹⁰(log N/N)² + c³/√log N]`.

The complete residual has one absolute constant:

`‖W_N(c)u_m−E_m(c)u_m‖² ≤ K m⁴ [c⁵/log N+c¹⁰(log N/N)²+c³/√log N]`.

Every logarithmic conductor range shares an eventual horizon, independent
of its conductors and of overlap throughout the stated source domain.

The common conductor floor is `a/c⁷`. If both conductor cutoff and overlap
are at most `(log N)^(1/100)`, the summed squared residual divided by the
squared floor is at most `K'(log N)^(-21/100)`. The cutoff condition follows
from `16α<1`. Finite Ramanujan coordinate mass then excludes every
nonpositive eigenvector.

## Lean

Namespace `GaloisForLFunctions.CriticalArithmeticCorrelationTheory`:

- `exists_tiltedUnitSpline_uniform_conductor_residual_bound`: the common residual rate.
- `matrix_posDef_of_uniform_conductor_budget`: finite-coordinate spectral transfer.
- `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_iteratedLog`: actual matrix positivity.
- `eventually_tiltedUnitSpline_weilQuad_nonneg_iteratedLog`: the literal atomic Weil form.

Capstone: [TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap.lean](../../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap.lean).
The capstone and all five new supporting modules passed direct
`lake --old env lean` checks. Transitive axiom audits contain exactly
`propext`, `Classical.choice`, `Quot.sound`. All modules are imported by
the CACT umbrella.

This target does not identify the agreement-shell square completion and does
not settle Q2 or Q3.
