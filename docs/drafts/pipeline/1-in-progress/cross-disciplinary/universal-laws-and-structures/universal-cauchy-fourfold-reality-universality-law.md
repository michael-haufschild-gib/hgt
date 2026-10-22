# Universal Cauchy fourfold-reality universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `universalCauchyRealKrylovPointwiseRecovery_iff_all_real`: real reciprocal-Krylov recovery is
  equivalent to pointwise reality on any conjugation-stable regular family.
- `cauchyQuartetVariance_eq_zero_iff`: a regular quartet variance vanishes exactly on the union of
  the real and imaginary axes.
- `cauchyQuartetVariance_nonneg`: all quartet variances are nonnegative.
- `tsum_cauchyQuartetOrientationTerm_eq_variance`: the complete orientation response is a nonzero
  probe scalar times total quartet variance.

These statements use the same spectral family and Cauchy coordinate. Excluding the imaginary axis
removes the extra zero branch of the quartet variance; choosing a probe off both axes makes its
orientation scalar faithful. Corpus research found no theorem joining the algorithmic real-Krylov
criterion to the scalar quartet-orientation criterion.

## Universal law

For every finite conjugation--negation invariant regular family with nonzero real parts and every
regular Cauchy probe off both axes, the following conditions are equivalent:

1. one common sequence of real reciprocal polynomials recovers every conjugate-adjoint response;
2. every spectral point is real;
3. every quartet variance vanishes;
4. the total one-probe orientation response vanishes.

The same theorem records the exact orientation-response decomposition.

## Paper proof

Real-Krylov descent gives (1) iff (2). The quartet zero classification, with the imaginary-axis
branch excluded, gives (2) iff (3). Nonnegativity makes zero total variance equivalent to termwise
zero. The exact quartet decomposition and the nonzero probe scalar identify zero total variance
with (4). No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.UniversalCauchyFourfoldRealityUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
