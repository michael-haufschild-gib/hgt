# Carlitz–Goss RH from greedy compositions

- **Stage:** 1-in-progress
- **Source:** review-0911 §11.4.

## Exact target

For every prime power `q=p^s`, `s>0`, and every `y∈ℤ_p`, the zeros in `x`
of the Goss zeta function of `𝔽_q[T]` are simple and belong to
`𝔽_p((T⁻¹))`. The domain for `x` is the nonzero elements of the completed
algebraic closure of `𝔽_q((T⁻¹))`.

## Proof dependencies

[Sheats, Theorems 1.1–1.4 and §2](https://arxiv.org/pdf/math/9801158):

1. Among carry-free compositions of `N`, with all but the final part
   positive and divisible by `q−1`, the reversed-lexicographic maximum
   uniquely maximizes the weighted sum of the parts.
2. Finite-field power sums and Lucas's theorem identify the leading
   coefficient of each monic-polynomial power sum. The unique maximum
   prevents cancellation.
3. Greedy-composition inequalities give strictly increasing consecutive
   coefficient valuations. For general `y∈ℤ_p`, digit truncations stabilize
   those valuations.
4. Every Newton-polygon segment has horizontal length one. Its root is
   simple and belongs to the coefficient field.

`SignFreePurityMechanisms/SeparationForcesRationality.lean` supplies a
polynomial Galois-invariance principle. The same owner's
`TheUltrametricNewtonPolygonSeparatesTheRoots.lean` proves simplicity,
separation and splitting of polynomials with strictly log-concave
coefficient norms (`HasSimpleSlopes.derivative_eval_ne_zero`,
`splits_of_strict_logConcave`). The composition theorem, actual Goss
coefficients and passage to the entire series remain necessary.

## Lean status

The actual Goss-zeta theorem and its composition input remain unformalized.
The target includes every prime power, not only prime `q` or integer `y`.
