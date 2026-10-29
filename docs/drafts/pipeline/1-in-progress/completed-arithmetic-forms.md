# Completed arithmetic forms

- **ID:** completed-arithmetic-forms
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2910/astra.md
- **Statement:** Quantitative source comparison preserving radicals, domains, cross terms, and
  endpoint precision under the required limits.

## Mathematical scope

1. Native signed theta successors from rank seven to arbitrary rank.
2. Completed macroscopic Weil overlap comparison and profile-compatible exhaustion.
3. Actual signed coalescent surplus at most \(N/18+o(N)\) in compatible windows.
4. Euler-deletion cumulative covariance and infinite-tail control at inner-cutoff scale.
5. Complete Suzuki rectangular and CCM first-clock source lower bounds.
6. Universal exclusion of actual theta-clock guarded zeros.
7. Arithmetic upper control of the complete Hecke defect or index.
8. Actual Chebyshev energy or detector Gram improvements yielding specified zero strips.
9. Quantitative source transfers without assuming the missing signs.

## Arithmetic comparison metric

For the exact divisor-conductor kernel
\[
B_Q(i,j)=\sum_{m\mid Q,\ m\ne1}G_m(i,j)=Q\min(i,j)-ij,
\qquad 0\le i,j\le Q,
\]
the completed energy satisfies
\[
4E_Q(a)=Q\bigl[(\sum_i a_i)^2+\sum_i a_i^2\bigr]+R_Q(a),\qquad R_Q(a)\ge0.
\]
The interior radical is zero. The inverse is the Dirichlet second difference divided by `Q`.
For a coupling extended by zero at both endpoints, its exact Schur cost is
`Σ_(0≤i<Q)(b_(i+1)-b_i)²/Q`, attained at the inverse coefficient vector.

Lean: `CompletedArithmeticForms/CyclotomicCoercivity.lean` and
`CompletedArithmeticForms/DirichletSchurCost.lean`.

The arithmetic estimate still required for the overlap problem identifies the actual mixed
coupling in these coordinates and controls its Dirichlet cost together with the complete residual.

A conditional complete-Weil comparison does not discharge the actual source remainder estimate.

## Accumulation and simultaneous truncation

For arbitrary increments, `a_j=c_j/j` identifies cumulative covariance with
`E_(T+1)(a)/(T+1)`. Its exact positive remainder controls both the weighted mass square
and weighted coefficient square mass. A coupling `b_j` has local variation payment
`D_(T+1)(j b_j)` with zero boundary values.

For actual Euler-deletion increments,
`0≤fullErrorEnergy−cumulativeEnergy≤(M+1)²/(T+1)` simultaneously in `X`, `M`, and `T`.
This bounds the literal omitted tail; the source upper estimate at the inner cutoff remains.

Lean: `CompletedArithmeticForms/DivisorCovariance.lean`.

## Native source error scale

At source scale `q≥2k+6` and `x>0`, the complete Gaussian-normalized signed moment
and its first-atom value satisfy

`|σ_k(x)−σ_k^(1)(x)|≤27·24^(2k) q^k ε(x)`,

where `ε(x)=regimeOneLikelihoodScale x` has an explicit exponentially decreasing
upper envelope. This is an all-order bound with visible order dependence, rather
than an assertion about a truncated theta source.

Lean: `ThetaCuspEffectiveTailScale.abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective`.

## Gauge variance and the actual census point

Distinct ordered unequal prime pairs have distinct ratios. Consequently the gauge
mean of the twisted coalescent source vanishes and its gauge variance is exactly
the sum of squared pair weights. At bandwidth `4/3` the normalized variance obeys

`∫|S_T(x)|² dx ≤ (1536/π²)(log T)³ T^(1+η) = o(N(T,2T)²)` for `η<1`.

The actual prime surplus is the value `S_T(0)`. Haar-small exceptional sets do not
bound this prescribed point. The missing arithmetic information must distinguish
the actual additive prime correlations from multiplicative gauge twists.

Lean: `ArithmeticCorrelationGeometry/TheCoalescentSurplusIsPureGaugeCharge.lean`,
`integral_normSq_twistedPrimeCoalSum`,
`twistedPrimeCoalescentSurplus_meanSquare_isLittleO`, and
`twistedPrimeCoalescentSurplus_zero`.

## Source boundaries

- Fixed-modulus averaging controls all residue packets; growing conductors and cross-annulus
  transport require further estimates.
- Fixed-overlap successor fibers grow logarithmically.
- The all-order signed theta hierarchy is RH-equivalent.
- Unrestricted positive extension of the sharp critical prime source is impossible.
- The Euler-deletion current criterion measures growth at the inner cutoff.
