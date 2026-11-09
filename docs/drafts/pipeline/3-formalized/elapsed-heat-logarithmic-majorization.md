# Elapsed heat and logarithmic depth majorization

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; transport of finite initial depth layers.
- **Threshold theorem:** For every nonzero real polynomial, `t≥0`, and `a>0`,
  `Σ_upper(t) log⁺(((Im z)²+2t)/a) ≤ Σ_upper(0) log⁺((Im z)²/a)`.
  The same inequality holds for the Riemann heat divisor at every `t>0`,
  with an extended nonnegative initial sum. Multiplicities are retained.
- **Product theorem:** For polynomials, every largest-`k` product of surviving
  elapsed squared depths is bounded by the initial largest-`k` product.
  For positive lists with ordered lengths, this family is equivalent to all
  logarithmic threshold inequalities.
- **Count theorem:** The actual Riemann heat divisor satisfies
  `N(t) log(2t/a) ≤ 2 Σ_upper(0) log⁺((Im z)²/a)` for `0<a<2t`.
- **Sharpness:** An isolated quadratic pair attains equality until collision;
  every universal clock coefficient above `2` fails.
- **Contribution count:** One, including profile comparison, threshold limit,
  product equivalence, entire transfer, sharpness, and power-moment separation.

## Mathematical content

Positive power sums do not supply every increasing convex test of logarithmic
depth. Threshold tests compare products of selected deepest roots while
permitting a deep initial pair to support a shallow surviving pair. The initial
threshold budget ignores every root below squared depth `a`; infinitely many
such shallow roots cannot make it diverge. This replaces the false hard
depth-count cutoff with a quantitative finite-layer budget.

Corpus searches for logarithmic heat majorization, products of largest root
depths, and logarithmic upper-root sums surfaced squared-height majorization
and power-moment budgets; no threshold or product comparison surfaced.

An explicit separation is proved: the abstract depth list `(2,2)` has every
real power sum at most that of `(4,1/2,1/2)`, yet its threshold sum at `a=1/2`
is greater by `log 2`. With `x=2^q>0`, the power comparison is
`2x≤x²+2/x`. For `x≤2`, multiply by `x` and use
`x³−2x²+2=x(x−1)²+2−x≥0`; for `x≥2`, use `2x≤x²`.
Thus even all positive power budgets and decreasing count do not imply
the logarithmic threshold budget.

## Proof

For `r>0`, use `Φ(u)=log(a^r+u^r)−log(a^r)`. Its height derivative satisfies
`y ∂_y Φ(y²+c) = 2r [y²/(y²+c)] [(y²+c)^r/(a^r+(y²+c)^r)]`.
For `c≥0`, both factors are nonnegative and increasing on `y>0`. The complete
conjugate-packet criterion gives nonpositive work. Each root's own conjugate
cancels the explicit clock derivative at `c=2t`.

Subtract `Φ(2t)` from each nonreal-root term to obtain an action continuous
through real collisions. Freeze the final count and compare forward
derivatives. Constant real perturbations remove initial multiple roots;
continuous real-axis-vanishing minorants pass the full nonreal moment to the
limit. No continuity of the nonreal count is assumed.

The uniform scalar bound
`0≤Φ(u)/r−log⁺(u/a)≤log(2)/r` for `u≥0` passes finite root sums to the exact
threshold. After taking logarithms, these are precisely hinge comparisons.
The identity between top sums and their supporting hinge thresholds gives
the largest-product comparison and its converse, for lists of ordered
lengths. Nonreal polynomial counts decrease under heat.

For the entire divisor, transfer the polynomial threshold inequality itself.
Passing the smooth profile through the infinite initial sum first could
retain infinite shallow tails even when the threshold budget is finite.
A continuous real-axis-vanishing minorant agrees with the threshold weight
on the finite target packet. Locally uniform polynomial heat convergence
then bounds its multiplicity-weighted sum by the initial extended budget.
The corpus bound `xiApproxGrowth<1/10` covers `0<t≤1`; all zeros are already
real for `t≥1/8`. Thus this direct transfer covers every positive time.
Conjugation halves the budget, and each survivor pays at least `log(2t/a)`.

## Lean certificates

The following `ArithmeticElectrostatics` modules pass direct checks with
`lake --old env lean`. Their audited capstones use only `propext`,
`Classical.choice`, and `Quot.sound`.

- `TheLogarithmicDepthProfilesDissipate`: profile admissibility and derivative.
- `TheConjugatePacketPaysLogarithmicDepth`: complete reciprocal-field work.
- `ThePolynomialLogarithmicDepthActionIsContinuous`: collision continuity.
- `ThePolynomialLogarithmicDepthActionHasItsDerivative`: separable comparison.
- `ThePolynomialHeatDivisorPaysLogarithmicDepth`: arbitrary initial multiplicity.
- `TheLogarithmicDepthThresholdIsALimit`: uniform error and threshold limit.
- `ThePolynomialHeatDivisorObeysLogarithmicThresholds`: threshold budget and sharpness.
- `TheDeepestSurvivorsHaveSmallerProducts`: largest-product comparison and exact threshold equivalence.
- `TheInitialDepthLayersPayForHeatSurvival`: actual Riemann heat divisor and logarithmic count credit.
- `PowerMomentsDoNotDetermineLogarithmicMajorization`: explicit strict separation from every power budget.

Main declarations:
`polynomial_upper_logarithmicThreshold_le_initial`,
`polynomial_largest_elapsed_depth_product_le_initial`,
`logarithmicThresholds_iff_largestDepthProducts`,
`heat_upper_logarithmicThreshold_le_initial`,
`nonrealCount_logarithmic_credit_le_initial`,
`logarithmic_elapsed_coefficient_is_sharp`,
`equal_depths_power_moments_le_split_depths`, and
`equal_depths_logarithmicThreshold_gt_split_depths`.

All modules are wired into `ArithmeticElectrostatics.lean`; the umbrella
was not compiled. No RH conclusion follows from the threshold budget alone.
