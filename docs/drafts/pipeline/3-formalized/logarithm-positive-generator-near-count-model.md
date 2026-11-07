# A positive-generator model near the exact count

- **ID:** SPL-positive-near-count
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** A nonclassical integer-norm Beurling system with slope-one
  count and error `O((log x)²)`.

## Construction and count

Delete the rational-prime label `2`; retain every odd prime; add one extra
label of norm `3` and one label of norm `4`. All generator multiplicities
are nonnegative. Generalized integers correspond bijectively to
triples `(u,a,b)` with `u` a positive odd integer and `a,b≥0`, with norm
`u 3^a 4^b`.

Thus the count is
`N(x)=Σ_{a,b≥0} #{odd u≥1 : u≤x/(3^a4^b)}`.
The main-term coefficient is
`(1/2)(1−1/3)⁻¹(1−1/4)⁻¹=1`.
For `3^(A+1)>x` and `4^(B+1)>x`, the sum is supported in the rectangle
`0≤a≤A, 0≤b≤B`. Each odd-integer count differs from half its endpoint
by at most `1/2`; the omitted geometric main terms total less than `2`.
Consequently `|N(x)−x|≤(A+1)(B+1)/2+2`.

Taking logarithmic floors for `A,B` gives, for every `x≥1`,

`|N(x)−x|≤(log x/log 3+1)(log x/log 4+1)/2+2`.

## Scope

The distinct norm-three labels ensure nonunique factorization. This places
a genuine positive-generator system above the logarithmic isolation floor,
within a quadratic logarithmic error. It does not prove the floor sharp.

The Euler ratio is formally
`(1−2^(−s))/((1−3^(−s))(1−4^(−s)))`.
This finite modification supplies no new zero in `Re s>0`; it does not
answer the exceptional-zero distance question.

## Lean proof

Namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount`.

- `PositiveNearCountModel.lean`: `hasIntegerNorms`, `coordinates_injective`,
  `exists_coordinates`, `intNorm_coordinates`, `isDiscrete` identify the
  actual positive-generator system and prove its local finiteness.
- `PositiveNearCountEstimate.lean`: `countBall_eq_rectangle_sum`,
  `count_error_rectangle`, `count_error_log_bound`, `count_error_log_sq`,
  `not_prime_equiv` prove the count formula, explicit bound, quantified
  `O((log x)²)` estimate and nonclassicality.

Both source files pass direct Lean checks. Capstone dependency audits use
only `propext`, `Classical.choice`, `Quot.sound`. No external novelty claim.

The [carry recurrence](logarithm-positive-model-carry-recurrence.md) gives
signed logarithmic deficits. Closing the logarithmic-to-quadratic-logarithmic
gap remains open.
The [averaged deficit](logarithm-positive-model-averaged-deficit.md) has
exact order `x log x`, with an explicit bound for the actual count integral.
