# A positive-generator model near the exact count

- **ID:** SPL-positive-near-count
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** A nonclassical integer-norm Beurling system with slope-one
  count and error `O((log x)²)`.

## Construction and proposed count

Delete the rational-prime label `2`; retain every odd prime; add one extra
label of norm `3` and one label of norm `4`. All generator multiplicities
are nonnegative. Generalized integers should correspond bijectively to
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

## Scope and required proof

The distinct norm-three labels ensure nonunique factorization. This would
place a genuine positive-generator system above the logarithmic isolation
floor, within a quadratic logarithmic error. It would not prove that the
floor is sharp.

The Euler ratio is formally
`(1−2^(−s))/((1−3^(−s))(1−4^(−s)))`.
This finite modification supplies no new zero in `Re s>0`; it does not
answer the exceptional-zero distance question.

Formalize the factorization bijection, local finiteness, finite count identity,
and explicit error bound before using the construction. No Lean proof or
external novelty claim is asserted.

## Carry recurrence to investigate

The Euler ratio also suggests the exact integer-threshold recurrence

`N_B(n)+N_B(⌊n/2⌋)=Σ_{a≥0}⌊n/3^a⌋=(3n−s₃(n))/2`,

where `s₃(n)` is the ternary digit sum. Thus its discrepancy should satisfy
`D(n)+D(⌊n/2⌋)=(n mod 2−s₃(n))/2`.
This would express the count error through ternary carries under dyadic
dilation. Whether their cancellation improves the quadratic logarithmic
upper bound is a separate question. The recurrence also requires formalization.
