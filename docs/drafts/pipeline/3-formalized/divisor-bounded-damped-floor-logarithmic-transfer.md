# Logarithmic cancellation survives the divisor-bounded damped floor transform

- **ID:** divisor-bounded-damped-floor-logarithmic-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** For `0<ε≤1/2`, every common logarithmic partial-sum saving survives the centered damped floor transform of a divisor-square bounded family with convergent reciprocal mass.

## Exact transfer

Let `s_a : ℕ→ℝ` be a family with one constant `C≥0` such that
`|s_a(d)|≤C τ(d)²` for every `a` and positive `d`. Suppose each reciprocal
series `Σ_d s_a(d)d^(-ε)/d` converges, and for every natural `p` there are
`B_p≥0` and `N_p` such that

`|Σ_(d≤x)s_a(d)|≤B_p x/(log x)^p`

for every `x≥N_p` and every `a`. Define its actual centered floor prefix by

`A_(a,ε)(n)=Σ_(d≤n)s_a(d)d^(-ε) floor(n/d)
             -n Σ_(d≥1)s_a(d)d^(-1-ε)`.

For every natural `q`, there are `K_q≥0` and a common threshold such that

`|A_(a,ε)(n)|≤K_q n^(1-ε)/(log n)^q`

for every family member beyond that threshold. This theorem transfers the stated
partial-sum bounds; it does not assert them for an unspecified arithmetic source.

## Paper proof

Finite Abel summation controls the reciprocal tail from the signed partial sums.
Reversing the long floor sum into hyperbola blocks gives, for `1≤D≤n`,

`|A_(a,ε)(n)|≤Σ_(d≤D)|s_a(d)|d^(-ε)+(13/ε)L n D^(-ε)`

whenever the partial sums beyond `D` are bounded by `Lx`. The head retains its
actual weighted mass. The checked divisor-square estimate bounds it by
`C D^(1-ε)(1+log D)^4`.

Set `b=2(q+5)`, `p=q+b`, and `D=floor(n/(log n)^b)`. Eventually,
`D≥sqrt(n)`, `D≥n/(2(log n)^b)`, and `log D≥(log n)/2`.
The head is at most `16C n^(1-ε)/(log n)^q`. The common order-`p` partial-sum
bound controls every tail block with `L=B_p/(log D)^p`; the tail is at most
`(13/ε)2^(q+b+1)B_p n^(1-ε)/(log n)^q`. Adding these two bounds proves the
claim with one threshold for the whole family.

## Lean declarations and audit

`HyperbolaCancellationWithDivisorBoundedCoefficients.lean`:

- `abs_tsum_tail_rpow_le_of_linear_of_summable`
- `sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc`
- `abs_weightCenteredPrefix_dampedSign_le_head_of_linear`
- `sum_abs_mul_rpow_le_divisor_square_head`

`LogarithmicCancellationSurvivesTheDampedFloorTransform.lean`:

- `eventually_logarithmic_hyperbola_cutoff_bounds`
- `exists_uniform_weightCenteredPrefix_dampedSign_log_rate_of_divisor_square`

All six targets passed scratch checks and transitive axiom audits with only
`propext`, `Classical.choice`, and `Quot.sound`. Both modules passed producing
and final direct `lake --old env lean` checks, and are wired into the BVI
umbrella. Their scratch files were removed. No umbrella build or raised limits
were used.

The actual Vaughan fluctuation application is now checked in
`vaughan-convolution-mean-and-logarithmic-fluctuation.md`; the complete uniform
Gram law remains under verification. No fixed power saving or full answer to
Q-I is claimed.
