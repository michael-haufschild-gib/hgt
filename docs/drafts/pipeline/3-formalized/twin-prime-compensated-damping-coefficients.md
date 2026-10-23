# Cancel the zero-damping axes before estimating

- **ID:** twin-prime-compensated-damping-coefficients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [balanced CRT estimate](../2-fully-proven/twin-prime-balanced-crt-compensation.md).
- **Statement:** Exact divisor and cofactor compensation remove the inverse damping loss; cofactor-one terms vanish and the remaining coefficients are bounded by the cofactor logarithm.

## Exact statement and complete proof

For `epsilon>0` define

`b_epsilon(d)=mu(d)(1-d^(-epsilon))/epsilon`.

At `d=0` this coefficient is zero because `mu(0)=0`. For `d>=1`,
`0<=1-d^(-epsilon)<=epsilon log d` follows from `1-exp(-u)<=u`
and monotonicity of the exponential, with `u=epsilon log d>=0`.
Since `|mu(d)|<=1`,

`|b_epsilon(d)|<=log d`.

For `n>=2`, the proved Möbius divisor identity gives
`sum_(d|n) mu(d)=0`. Subtracting this zero before dividing yields

`tau_epsilon(n)/epsilon = -sum_(d|n) b_epsilon(d)`.

Multiplying two such identities and summing over `2<=n<=X` gives

`dampedPairAverage(epsilon,X,h)
 = (1/X) sum_(2<=n<=X) sum_(d|n,e|n+h) b_epsilon(d)b_epsilon(e)`.

This is a finite identity with no limiting or cancellation premise.
For every parameter `t:Real`, the positive clock `epsilon=exp(-t)`
makes all public statements independent of proposition-valued inputs.

## Cofactor compensation removes the unit endpoint

A second use of the same zero divisor sum transfers the logarithmic
cost to the complementary divisor. Put

`w_epsilon(m)=(1-m^(-epsilon))/epsilon`.

For every divisor pair `dm=n`, complete multiplicativity of real
powers gives `d^(-epsilon)m^(-epsilon)=n^(-epsilon)`. Therefore

`tau_epsilon(n)/epsilon
 = sum_(dm=n) mu(d)d^(-epsilon) w_epsilon(m)` for `n>=2`.

Expand the right side: its first sum is `tau_epsilon(n)/epsilon`
and its second is `n^(-epsilon)/epsilon * sum_(d|n)mu(d)=0`.
This is a finite identity, including at `epsilon=0` with Lean's
totalized division convention; the useful approximation uses
positive damping.

For `d,m>=1` and positive damping,

`|mu(d)d^(-epsilon) w_epsilon(m)| <= log m`,

and `w_epsilon(1)=0` identically. Thus the cofactor-one contribution
vanishes exactly in these coordinates. At zero damping the continuous
extension is the familiar convolution `Lambda=mu*log`; no new analytic
cancellation theorem is being claimed.

For bounded cofactors the weights cost `log m`, not `log X`. Growing
cofactors still require estimates at their actual arithmetic ranges.
Qualitative fixed-form cancellation is not silently promoted to a
bound uniform in those growing coefficients.

## What it changes, and what it does not

The full physical expansion has coefficient cost `log d log e`, not
an inverse damping factor. The balanced CRT paper theorem therefore
applies to these coefficients after dividing each by `log(2Y)`, giving
`O(Y^(2-1/400) log^2(2Y))` uniformly in positive damping.

This changes the decomposition: the subtracted axes cancel only after
the complete divisor sums are assembled. An old uncorrected truncated
head cannot be replaced by the new head while leaving its tails or
stationary terms unchanged. No interchange of an infinite conditional
divisor series and a stationary average is claimed.

In particular this identity is not a source-specific lower bound,
and does not prove twin-prime infinitude. Logarithmic weights and
both Möbius signs remain on the growing nonunit-cofactor range.

## Corpus and novelty audit

The corpus already has `Lambda=mu*log` and its damped twist in
`ArithmeticContinuationAndCriticalEnergy/TheTangentFactorsThroughTheMoebiusDilation.lean`:
`sum_divisors_dampedMoebius_mul_dampedLog` and
`prefixDilation_dampedPrime_factor`. Their statements were checked.
The present identity is its finite-difference counterpart for the
physical source. Verdict **BRIDGE**, no scientific novelty claimed.

The [nonunit-cofactor target](../1-in-progress/twin-prime-nonunit-cofactor-dispersion.md)
keeps the complete truncated row and all mixed terms. The exact
endpoint cancellation warns against treating estimates for isolated
faces as necessary conditions for estimating the full source.

## Gates

- [x] Complete finite paper proof.
- [x] Lean certificate and foundational axiom audit.
- [x] Index integration; the nonunit pair capstone is returned by corpus search.

## Lean certificate

Leaf: [DampedPairDiagonal.lean](../../../../formal/GaloisForLFunctions/twin-prime/DampedPairDiagonal.lean).

- `TwinPrime.abs_compensatedDampingCoeff_exp_le_log`
- `TwinPrime.abs_compensatedDampingCoeff_physical_le_log`
- `TwinPrime.normalizedDampedResponse_eq_compensated`
- `TwinPrime.dampedPairAverage_eq_compensated`
- `TwinPrime.dampedCofactorTerm_one`
- `TwinPrime.abs_dampedCofactorTerm_exp_le_log`
- `TwinPrime.abs_dampedCofactorTerm_physical_le_log`
- `TwinPrime.normalizedDampedResponse_eq_cofactor_compensation`
- `TwinPrime.normalizedDampedResponse_eq_nonunit_cofactors`
- `TwinPrime.dampedPairAverage_eq_nonunit_cofactors`

All ten capstones have no proposition-valued premises. The leaf
check and all ten axiom audits passed with only `propext`,
`Classical.choice`, and `Quot.sound`. The zero-damping equalities
use totalized division; the quantitative bounds use the explicit
positive exponential clock or the proved physical schedule.
No analytic premise, placeholder or computational certificate
was introduced. The leaf is already in the own umbrella.

## Log

- 2026-10-23 — Extracted exact axis compensation while checking the
  normalization of the balanced CRT theorem. No analytic hypothesis
  or conditional Lean interface introduced.
- 2026-10-23 — Certified both compensations, logarithmic bounds,
  vanishing unit terms and the exact nonunit pair expansion.
