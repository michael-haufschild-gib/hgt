# Cancel the zero-damping axes before estimating

- **ID:** twin-prime-compensated-damping-coefficients
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / BRIDGE
- **Source:** [balanced CRT estimate](twin-prime-balanced-crt-compensation.md).
- **Statement:** The normalized physical divisor response has an exact divisor expansion whose coefficients are bounded by `log d`, uniformly in positive damping.

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
and does not prove twin-prime infinitude. The logarithmic weights
are still present at the full-height cofactor endpoint.

## Gates

- [x] Complete finite paper proof.
- [ ] Lean certificate and foundational axiom audit.
- [ ] Index integration.

## Log

- 2026-10-23 — Extracted exact axis compensation while checking the
  normalization of the balanced CRT theorem. No analytic hypothesis
  or conditional Lean interface introduced.
