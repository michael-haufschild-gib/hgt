# Complete Möbius–divisor scale coordination

- **Stage:** 1-in-progress
- **Type:** experimental source investigation; RH producer open
- **Chain:** literal Möbius–divisor Abel action -> uniform normalized bound -> RH.
- **Source:** `CCMFUSuzukiMobiusDivisorAbelProducer` and `CCMFUSuzukiMobiusDivisorDilationChannels`.

## Frozen question

Does cancellation in the complete arithmetic source occur mainly between adjacent dilation
scales, or require coordination between widely separated scales? The experiment retains every
integer dilation and every clipped quotient block. It is not a test on truncated primes or a
replacement for the all-scale bound.

Write `D(q)=log(q!)-sum_(n<=q) tau(n)+2 gamma q`,
`A(q)=sum_(m=1)^q D(m)(sqrt(m+1)-sqrt(m))`, and `Q=floor(M/d)`.
The exact dilation contribution is

`C_d(M)=mu(d)[sqrt(d) A(Q-1)+D(Q)(sqrt(M)-sqrt(d Q))]`.

Summing `d=1..M` gives the existing finite Abel action. The terminal expression is zero when
`d Q=M`. Group by `j=floor(log_2 Q)`, with no discarded groups.

## Experimental commitments

See [protocol](../2-fully-proven/computations/mobius-divisor-scale-coordination-2026-09-06/PROTOCOL.md).
Discovery uses physical bands `M in [2^e,2^(e+1))`, `e=12,14,16`; later bands `e=18,20`
are held out. All use 64 equally spaced integer endpoints. Numerical identities are checked
against an independently assembled prime-power Chebyshev Abel action.

**C1 (frozen):** adjacent dilation groups supply at least 75% of total covariance cancellation
on every discovery band. This is a prospective local mechanism, not a claimed theorem.
If it fails, retain the failure and examine the full distance profile; do not tune the gate.

Independent permutations of the endpoint labels within each group retain that group's empirical
distribution and destroy alignment between groups. These are descriptive controls, not
independent arithmetic samples or statistical proof.

## Proof audit

The logarithmic primitive and the Möbius–divisor action are existing RH-equivalent receivers.
An Euler-product audit of common Voronoi phase coefficients reaches the already documented
`mu(n) tau(n)` reciprocal-zeta-square obstruction. A dyadic pairing cancels interior terms in
odd/odd phase fibers but leaves boundary and other phase classes. Neither supplies a bound.
No RH theorem, route retirement, or novelty claim is made.
