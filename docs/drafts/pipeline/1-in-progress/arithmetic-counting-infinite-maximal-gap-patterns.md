# Infinite prime patterns can retain the exact maximal gap

- **ID:** ACP-INFINITE-MAXIMAL-GAP-PATTERNS
- **Stage:** 1-in-progress
- **Type:** Proof plan
- **Parent:** arithmetic-counting-positivity.md
- **Input under formalization:** ../2-fully-proven/arithmetic-counting-positive-density-exact-cutoff-gap.md

## Intended positive statement

Construct infinite sets of flipped primes whose actual greatest
hyperplane gap is exactly g0=2 log 2. Their reciprocal mass can be made
arbitrarily small. The prior infinite construction only paid gaps
arbitrarily close to g0; the single-prime p>=11 theorem does not establish
an infinite joint flip. This is not a replacement single-prime threshold.

## Corpus and mechanism

The corpus search for infinite maximal-gap patterns returned only the
counted squared-density lower bound, finite dyadic selection and the
single-prime maximum. DivisibilityCountsControlInfinitePrimeFlips.lean was
read: it already constructs infinite prime sets with reciprocal mass at
every cutoff at most any prescribed eta>0.

Proposed sufficient count: all reciprocal cutoff masses are at most 1/32.
Every flipped prime then satisfies 1/p<=1/32, so p>16. The harmonic count
floor and exact mean give c>=15/16. In particular c>0 and c^2>=1/2.

For every positive conductor 2<=m<=16, the prime cutoff at m is empty,
so its Mobius coefficient vanishes. Every nonzero positive conductor
weight therefore has m>16 and energy D_m=E_m-gamma>=log m>=log16=2g0.
The normalized positive-conductor mass is 1-c^2; equivalently the
unnormalized positive mass is c^(-2)-1<=1. Thus for 0<s<g0,

Phi_P(s) <= -1/s + 1/(2g0-s) < 0.

The positive-density exact secular criterion should then prove the actual
maximal gap. Applying the earlier infinite-prime construction at
min(eta,1/32) gives infinite maximal-gap patterns at arbitrarily small
reciprocal mass.

## Checks still required

Prove the small-conductor vanishing directly from exact cutoff
compatibility; justify the positive-conductor total by the full counted
mass, with no subtraction from a divergent series. Discharge every
support, logarithmic energy and limit inequality in Lean. The 1/32
constant is a sufficient uniform count, not a proposed sharp threshold.
No zero-density maximal-gap example or complete Weil positivity follows.

The exact-cutoff-gap dependency is currently undergoing its first scratch
audit. No complete paper proof or draft is claimed for this card yet.
