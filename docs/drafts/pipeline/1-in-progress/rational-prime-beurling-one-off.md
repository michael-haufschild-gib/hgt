# A one-off Euler product over rational primes

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** There exist ordinary multiplicative natural Dirichlet coefficients with positive linear counting and an Euler product over rational primes, allowing repetitions, whose continuation has exactly `3/5 ± iγ` as zeros on `Re s > 59/100`, away from its pole at `1`.

## Mechanism

`RHTower.eventually_exists_prime_short_interval_seven_twelfths` supplies a rational prime in `(x,x+x^(59/100)]` for every sufficiently large `x`, since `7/12 < 59/100 < 3/5`. Round the discrete Beurling generators to these primes. Their logarithmic displacement is `O(exp(−41t/100))`, so the prime-sum correction should be holomorphic on `Re s > 59/100`. Prime-power corrections are already holomorphic on `Re s > 1/2`. The nonvanishing exponential correction therefore preserves the isolated pair.

Repeated prime labels give local factors `(1−p^(−s))^(−m_p)` with finite natural multiplicities `m_p`. Unique factorization should make the collected occupation coefficients ordinarily multiplicative. The residue and Wiener–Ikehara argument from `TheIntegerNormOneOffHasLinearCounting` should still give positive linear counting.

## Required checks

- The short-interval theorem's transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; direct Lean audit passed, including `7/12 < 59/100 < 3/5`.
- Generalize the perturbation estimate to decay exponent `41/100`, including the finite initial segment.
- Prove finite prime multiplicities, ordinary coefficient multiplicativity, and the Dirichlet-series identity.
- Formalize the continuation, exact zero pair, positive residue, and counting asymptotic.

No polynomial vertical growth, unit coefficients, or Riemann functional equation is claimed. No AAL decision for actual zeta is claimed.

## Stronger variant to audit

The same source proves a lower bound for prime mass in every short window. A capacity-constrained matching may keep prime multiplicities uniformly bounded: use windows of exponent strictly between `7/12` and `3/5`, and assign each rational prime only a fixed number of generator labels. Bounded multiplicities would give `a_n ≤ d_K(n)` and hence Ramanujan coefficient growth. The matching and its quantitative displacement bound remain unproved here.
