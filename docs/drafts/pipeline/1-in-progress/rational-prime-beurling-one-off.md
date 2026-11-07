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

## Paper proof

Let `t_k` be the existing discrete one-off atoms and put `q_k` equal to the least rational prime at least `exp(t_k)`. This choice is monotone. Huxley's theorem gives, for all sufficiently large `k`,
`0 ≤ log(q_k) − t_k ≤ exp(−41t_k/100)`.
The atoms tend to infinity because their cumulative mass is `k+1`. For `Re s ≥ σ > 59/100`, integration along the real segment between the two logarithms bounds the prime-term difference by
`|s| exp(−σt_k)(log(q_k)−t_k)`.
Its tail is bounded by `|s| exp(−(σ+41/100)t_k)`, a summable sequence. The finite initial segment is entire. Thus the prime-sum correction is holomorphic on `Re s > 59/100`; both prime-power remainders are holomorphic on `Re s > 1/2`. Multiplication of the original continuation by the exponential of their difference preserves exactly the original zero pair.

For a finite occupation `v`, set `N(v)=∏_k q_k^(v_k)` and `a(n)=#{v:N(v)=n}`. Absolute convergence at `s=2` makes every fibre finite; the occupation Euler product gives the ordinary Dirichlet series for `Re s>1`. If `m,n` are coprime, prime labels in an occupation of `mn` split uniquely according to whether `q_k` divides `m` or `n`. This gives a bijection with the product of the two occupation fibres, hence `a(mn)=a(m)a(n)` and `a(1)=1`.

Removing the simple pole at `1` gives a holomorphic numerator `H` on `Re s>59/100`. Its value at `1` is nonzero. Positivity of the occupation series for real `s>1` and continuity imply `H(1)>0`. The divided difference `(H(s)−H(1))/(s−1)` supplies the continuous boundary value required by the corpus's unconditional Wiener–Ikehara theorem. Consequently `Σ_{n<N} a(n)/N → H(1)>0`.

The paper argument is dependency-closed; Lean formalization is in progress.

No polynomial vertical growth, unit coefficients, or Riemann functional equation is claimed. No AAL decision for actual zeta is claimed.

## Stronger variant to audit

The same source proves a lower bound for prime mass in every short window. A capacity-constrained matching may keep prime multiplicities uniformly bounded: use windows of exponent strictly between `7/12` and `3/5`, and assign each rational prime only a fixed number of generator labels. Bounded multiplicities would give `a_n ≤ d_K(n)` and hence Ramanujan coefficient growth. The matching and its quantitative displacement bound remain unproved here.
