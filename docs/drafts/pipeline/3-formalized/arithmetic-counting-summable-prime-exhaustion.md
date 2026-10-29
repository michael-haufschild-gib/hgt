# Divisibility counts control infinite prime flips uniformly in the horizon

- **ID:** ACP-SUMMABLE-PRIME-EXHAUSTION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean:** `DivisibilityCountsControlInfinitePrimeFlips.lean`

## Exact statements

For any set P of natural numbers, let omega_P be the existing prime-sign
gauge with prime pattern -1 on P and +1 elsewhere. Nonprime members of P
are irrelevant. Put F_P(N)={p prime: p<=N and p in P} and
`eta_P(N)=sum_(p in F_P(N))1/p`. Then

1. `omega_P(n)=finiteFlip(F_P(N),n)` whenever n<=N, including n=0.
2. For N>=1, its harmonic correlation is at least `1-2 eta_P(N)`.
3. For any Q and N>=1, the normalized squared harmonic distance from the
   fixed finite cutoff F_P(Q) is at most `4 eta_(P intersect (Q,infinity))(N)`.
4. For every eta>0 there is an infinite set P of primes such that
   `eta_P(N)<=eta` for every N.
5. For every a<2 log 2 there is a completely multiplicative sign flipping
   infinitely many primes with hyperplane gap at least a.

Statements 1-3 hold for every P and every indicated horizon. In particular,
the count does not assume summability or the existence of a limiting mean.
Statement 5 is an unconditional infinite-family existence theorem.

## Uniform counting proof

A number n<=N has no prime factor above N. The factorization product for
omega_P therefore equals its finite-cutoff product throughout [1,N]; at
zero both products equal one. Multiplicativity and prime values are already
proved for primeSignGauge and are reused.

For any finite prime set F, a nontrivial sign requires an F-prime dividing n.
Since each sign is between -1 and 1,

`1-omega_F(n)<=2 sum_(p in F) 1_(p divides n)`.

Sum with weight 1/n and interchange the two finite sums. The exact count of
multiples is `H_floor(N/p)/p<=H_N/p`. Thus
`H_N-S_F(N)<=2 H_N sum_(p in F)1/p`. Use F_P(N) and divide by H_N>0 to prove
statement 2. This is a bound on actual horizon-dependent counts.

Partition P into P at most Q and its tail T above Q. Their gauge product is
omega_P. Each gauge squares to one, so
`(omega_P(n)-omega_(P at most Q)(n))^2=2(1-omega_T(n))`.
The finite part is exactly finiteFlip(F_P(Q)) at every integer. Sum this
identity harmonically and apply the preceding defect count to T. This proves
statement 3, uniformly in N and Q, without exchanging limits.

## Infinite sparse construction and paid gap

Choose A with 2/A<eta. Recursively choose primes p_n>=A*2^n and
p_(n+1)>p_n, using only the unboundedness of primes. The range P is infinite.
The reciprocal series is dominated by `(1/A)*(1/2)^n`, whose sum is 2/A.
Injectivity transfers this series to the reciprocal indicator of P. Every
finite prime-cutoff sum is therefore at most 2/A<eta, proving statement 4.

If eta<=1/2 bounds every eta_P(N), statement 2 gives a nonnegative correlation
floor 1-2 eta at every positive horizon. The already proved pole-angle
inequality is uniform over sign gauges and integer horizons; it pays the
fixed gap `g0*(1-2 eta)^2`, where g0=2 log 2. For a<g0 choose
`eta=min(1/4,(g0-a)/(8g0))>0`. Then eta<=1/2 and
`g0*(1-2 eta)^2>=g0-4g0 eta>a`. The sparse construction supplies an actual
infinite P with that gap, and weakening the gap to a proves statement 5.
All analytic inputs are geometric-series summation and the closed
pole-angle theorem. No numerical experiment or unproved source estimate
is used.

## Scope and next refinement

The finite-cutoff harmonic error is controlled explicitly by reciprocal
prime mass, a stronger currency than pointwise convergence. This does not
assert optimal gap continuity, full resolvent convergence, complete Weil
positivity, or exact selection among infinite gauges.

The exact positive Euler-product harmonic mean for arbitrary reciprocal-
summable P is a separate refinement. The present proof does not assume it.
Corpus searches found the existing general prime-sign construction and
matching-density theorems, which are reused; no existing horizon-uniform
infinite-prime counting theorem was found. No literature-wide priority claim
is made.

Prime-pattern signs are the generalized Liouville functions studied by
[Borwein, Choi and Coons](https://arxiv.org/abs/0809.1691). Their construction
and mean-value theory are background, not claimed new here. The scoped
contribution is the uniform harmonic counting estimate and its transfer
to actual prime-hyperplane gaps for an infinite prime family.

- [x] Complete finite count, uniform error and infinite sparse construction.
- [x] Lean endpoints and standard transitive axiom audit.
- [x] Canonical installed-source check, umbrella and durable evidence.

## Lean closure

The five public endpoints are `primeSetFlip_eq_finiteFlip_of_le`,
`primeSetFlip_harmonicCorrelation_ge`, `primeSetFlip_cutoff_distance_sq_le`,
`exists_infinite_primes_bounded_reciprocal_mass`, and
`exists_infinite_prime_flips_with_near_maximal_gap`.
Scratch 74195 and canonical 84861 exited zero without diagnostics. All five
transitive axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`. Exact commands, source hash and actual output are preserved in
`arithmetic-counting-summable-prime-exhaustion-audit.txt`.

No olean was needed for this leaf. Existing imported artifacts were preserved;
the umbrella was wired without compilation. The general all-pattern harmonic
mean is being investigated separately in
`../1-in-progress/arithmetic-counting-all-prime-pattern-harmonic-density.md`.
