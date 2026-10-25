# Rank-one cofactor moduli are Archimedean

- **ID:** rank-one-cofactor-moduli-are-archimedean
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** Every one-dimensional actual cofactor module has either the
  augmentation character or cofactor character magnitudes `n^(-s)` for one
  real s>=1/2.

## Lead

In one complex dimension the commuting unital action is scalar. With the
unit cyclic vector, K(n,n)=|chi(n)|^2 and chi is completely multiplicative.
The new actual energy-ratio invariant makes r(n)=n*|chi(n)|^2 nonnegative,
completely multiplicative and nonincreasing in the ordinary integer order.
The conjectured elementary classification is: either r(n)=0 for all n>=2,
or r(n)=n^(-alpha) for alpha>=0. Comparison of integer powers through their
logarithms should force the latter form. If any r(n)=0, monotonicity and
multiplicativity force r(2)=0 and then every positive integer above one.

The claim concerns magnitudes only. It does not put the full complex
character on the Kronecker curve, control signs/phases, or identify s with
a zeta real part. A global polynomial energy upper bound alone does not
justify a bound on local subsequence escape exponents; do not add one.

## Gates

- [x] Corpus search for the monotone multiplicative classification.
- [x] Exact scalar extraction from actual rank one on paper.
- [x] Dependency-closed paper proof.
- [ ] Lean verification and transitive axioms.

## Dependency-closed paper proof

Let xi=v_1 be the unit cyclic vector. In complex dimension one each v_p is
z_p xi. Pairing with xi gives z_p=K(p,1), hence z_p is real. Applying D_p to
v_q gives z_(pq)=z_p z_q. Thus K(p,q)=z_p z_q and
r(p)=p*z_p^2 is a nonnegative multiplicative function with r(1)=1.
The actual contracted-energy identity makes r antitone in the ordinary
integer order.

If r(2)=0, then r(p)=0 for every p>=2, giving augmentation. Otherwise r(2)>0.
For every p, choose k with p<=2^k. Antitonicity gives
r(p)>=r(2)^k>0. Define g(p)=-log r(p). It is nonnegative, monotone, and
logarithm-additive: g(pq)=g(p)+g(q).

For positive integers n,m with m>1, compare n^k with
m^ceil(k*log(n)/log(m)). Monotonicity and logarithm-additivity imply

    k*g(n) <= k*g(m)*log(n)/log(m) + g(m).

If g(n)>g(m)*log(n)/log(m), choose k larger than g(m) divided by that
positive gap; contradiction. Interchanging n and m gives equality. Taking
m=2 yields g(n)=alpha*log(n), alpha=g(2)/log(2)>=0, including n=1.
Therefore r(n)=n^(-alpha), z_n^2=n^(-(alpha+1)), and
|z_n|=n^(-s) for s=(alpha+1)/2>=1/2.

This also proves reality of the character and the product formula for the
entire rank-one Gram. In the positive branch each sign z_n/|z_n| lies in
{−1,1} and is multiplicative. The argument does not select those signs.

## Lean draft

Unverified parts:
- `/tmp/qiii_monotone_multiplicative_body.lean`: generic logarithm-additive
  monotonicity and multiplicative power classification.
- `/tmp/qiii_actual_rank_one_body.lean`: actual scalar extraction, real
  character, energy character, and magnitude classification.

Both are appended to the next diagonal scratch. No canonical promotion.
The scalar extraction uses mathlib's checked source statement
`finrank_eq_one_iff_of_nonzero'`, not the unrelated matrix-kernel wrapper.
The preceding corpus log-ceiling search surfaced
`RHTower.Sieve.ceil_log_ratio_spec`; the draft uses the same elementary
ceiling comparison directly so the general theorem has no sieve dependency.

## Current verification status

The first combined diagonal check completed. The energy crossing, deleted
white-noise positivity, actual rank-one character construction, augmentation
positivity and augmentation numeric diagonal order passed independently.
Other parts had local elaboration errors. Import, endpoint normalization,
finite-dimensional API, cast, dependent-if rewrite and augmentation
multiplication repairs are staged. No new leaf from this batch is promoted.
The retry is `/tmp/qiii-diagonal-energy-check.lean`, queued after the current
moving-origin check; its log will be `/tmp/qiii-diagonal-energy-retry-check.log`.
