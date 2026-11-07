# Polynomial logarithmic returns and power convergence

- **ID:** SPL-polynomial-return-profile-rate
- **Stage:** 2-fully-proven; Lean verification in progress
- **Type:** THEOREM
- **Corpus input:** `RHTower.Matveev.effectiveBakerBound_holds`, the proved
  profile modulus, complementary pairing, and actual-count bridge.

## Statements

For `α=log 3/log 4`, fixed constants give both:

1. For every integer `Q≥2`, a half-turn return `|kα−ℓ−1/2|<1/Q`
   with `1≤k≤A Q^(D+1)`, where `D≥1`.
2. Every such return obeys `Q<A' k^D'` for fixed `D'≥1,A'>0`.

For the odd-primes-plus-{3,4} system, some fixed `0<η≤1` and `K,L>0` satisfy

- `|n⁻¹ Σ_{a<n} P(X/3^a)−1/4|≤K n^(−η)` for all `n≥1,X>0`;
- `|(X²/2−∫₀ˣ N(t)dt)/(X log X)−1/(4 log 3)|≤L(log X)^(−η)`
  for all `X≥exp 1`.

## Proof

The corpus Baker theorem gives `c/(2+|u|+|v|)^D≤|u log 2+v log 3|`
for nonzero integer coefficients, after enlarging its positive real exponent
to a positive integer. Its transitive axiom audit is standard.

Dirichlet supplies `1≤q≤Q`, `|qα−m|<1/Q`; `1/2<α<1` forces
`0≤m≤q`. Apply Baker with coefficients `(-2m,q)`. Their height base is
at most `5q`, so the nonzero step `β=|qα−m|` is at least `c₀/Q^D`.
For `j=floor(1/(2β))`, `j≥1`, `0≤1/2−jβ<β`, and
`j≤Q^D/(2c₀)`. Thus `k=jq` reaches the half-turn with the claimed cost;
its winding is `jm` or `jm−1` according to the sign of the step.

Conversely, a half-turn of precision `1/Q`, `Q≥2`, forces `0≤ℓ≤k`.
Baker with `(-(2ℓ+1),k)` has height base at most `6k` and gives
`c/(6k)^D≤log 4 |kα−ℓ−1/2|<log 4/Q`. This proves the exclusion.

Complementary pairing and the proved profile modulus give
`average error≤R(Q)+A Q^M/n`, with fixed `M≥2,A>0` and
`R(Q)=(8 log Q+32 log 4+2/3)/Q`.
Since `log Q≤2 sqrt Q`, `R(Q)≤C Q^(−1/2)` with
`C=16+32 log 4+2/3`.
For every real `Y≥1`, choose `Q=ceil(Y^(1/(2M)))+1`.
Then `2≤Q`, `Y^(1/(2M))≤Q≤3Y^(1/(2M))`, giving
`R(Q)+A Q^M/Y≤(C+A 3^M)Y^(−1/(4M))`.

The actual-count bridge gives coefficient error at most
`R(Q)(1/log 3+1/log X)+(A Q^M+7/8)/log X`.
Apply the same choice with `Y=log X≥1`. Multiplication by
`1/log 3+1` and the bound `Y⁻¹≤Y^(−η)` prove the count estimate.
Every analytic input is already proved for this actual system.

## Scope

Constants and exponents depend only on the fixed scales two and three.
The earlier elementary bounds retain their explicit constants.
No many-prime uniform exponent, pointwise discrepancy improvement,
prime-energy asymptotic, or exceptional-zero exclusion follows.
