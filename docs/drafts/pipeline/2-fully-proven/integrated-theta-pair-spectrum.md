# Exact integrated theta-pair spectrum

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean pending
- **Wall:** Σ6

For positive integers `n,m`, `r≥0`, and real `b`, put `q=πnm exp r`.
Let `F(τ,q)` be the positive first-atom Bessel-tail density already formalized.
The literal ordered-pair Wigner tail satisfies

`∫_(s>r) Re W_(n,m)(s/2,b) ds`
`=4(πnm)^(-1/2) cos(b(log n−log m)) F(b/2,q)`.

The exact product/ratio identity gives
`W_(n,m)(s/2,b)=exp(s/2) exp(-ib(log n−log m)) Rhat(2πnm exp s,b)`.
The radial transform is real. Substitution `u=πnm exp s` changes its
center integral to `(πnm)^(-1/2)∫_(u>q)u^(-1/2)Rhat(2u,b)du`.
The established radial Fourier-tail identity evaluates this as
`4(πnm)^(-1/2)F(b/2,q)`. Since `q≥π>1+√2`, this factor is strictly positive.

Thus the tail has exactly the cosine's sign. Diagonal pairs are strictly
positive at every frequency; every pair is strictly positive at frequency
zero. For `n≠m`, the frequency `b=π/(log n−log m)` gives a strictly
negative pair tail. This excludes termwise positivity, not positivity of
the complete theta sum.

The positive survivor is the exact all-frequency sign classification and
strict positivity of every diagonal tail, with no frequency cutoff.

## Absolute pair-series remainder

Let `C(τ)=4 Cost(7/2,τ)+6 Cost(3/2,τ)+6 Cost(5/2,τ)`, using
`besselPowerTailCost`. The established power-tail and endpoint bounds give
`|F(τ,u)|≤C(τ)exp(-u)` for `u≥1`.
Writing `q=πexp r`, the absolute pair-tail contribution is at most
`4C(b/2)exp(-qnm)`: `(πnm)^(-1/2)≤1` and the ratio cosine has absolute
value at most one.

For `n,m≥1`, `nm≥n+m−1`. Hence the pair-tail series is absolutely
convergent. Omitting all pairs with `n>M` or `m>M` leaves absolute error
at most

`8C(b/2) exp(-q(M+1))/(1-exp(-q))²`.

This follows by covering the omitted set by two geometric half-strips.
The constant depends on frequency; this is an absolute error bound, not
a positive lower bound for the signed complete sum. Identification with
the full-source Fourier integral additionally requires the appropriate
sum/integral exchange.
