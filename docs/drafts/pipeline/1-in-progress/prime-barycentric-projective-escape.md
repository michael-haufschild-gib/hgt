# Prime barycentric packets escape projectively

- **ID:** prime-barycentric-projective-escape
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** `../3-formalized/new/prime-barycentric-coefficient-divergence.md`
- **Statement:** `[CONJECTURE]` For fixed primes `p<q`, the ratio of the canonical exact coefficient
  magnitudes satisfies `|a_q(X)|/|a_p(X)| → ∞` along prime exhaustion.

## Goal

Test whether one common scalar renormalization can turn the divergent exact finite packets into a
nonzero coefficientwise limit.  Pairwise ratio divergence would rule this out: no scalar-normalized
packet can retain finite nonzero coefficients at two fixed primes.

## Gates

- [x] 0 → 1 in-progress: exact relative factor and Chebyshev provider identified
- [ ] 1 → 2 fully-proven: complete paper proof
- [ ] 2 → 3 formalized: exact Lean target and axiom audit
- [ ] 3 → 4 publication-ready: integrate with the fixed completed-flux germ

## Formula

Write `x_p=(log p)^2` and `x_q=(log q)^2`.  Appending a prime `r>q` multiplies the coefficient at
`p` by `x_r/(x_r-x_p)` and the coefficient at `q` by `x_r/(x_r-x_q)`.  Hence their magnitude ratio
is multiplied by

`(x_r-x_p)/(x_r-x_q) = 1 + (x_q-x_p)/(x_r-x_q)`.

This is strictly larger than `1+(x_q-x_p)/x_r`.  Since

`∑_{r prime} 1/(log r)^2 = ∞`,

the product of the relative factors diverges.  The factors contributed by primes at most `q` form
a fixed positive constant.

## Significance

Coefficientwise divergence could in principle be an overall normalization error.  Projective
escape rules that out.  The finite exact packets do not approximate any all-prime local-coefficient
object even up to a common scalar.  Any completed source must use a genuinely different
renormalized constraint, not a scalar rescaling of the finite interpolation flow.
