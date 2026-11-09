# Decisive samples of zero convergence exponent

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B136, quantitative sampling boundary.

## Statement

There is one set D of prime powers such that ∑_{d∈D}d^{-s} converges for every s>0,
yet a uniform lower bound for the cubic-spline traces on D forces purity for every
tempered zero configuration without real zeros, without top attainment.
Consequently #D∩[1,X] = O_s(X^s) for every s>0.

## Argument to formalize

For each k, every tail of the (k+1)-st powers of primes is decisive by gap iteration.
Continuity of the trace on the compact configuration charts gives a finite prime
block detecting chart k below −k at exponent k+1. Let D be the union of these powered
blocks. Chart nesting and the doubled encoding show that D is decisive.

For fixed s>0 choose N with (N+1)s>1. The finitely many blocks k<N contribute a
finite sum. For k=N+j and p≥2,
p^{−(k+1)s} ≤ (2^{−s})^j p^{−(N+1)s}.
The right-hand side has a convergent double sum (geometric series times p-series).
Selecting one powered-block representation per degree transfers convergence to D.
The counting bound follows by weighting every d≤X by d^{−s}≥X^{−s}.

## Status

Corpus novelty search found the arbitrary-gap construction, but no decisive sample
with zero convergence exponent. The paper argument is complete; Lean formalization
is in progress. No statement
about a bound for ζ's actual traces is claimed.
