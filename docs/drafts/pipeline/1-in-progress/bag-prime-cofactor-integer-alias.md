# BAG actual prime cofactor aliases

- **ID:** BAG-C28.56d
- **Stage:** 1-in-progress
- **Type:** CONJECTURE TEST / positive source construction
- **Source:** ChiPrimeGaussianCubicPrimeOnlyVaughan; ChiPrimePacketFourthMoment; finite fibre Cauchy
- **Statement:** Actual negative prime cofactors force arbitrarily large non-diagonal integer-frequency alias energy at a common prime modulus.

## Hard target

The BAG full signed Gaussian cubic remains open. This tests the proposed use of exact real-fraction collision freedom in its signed Type-II correlation. Integer long factors see frequencies modulo one. Real injectivity therefore does not identify the true diagonal of the sampled phase.

## Corpus-derived paper argument

On a prime m>V with V≥1, the actual squarefree Vaughan short coefficient is -1: the truncated Möbius divisor sum on m contains only divisor 1. Choose P to be the actual dyadic prime band (64k⁸,128k⁸] and Q the actual band (64(2k²)⁸,128(2k²)⁸], with a chosen r∈Q removed. Every m∈P is less than each q,r in the second band. Hence mq is a unit modulo r. Equality of the REAL fractions mq/r forces equality of m and q by prime factorization, but the residue map (m,q)↦mq mod r has many repeated values.

Write M=|P||Q\{r}| and c_a for its fibre sizes. The corpus dyadic PNT gives M≥(k+1)r eventually, uniformly in every r in the second band. Finite fibre Cauchy gives r∑c_a²≥M², so the non-diagonal ordered alias mass ∑c_a²-M is at least kM. Every cofactor coefficient is -1; its signed cross product is +1. These are actual source coefficients, not freely chosen energy vectors. All such aliases have equal exp(2πi d mq/r) for every integer long factor d.

## Scope and survivor

The test concerns the actual prime-cofactor subfamily of the Type-II source. It does not discard the remaining squarefree cofactor signs, prove a lower bound for the full Gaussian cubic, or refute BAG. Its strongest positive survivor is the constructed prime family with uniformly growing signed non-diagonal alias mass. A valid joint proof must cancel or evaluate these modular collisions, rather than declaring only identical tuples diagonal.

## Status

Paper counting argument complete; Lean audit pending. No numerical experiment. The full Gaussian amplitude and the remaining signed cofactor complement still require a joint argument.
