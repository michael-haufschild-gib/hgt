# BAG actual prime cofactor aliases

- **ID:** BAG-C28.56d
- **Stage:** 5-failed (identical-pair-only estimate; BAG remains open)
- **Type:** FAILED ESTIMATE / audited positive source construction
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

Paper proof and exact positive survivor formalized in `ChiPrimeVaughanIntegerAliases.lean`.

- `eventually_vaughanAliasOffDiagonal_large`: signed non-identical-pair alias energy ≥ kM, uniformly in every constructed prime modulus.
- `eventually_exists_vaughanPrimeAlias`: actual moduli and distinct products with coefficient -1 and equal phase at every integer long factor exist eventually.
- `not_eventually_vaughanAliasOffDiagonal_le_card`: no fixed multiple of identical-pair energy controls this subfamily eventually.
- Product injectivity, unit frequencies and exact signed fibre-energy identification are also proved.

Direct production audit46498 and all15 public axiom queries97162 passed. Only `propext`, `Classical.choice`, `Quot.sound`; no added axioms or analytic premises. Leaf wired into RHTower, no umbrella/full build. Global lint68165 exits1 on14 unrelated unreachable modules, no new BAG error. Owned scratch sources removed after both audits; logs retained under `/tmp/bag-cofactor-alias-*01a0.log`.

The retired claim is that real-product injectivity permits an identical-pair-only sampled energy bound. The positive survivor is the actual family with growing signed alias mass, not merely a negation. Full Gaussian amplitudes and the remaining signed cofactor complement still require a joint argument. No numerical experiment; RH remains open.
