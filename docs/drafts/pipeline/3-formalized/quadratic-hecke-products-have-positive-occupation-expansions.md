# Quadratic Hecke products have positive occupation expansions

- **ID:** quadratic-hecke-products-have-positive-occupation-expansions
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Real-character nonvanishing](../1-in-progress/real-hecke-characters-nonvanishing-by-positive-occupations.md)
- **Lean:** `HeckeLFunctions/QuadraticHeckeProductsHavePositiveOccupationExpansions.lean`
- **Statement:** For an actual ray class character `psi` with square one, `heckeL(1,s)*heckeL(psi,s)` on `Re s>1` is an absolutely convergent general Dirichlet series with coefficient one for every finite occupation and nonnegative frequencies. Its particle index is nonempty.

## Proof

The joint values of the trivial and quadratic characters on any ideal are
exactly `(0,0)`, `(1,1)`, or `(1,-1)`. The first case follows from failure
of prime-to membership; in the other cases the unit character value has
square one, so factoring `z^2-1` gives its two possible signs.

At a prime put `x=N(p)^(-s)`. The product of the two actual Euler factors
is one if the prime divides the modulus, `(1-x)^(-2)` if its character
value is positive, and `(1-x^2)^(-1)` if negative. The particle index is
the corresponding subset of prime-by-Bool indices: two particles of
frequency `log N(p)` for a positive prime and one of frequency
`2 log N(p)` for a negative prime.

Each particle nome contracts on `Re s>1` and its norm is bounded by
`N(p)^(-Re s)`. The already summable prime-norm family, duplicated twice,
therefore dominates their norms. The existing occupation Euler theorem
gives absolute convergence over finitely supported natural occupations.
Extend the particle Euler factors by one to all prime-by-Bool indices,
group each finite Bool fiber, and compare with the product of the two
proved Hecke Euler products. Uniqueness of products gives the exact
occupation identity.

The nome of each particle is `exp(-s*frequency)`. Finite products identify
the occupation monomial with `exp(-s*energy)`, where energy is the sum of
nonnegative particle frequencies times natural occupation multiplicities.
Every coefficient is one.

Finally, if no prime lay outside the modulus, every trivial Euler factor
would equal one and `heckeL(1,s)=1` on `Re s>1`. Its residue limit would
then be zero, contradicting the already proved `heckeDensity_pos`.
A good prime gives at least one particle by the quadratic sign classification.
No class field theory or prime-distribution assertion is used.

## Declarations

- `quadratic_heckeValue_cases`
- `exists_prime_heckeValue_one_ne_zero`
- `nonempty_heckeQuadraticParticle`
- `quadratic_heckeEulerFactor`
- `summable_norm_heckeQuadraticParticleNome`
- `heckeL_mul_eq_quadraticOccupation`
- `heckeQuadraticOccupationEnergy_nonneg`
- `summable_norm_heckeQuadraticOccupation`
- `heckeL_mul_eq_positive_exponentialSeries`

## Verification

Complete scratch passes without warnings. Five main transitive axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
Final direct source audit with `lake --old env lean` passes without
warnings. The olean is built for the written Landau consumer, which
remains under formalization.
