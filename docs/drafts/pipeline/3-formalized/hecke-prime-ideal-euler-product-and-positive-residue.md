# Hecke prime-ideal Euler products and positive residues

- **ID:** hecke-euler-residue
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class field theory programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL3 and the positivity of the HL4/HL5 densities.
- **Statement:** For every number field, modulus and ray class character, the ideal L-series
  converges absolutely and equals its prime-ideal Euler product on `Re s > 1`, where it is nonzero.
  The trivial character deletes exactly the finite-modulus Euler factors from Dedekind zeta.
  Its residue, and every ray class's ideal density, are strictly positive.

## Exact statements

Writing `u_ψ(𝔭,s) = ψ(𝔭) (N𝔭)^{-s}`, with `ψ(𝔭) = 0` at primes dividing the modulus:

\[
L(s,ψ)=\sum_{I\ne0}ψ(I)(NI)^{-s}
      =\prod_{\mathfrak p}(1-u_ψ(\mathfrak p,s))^{-1}\ne0
\qquad (\Re s>1).
\]

\[
L(s,1)=\zeta_K(s)\prod_{\mathfrak p\mid\mathfrak m_0}
             (1-(N\mathfrak p)^{-s}),
\qquad
\rho_{\mathfrak m}=\operatorname{Res}_{s=1}\zeta_K(s)
             \prod_{\mathfrak p\mid\mathfrak m_0}(1-(N\mathfrak p)^{-1})>0.
\]

The counting density is `ρ_𝔪 = Nat.card (RayClassGroup 𝔪) * rayDensity 𝔪`; hence
`rayDensity 𝔪 > 0`. The residue limit is taken as real `s → 1⁺` and agrees with the
previously constructed continuation `ρ_𝔪 ζ(s) + R(s)`, with `R` holomorphic near one.

## Proof

1. Unique ideal factorization gives a bijection between nonzero integral ideals and finitely
   supported natural exponent vectors on nonzero prime ideals. Fractional-ideal valuations
   recover every exponent, proving injectivity; the factorization theorem proves surjectivity.
2. The map `I ↦ ψ(I)(NI)^{-s}` is multiplicative. Under this bijection it becomes the monomial
   `∏_𝔭 u_ψ(𝔭,s)^{ν(𝔭)}`. Character values have norm at most one, while `N𝔭 ≥ 2`, so each prime
   summand has norm less than one when `Re s > 1`. The corpus theorem on summability of prime
   norm powers bounds the sum of their norms.
3. The existing occupation Euler-product theorem gives both absolute convergence of the ideal
   sum and convergence of the finite prime products. Grouping the sum by the finite norm fibers
   recovers the existing Dirichlet coefficients; the zero ideal contributes zero.
4. The denominator product `∏_𝔭 (1-u_ψ(𝔭,s))` also converges, since the prime summands are
   absolutely summable. Multiplying it by the reciprocal-factor product gives one, proving
   nonvanishing without assuming a nonzero infinite product.
5. For the trivial character, the local value is zero exactly at primes dividing the finite
   modulus. Multiplying the unit-modulus Euler product by the finite product of deleted
   denominators proves the Dedekind-zeta identity. At the unit modulus, the positive-norm
   coefficients are exactly the numbers of ideals, so that L-series is Mathlib's Dedekind zeta.
6. The finite correction is continuous at one, and every factor `1-1/N𝔭` is positive.
   Mathlib's positive Dedekind-zeta residue gives the explicit positive limit. Uniqueness of
   limits identifies it with the density from the previously proved ray-class count.

## Lean declarations

All modules are in `formal/GaloisForLFunctions/HeckeLFunctions/`, namespace
`GaloisForLFunctions.HeckeLFunctions`.

| Module | Main declarations |
|---|---|
| `NonzeroIdealsArePrimeExponentVectors.lean` | `primeExponentsIdealEquiv`, `count_idealOfPrimeExponents` |
| `HeckeLSeriesHaveEulerProducts.lean` | `summable_norm_heckeIdealTerm`, `heckeL_eq_tsum_ideals`, `heckeL_eulerProduct_hasProd`, `heckeL_eulerProduct_tprod`, `heckeL_ne_zero` |
| `TheTrivialCharacterRemovesTheModulusEulerFactors.lean` | `heckeL_trivialModulus_one`, `heckeValue_one_prime`, `heckeL_one_eq_dedekindZeta_mul` |
| `TheTrivialCharacterHasAPositiveResidue.lean` | `tendsto_sub_one_mul_heckeL_one_explicit`, `heckeDensity_eq_dedekindZeta_residue_mul`, `heckeDensity_pos`, `rayDensity_pos` |

## Validation

All four modules passed final direct source checks, each run from `formal/` with
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/<Module>.lean`.
The transitive `#print axioms` audit passed: audited declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
The four modules are wired into `HeckeLFunctions.lean`, and the programme into `MainTheorems.lean`.
No umbrella or full build is used.

## Remaining programme

This settles HL3 and the positivity of the counting/residue constants. Nonvanishing at one,
the full Hecke continuation and functional equation, Hecke Mertens theorems, and class field
theory remain on the parent card. No reciprocity or unproved analytic input is assumed here.
