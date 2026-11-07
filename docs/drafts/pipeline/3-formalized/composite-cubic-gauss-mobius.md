# Cubing a composite Gauss sum recovers Möbius

- **ID:** composite-cubic-gauss-mobius
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The normalized cubic residue sum on the quotient by a product of distinct Eisenstein primes has cube equal to the ideal Möbius sign times the primary angular part.

## Exact statement

Let `P_i` be a finite family of distinct maximal ideals of the Eisenstein
integers, none containing `λ = ω−1`. Put `I = ∏P_i` and `p = ∏p_i`, where
`p_i` is the canonical primary generator. Let `e : O/I ≃ ∏O/P_i` be CRT.
For every primitive additive character `ψ : O/I → ℂ×`, define

`γ(I,ψ) = |p|⁻¹ Σ_{x∈O/I} (∏_i χ_{P_i}(e(x)_i)) ψ(x)`.

Then

`γ(I,ψ)³ = μ_K(I) p/|p|`.

A definite primitive additive character on `O/I` is also constructed, so a
specific normalized composite Gauss sum satisfies this identity. The empty
prime family is included.

## Proof

Transport `ψ` to the product ring. Its restriction `ψ_i` to the additive
coordinate subgroup is primitive: otherwise a nonzero shift supported in
that coordinate would annihilate the original character. Decomposing a
residue tuple into its coordinates factors `ψ`, and finite distributivity
factors the composite sum into the local Gauss sums.

Each local normalized Gauss sum has cube `−p_i/|p_i|`, independently of its
primitive additive character. Multiplication gives the product angular part
and `(-1)^#i`. Distinct maximal ideals are coprime; multiplicativity of the
ideal Möbius function identifies this sign with `μ_K(I)`. Conversely, a
product of primitive local additive characters is primitive, providing the
definite global character through CRT.

## Lean and scope

Module: `GaloisForLFunctions/MetaplecticMobiusDescent/CubingTheCompositeGaussSumRecoversMobius.lean`.

- `ProductGauss.localChar_primitive`, `ProductGauss.factorization_equiv`
- `Eisenstein.primeProduct_moebius`
- `Eisenstein.compositeCubicGauss_cube`
- `Eisenstein.canonicalProductAddChar_primitive`
- `Eisenstein.normalizedCompositeCubicGauss_cube`

Direct `lake --old env lean` audit passed. Six endpoint axiom audits use only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired.

This closes the composite arithmetic identity in the external metaplectic
argument. It does not prove a new cancellation bound. The local Gauss identity
is [primary-cubic-gauss-sign](primary-cubic-gauss-sign.md); the global analytic
obligations remain on [metaplectic-mobius-descent](../1-in-progress/metaplectic-mobius-descent.md).
