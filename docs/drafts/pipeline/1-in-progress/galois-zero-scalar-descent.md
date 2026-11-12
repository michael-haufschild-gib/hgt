# Scalar descent of prime-compatible symmetries

- **ID:** galois-zero-scalar-descent
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Questions:** Arithmetic descent of the full zero motive.

## Theorem

Let `Δ` be the entire integer zero group, `A=ℂ[Δ]`, and
`S={(2^z,3^z):z∈Δ}`. Every rational-algebra endomorphism commuting with
`T_2,T_3` is injective and has the unique form

`F(a[z]) = σ(a) χ(z)[φ(z)]`,

where `σ:ℂ→ℂ` is a scalar embedding with `(σ×σ)(S)⊆S`, `χ:Δ→ℂˣ`
is arbitrary, and the additive injection `φ` is uniquely determined by
`(2^(φz),3^(φz))=(σ(2^z),σ(3^z))`. Every such pair `(σ,χ)` gives a
commuting endomorphism.

Preserving the augmentation ideal is exactly `χ=1`. Thus a scalar
embedding extends to a unique pointed commuting endomorphism precisely
when it preserves `S`. A scalar automorphism extends to a unique pointed
commuting automorphism precisely when both it and its inverse preserve `S`.
Every commuting algebra automorphism restricts to a scalar automorphism.
Fixing any ground subfield is exactly fixing that field in the scalar action.

## Paper proof

A commuting map sends constants into the common fixed subspace, exactly
the constant line, and therefore induces a scalar embedding `σ`.
Its kernel is a stable proper ideal, hence zero by two-prime difference
simplicity. The nonzero image of `[z]` is a joint eigenvector with
eigenvalues `σ(2^z),σ(3^z)`. Distinctness of the joint spectrum forces a
single coefficient: `F([z])=χ(z)[φ(z)]`. Augmentation extracts `χ(z)`.
The inverse basis character shows this coefficient is a unit;
multiplicativity makes `χ` a character. Multiplication of spectral pairs
makes `φ` additive. Injectivity of `σ` and of the spectrum makes `φ`
injective. Applying the augmentation-ideal condition to `[z]−1` forces
`χ(z)=1`.

Conversely, forward spectral preservation uniquely defines `φ`.
First apply `σ` to coefficients, multiply the coefficient at `z` by
`χ(z)`, and transport its exponent to `φ(z)`. These three operations
compose to the required algebra map. Their single-character formula
proves commutation, recovers both coordinates, and proves uniqueness.
For `χ=1`, augmentation satisfies `εF=σε`.

Scalar restriction respects composition. Scalar automorphisms preserving
the spectrum in both directions therefore have mutually inverse pointed
lifts. Conversely, a commuting automorphism and its inverse both preserve
constants. Their scalar actions are inverse. The identity ideal is also
preserved by the inverse, since `εF=σε` and `σ` is injective. This gives
the exact automorphism criterion.

## Boundary

The spectrum is the actual infinite set of exponential pairs, with no
independence or algebraicity assumptions on the zeros. The classification
does not assert that every scalar embedding preserves it. Determining its
stabilizer over the actual arithmetic source field remains open. No
functional-equation descent or purity conclusion is asserted.
