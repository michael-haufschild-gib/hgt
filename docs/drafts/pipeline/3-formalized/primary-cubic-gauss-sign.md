# The primary cubic Gauss sum fixes the sign

- **ID:** primary-cubic-gauss-sign
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every Eisenstein prime away from three, the actual cubic Jacobi sum is minus the unique primary generator, and the normalized cubic Gauss sum has cube minus its angular part.

## Exact statement

Let `O = ℤ[ω]`, `λ = ω−1`, and let `P` be a maximal ideal with `λ ∉ P`.
Write `q = #O/P`. Lift the Euler character `x ↦ x^((q−1)/3)` uniquely to
`χ_P : O/P → {0,1,ω,ω²}`. Then `χ_P` has order three and

`p_P := −J(χ_P,χ_P)`

is the unique generator of `P` congruent to one modulo `λ²`.
For every primitive complex additive character `ψ` of `O/P`,

`G(χ_P,ψ)³ = −p_P q`,

`(G(χ_P,ψ)/|p_P|)³ = −p_P/|p_P|`.

A fixed complex embedding is understood. Existence of a primitive complex
additive character is supplied by mathlib. A definite normalized Gauss sum
is therefore defined at every such prime, without a character-existence input.
For any additive character, cubing its cubic Gauss sum removes the phase
introduced by an invertible additive shift.

## Proof

Reduction preserves the three cubic roots away from `λ`, permitting the lift
of Euler’s character. Its Jacobi sum reduces to a sum of polynomials of degree
less than `q−1`, hence vanishes modulo `P`. The Jacobi product formula gives
`J conjugate(J) = q`. Equality of ideal norms upgrades `(J) ⊆ P` to `(J) = P`.
The cubic Jacobi congruence gives `J ≡ −1 (mod λ²)`, so `−J` is primary.
Any other primary generator differs by a unit congruent to one modulo `λ²`;
the Eisenstein unit classification forces that unit to be one. Equivalently,
`J = −p` for every primary generator `p`.

The Gauss–Jacobi product identity and `χ_P(−1)=1` give `G³=qJ`. The norm
identity `|p|²=q` gives the normalized formula. An invertible additive shift
multiplies `G` by a cubic root of unity, which disappears on cubing.

## Lean and scope

Module: `GaloisForLFunctions/MetaplecticMobiusDescent/ThePrimaryCubicGaussSumFixesTheSign.lean`.

- `Eisenstein.cubicChar_order`
- `Eisenstein.cubicJacobi_eq_neg_primary_generator_of_principal`
- `Eisenstein.primaryGenerator_spec`, `Eisenstein.primaryGenerator_unique`
- `Eisenstein.cubicGauss_normalized_cube`
- `Eisenstein.normalizedCubicGauss_cube`
- `Eisenstein.cubicGauss_cube_mulShift`

Direct `lake --old env lean` audit passed. Seven endpoint axiom audits use
only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired.

This is classical arithmetic, adapted from the external OpenAI development;
source attribution and license accompany the module. It does not establish a
global cancellation estimate. The composite CRT identity and analytic descent
remain on [metaplectic-mobius-descent](../1-in-progress/metaplectic-mobius-descent.md).
