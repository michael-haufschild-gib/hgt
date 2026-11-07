# Sextic character conversion with exceptional frequencies

- **ID:** sextic-character-conversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Finite Fourier conversion factors into two Gauss sums for every character power; nonexceptional factors have norm one, while the exceptional fourth power retains its zero frequency.

## Exact statement

Let `F` be a finite field of cardinality `q`, `χ : F → ℂ` a multiplicative character extended by zero, and `ψ` an additive character. Define

`T_j(x) = q⁻¹ Σ_{h∈F×} (Σ_{t∈F} (χ^j)(t) ψ(−ht)) χ(h)⁻² ψ(x/h)`,

where powers are powers of zero-extended characters, including exponent zero. Then

`T_j(x) = q⁻¹ G(χ^j,ψ(−·)) G(χ^(j+2),ψ(x·))`.

If `ψ` is primitive and `χ^j, χ^(j+2)` are nontrivial, then
`T_j(x) = c_j χ^(−j−2)(x)` with `|c_j| = 1`.
For `χ^6 = 1`, the power `j = 1` therefore becomes the quadratic character `χ^3`, when this is nontrivial.

For `χ^6 = 1`, primitive `ψ`, and `j = 4`, write `a = q⁻¹ G(χ^4,ψ(−·))`. Then `T_4(0) = (q−1)a` and `T_4(x) = −a` for `x ≠ 0`. The zero-frequency term is part of the transform.

For a character of order three and primitive `ψ`, `G(χ,ψ)^3 = q J(χ,χ)`.

## Proof

The inner Fourier sum equals `χ^(−j)(h) G(χ^j,ψ(−·))` for every unit `h`. Pull out its Gauss factor and replace `h` by `h⁻¹`. The remaining sum is the second Gauss sum. This argument includes trivial powers. For a nontrivial output character, shifting the additive character extracts `χ^(−j−2)(x)`; at `x = 0` both sides vanish. Primitive Gauss sums have squared norm `q`, giving `|c_j| = 1`. A trivial multiplicative character has Gauss sum `q−1` at zero frequency and `−1` at nonzero frequencies. The cubic identity follows from the Gauss–Jacobi product identity and `χ(−1) = 1`.

## Lean and scope

Module: `GaloisForLFunctions/MetaplecticMobiusDescent/TheSexticCharacterBecomesQuadratic.lean`.

- `characterConversion_eq_gaussProduct`
- `sextic_to_quadratic`
- `characterConversion_scalar_norm`, `norm_characterConversion`
- `sextic_fourth_power_at_zero`, `sextic_fourth_power_off_zero`
- `cubic_gauss_cube`

Direct `lake --old env lean` audit passed. Six endpoint axiom audits use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella imports wired.

This formalizes finite algebra from the external metaplectic approach, with an unrestricted factorization. It is not a new zero-free region or a global mean-square estimate. The remaining source estimate is on [metaplectic-mobius-descent](../1-in-progress/metaplectic-mobius-descent.md).
