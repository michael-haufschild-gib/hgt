# Hecke Fourier coefficients scale by ray residues

- **ID:** hecke-fourier-coefficients-scale-by-ray-residues
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Primitive finite Hecke Fourier coefficients scale by the inverse actual finite character under field multipliers prime to the modulus. Multiplying a frequency by an element of its base ideal transfers it to the unit base with the exact inverse finite-character factor.

## Proof

Let `a,a'∈dual(mb)` and `a'=αa`, where `α` is prime to `m`.
The established unit-fraction theorem constructs algebraic integers
`r,s`, both invertible modulo `m`, with `sα=r`. Integer Gauss scaling
applied to `sa'=ra` gives

```
χ(s)⁻¹ F_b(a') = χ(r)⁻¹ F_b(a).
```

The character value `χ(s)` is nonzero. Multiplying by it and using
the proved reduction formula `reduce(α)=r/s` yields
`F_b(a')=χ(reduce(α))⁻¹F_b(a)`.

For `x∈b`, the element `xa` lies in `dual(m)`: if `r∈m`, then
`rx∈mb`, so `Tr((xa)r)` is integral. Let `e_b,a` denote the actual
residue trace character. For any residue `ρ`, the element
`x*rep_1(ρ)` belongs to `b` and reduces to `xρ`. Equality of phases
for representatives in `b` therefore gives

```
e_(1,xa)(ρ) = e_(b,a)(xρ).
```

The full primitive Gauss transform now gives
`F_1(xa)=χ(x mod m)⁻¹F_b(a)`. This transfer holds for every `x∈b`,
including nonunit residues; the character's zero extension handles
that case. All additive characters, unit fractions, and reductions are
constructed objects from the existing arithmetic development.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsScaleByRayResidues`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `finiteHeckeFourierCoefficient_mul_primeTo`
- `heckeTraceFrequencyToUnitBase`
- `heckeResidueTraceCharacter_toUnitBase`
- `finiteHeckeFourierCoefficient_toUnitBase`

All three main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeFourierCoefficientsScaleByRayResidues.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
The inverse ideal-character identity is a separate consumer.
