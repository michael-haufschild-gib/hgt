# Primitive Hecke Gauss constants have exact norm

- **ID:** hecke-primitive-gauss-constants-have-exact-norm
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Gauss and dual-character arithmetic](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Construct an actual nonzero primitive trace frequency and its coprime integral ideal. The finite Gauss coefficient corrected by its real sign and ideal character has squared norm equal to the finite conductor norm; dividing by the positive square root gives norm one.

## Proof

Apply the proved existence theorem for primitive trace frequencies to the
unit base ideal. It chooses a nonzero `a₀∈dual(m)` with associated
integral ideal `I₀=(a₀)/dual(m)` coprime to `m`. This construction also
works for the unit modulus. Put

```
Cψ = F_1(a₀) sgnψ(a₀) ψ(I₀).
```

The ideal `I₀` is nonzero because `a₀` is nonzero. Its character value
therefore comes from the actual finite ray class group and has norm one.
The infinite sign character has finite domain and also has norm one.
At the finite conductor, the coprime-support Gauss norm theorem gives
`|F_1(a₀)|²=Norm(m)`, hence `|Cψ|²=Norm(m)`.

The finite quotient ring is nonempty and finite, so its cardinality
`Norm(m)` is strictly positive. Taking the nonnegative square root gives
`|Cψ|=sqrt(Norm(m))`, and therefore
`|Cψ/sqrt(Norm(m))|=1`.

The frequency and ideal are constructed, with no additive-generator
premise. This norm theorem does not by itself assert the completed
functional equation or identify its root number; the coefficient identity
and analytic recombination remain separate consumers.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckePrimitiveGaussConstantsHaveExactNorm`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeReferenceFrequency`, `heckeReferenceFrequency_ne_zero`
- `heckeReferenceIdeal`, `heckeReferenceIdeal_coprime`, `heckeReferenceIdeal_ne_bot`
- `heckeGaussConstant`, `norm_heckeGaussConstant_sq`, `norm_heckeGaussConstant`
- `heckeNormalizedGaussConstant`, `norm_heckeNormalizedGaussConstant`

All three main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckePrimitiveGaussConstantsHaveExactNorm.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
