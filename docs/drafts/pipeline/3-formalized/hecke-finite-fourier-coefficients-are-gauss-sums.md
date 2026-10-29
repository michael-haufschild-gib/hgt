# Actual Hecke Fourier coefficients are Gauss sums

- **ID:** hecke-finite-fourier-coefficients-are-gauss-sums
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](../1-in-progress/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Actual finite coefficients in Hecke ideal-theta inversion are Gauss sums of constructed residue trace characters. At the finite conductor, their inverse-character scaling, nonvanishing, and exact squared norms follow, with additive primitivity characterized by a concrete trace-dual annihilator condition.

## Proof

Fix a nonzero integral ideal `b` coprime to the finite modulus `m`.
Let `a∈dual(mb)` under the rational trace pairing. For each residue
`ρ∈𝓞 K/m`, choose the existing representative `rρ∈b` and define

```
eₐ(ρ) = exp(2πi Tr(rρ a)).
```

The phase is one exactly when its rational trace is an integer.
If two elements of `b` have the same residue, their difference lies
in `m∩b=mb`, so its pairing with `a` has integral trace. Thus they
have the same phase. This proves `eₐ(0)=1` and
`eₐ(ρ+σ)=eₐ(ρ)eₐ(σ)`, constructing the actual additive character.
For every algebraic integer `r`, the same representative argument gives
`e_{ra}(ρ)=eₐ(rρ)`.

The character `eₐ` is trivial exactly when `a∈dual(b)`. In one
direction, test every element of `b` using its residue representative;
in the other, every representative already belongs to `b`. Consequently

```
eₐ is primitive
  ↔ ∀ r∈𝓞 K, ra∈dual(b) → r∈m.
```

The finite coefficient already present in the actual Poisson formula is
`Σρ χ(ρ)eₐ(ρ)`, hence precisely `gaussSum χ eₐ`. If the actual finite
Hecke conductor equals `m`, the finite character `χ` is primitive by
the proved conductor criterion. The general Gauss results then yield

```
F(ra) = χ⁻¹(r mod m) F(a),
F(a) ≠ 0 ↔ eₐ is primitive,
|F(a)|² = if eₐ is primitive then Norm(m) else 0.
```

All trace characters and frequencies are actual objects from the
existing theta inversion; no additive nondegeneracy premise is assumed.
The norm law includes the unit modulus and its singleton residue ring.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeFiniteFourierCoefficientsAreGaussSums`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `numberFieldTracePhase_eq_one_iff`
- `numberFieldTracePhase_eq_of_quotient_eq`
- `heckeTraceFrequencyMul`, `heckeResidueTraceCharacter`
- `heckeResidueTraceCharacter_smul`
- `heckeResidueTraceCharacter_eq_one_iff`
- `heckeResidueTraceCharacter_mulShift_eq_one_iff`
- `heckeResidueTraceCharacter_isPrimitive_iff`
- `finiteHeckeFourierCoefficient_eq_gaussSum`
- `finiteHeckeFourierCoefficient_smul`
- `finiteHeckeFourierCoefficient_ne_zero_iff`
- `norm_finiteHeckeFourierCoefficient_sq`

The trace-character construction, concrete primitive criterion,
inverse-character scaling, nonvanishing criterion, and exact norm were
checked transitively with `#print axioms`: only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeFiniteFourierCoefficientsAreGaussSums.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
Still required: identify the annihilator condition with ideal
coprimality, identify the dual coefficients with the inverse Hecke
character including their class factors, and assemble the normalized
completed functional equation.
