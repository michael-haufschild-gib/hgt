# Hecke Fourier support is ideal coprimality

- **ID:** hecke-fourier-support-is-ideal-coprimality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** A frequency in `dual(mb)` has primitive residue trace character exactly when its associated integral ideal is coprime to `m`. At the finite conductor, this is exactly the support of the actual Hecke Fourier coefficient, whose squared norm there is `Norm(m)`. Every nonzero base ideal admits a nonzero such frequency.

## Proof

Let `J=dual(mb)`, with `m,b` nonzero integral ideals. For `a∈J`,
the fractional ideal `(a)J⁻¹` lies inside `JJ⁻¹=1`, so it is the
image of a uniquely determined integral ideal `I_a`. It satisfies
`I_a J=(a)` and is zero exactly when `a=0`.

Trace duality gives `Jm=dual(b)`. For an algebraic integer `r`,

```
r ∈ (m:I_a)
  ↔ (r) I_a ≤ m
  ↔ (r) I_a J ≤ mJ
  ↔ (ra) ≤ dual(b)
  ↔ ra ∈ dual(b).
```

The multiplication equivalence uses the nonzero fractional ideal `J`.
For `b` coprime to `m`, the previously constructed residue trace character
is primitive exactly when this annihilator equals `m`. The proved
Dedekind ideal-quotient criterion therefore gives

```
e_a primitive ↔ I_a+m=(1).
```

At the finite conductor the actual multiplicative residue character is
primitive, so the established Gauss results give

```
F_b(a) ≠ 0 ↔ I_a+m=(1),
|F_b(a)|² = if I_a+m=(1) then Norm(m) else 0.
```

At zero, `I_0=0`, hence `F_b(0)=0` whenever `m` is proper.

To construct a nonzero primitive frequency, choose a nonzero integral
ideal `I` coprime to `m` in the inverse ordinary class of `J`. Then
`IJ` is principal. A generator `a` is nonzero because `IJ` is nonzero,
and lies in `J` because `I≤1`. Its associated ideal is exactly `I`.
This proves existence for every nonzero `b`, including when `m=(1)`.
No additive generator or nondegeneracy premise is assumed.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeFourierSupportIsIdealCoprimality`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualFrequencyIdeal`, `coe_heckeDualFrequencyIdeal`
- `heckeDualFrequencyIdeal_mul_dual`, `heckeDualFrequencyIdeal_eq_bot_iff`
- `exists_heckeDualFrequencyIdeal_coprime`
- `heckeDualProductIdeal_mul_modulus`
- `mem_colon_heckeDualFrequencyIdeal_iff`
- `heckeResidueTraceCharacter_isPrimitive_iff_coprime`
- `finiteHeckeFourierCoefficient_ne_zero_iff_coprime`
- `norm_finiteHeckeFourierCoefficient_sq_eq_coprime`
- `finiteHeckeFourierCoefficient_zero_of_finiteConductor_ne_top`

All five main transitive `#print axioms` audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeFourierSupportIsIdealCoprimality.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
Inverse Hecke coefficient identification and normalized completed
reflection remain separate obligations.
