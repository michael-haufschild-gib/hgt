# Primitive Fourier coefficients are inverse Hecke values

- **ID:** hecke-fourier-coefficients-are-inverse-hecke-values
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Gauss and dual-character arithmetic](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** At the actual finite conductor, every nonzero frequency `a∈J_b=dual(mb)` satisfies `F_b(a)sgnψ(a)=Cψ ψ(b)ψ⁻¹(I_a)`, where `I_a=(a)J_b⁻¹` is the constructed integral ideal and `Cψ` is the constructed arithmetic Gauss constant.

## Proof

If `a'=αa`, then `I_a'=(α)I_a` by cancellation of the nonzero
fractional ideal `J_b`. If both frequency ideals are coprime to `m`,
their ratio belongs to the actual prime-to-modulus ideal group, hence
`α` is prime to `m`. Ray-class multiplicativity gives
`ψ(I_a')=χ(α)sgnψ(α)ψ(I_a)`, while the proved finite Fourier covariance
gives `F_b(a')=χ(α)⁻¹F_b(a)`. Every real sign character has square one,
so `F_b(a)sgnψ(a)ψ(I_a)` is invariant among supported frequencies.

For the unit base ideal, comparison with the constructed reference
frequency identifies this invariant with `Cψ`. For general coprime
nonzero `b`, choose `x∈b`, nonzero and invertible modulo `m`.
Such an element exists by the proved residue representatives; for the
unit modulus, any nonzero element of `b` suffices. Put `a₁=xa`.
The exact transfer identities are

```
F_1(a₁)=χ(x)⁻¹F_b(a),
I_(a₁,1)*b=(x)*I_(a,b).
```

Multiplicativity and `ψ((x))=χ(x)sgnψ(x)` then convert the unit-base
invariant into `F_b(a)sgnψ(a)ψ(I_a)=Cψψ(b)`. Cancelling the nonzero
supported ideal value gives the asserted inverse formula. Outside
coprime support, both the Fourier coefficient and the zero-extended
ideal value vanish. Finally, inversion of the actual ray character
inverts every ideal coefficient, including this zero extension.

No primitive additive generator, principal ratio, residue lift, or
dual-character identification is assumed: each is constructed or proved.
The completed functional equation still requires the analytic dual
Mellin unfolding and normalization.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsAreInverseHeckeValues`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualFrequencyIdeal_principal_mul`
- `heckeDualFrequencyMultiplier_mem_primeTo`
- `heckeValue_dualFrequencyIdeal_mul_principal`
- `infiniteSignCharacter_sq`
- `finiteHeckeFourierCoefficient_sign_character_invariant`
- `finiteHeckeFourierCoefficient_unitBase_invariant`
- `finiteHeckeFourierCoefficient_unitBase_eq_inverse_heckeValue`
- `heckeDualProductIdeal_mul_base`
- `heckeDualFrequencyIdeal_toUnitBase_mul_base`
- `exists_nonzero_unitResidue_mem_coprimeIdeal`
- `finiteHeckeFourierCoefficient_base_invariant`
- `finiteHeckeFourierCoefficient_eq_inverse_heckeValue`
- `heckeValue_inv`
- `finiteHeckeFourierCoefficient_eq_dualHeckeValue`

All five main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeFourierCoefficientsAreInverseHeckeValues.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
