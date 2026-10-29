# Actual dual Hecke frequencies have ideal-class generators

- **ID:** hecke-dual-frequencies-have-class-generators
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual Hecke theta unfolding](../1-in-progress/hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** The actual trace dual `J_b=dual(mb)` has selected nonzero generators indexed by integral ideals of class `[J_b]⁻¹`; their associated frequency ideals are exactly those indices, their norms include the exact discriminant/conductor/base factor, and their Fourier coefficients are the inverse Hecke ideal values. The dual classes form an explicit permutation of ordinary classes.

## Proof

Apply the proved fractional-ideal orbit construction to the invertible
ideal `J_b`. For each integral ideal `I` of class `[J_b]⁻¹`, its generator
`g_I` is a nonzero element of `J_b` satisfying `(g_I)=I J_b`. The
previous frequency ideal also satisfies `I_(g_I) J_b=(g_I)`. Cancelling
`J_b` identifies the two integral ideals. Substitution into the proved
Fourier identity gives

```
F_b(g_I)sgnψ(g_I)=Cψψ(b)ψ⁻¹(I).
```

The general trace-dual norm formula gives
`Norm(J_b)=(|disc K|Norm(m)Norm(b))⁻¹`. Applying the exact fractional
generator norm formula therefore gives

```
|Norm_(K/ℚ)(g_I)|=Norm(I)/(|disc K|Norm(m)Norm(b)).
```

Finally, the proved identity `J_b*b=J_1` lifts to invertible fractional
ideals and then to ordinary classes. Inverting yields
`[J_b]⁻¹=[J_1]⁻¹[b]`. For base representatives of class `c⁻¹`, the dual
ideal indices have class `[J_1]⁻¹c⁻¹`. Inversion followed by multiplication
by the fixed class is an explicit equivalence of the class group.

These are arithmetic identities; the actual dual Mellin exchange and
completed reflection remain separate analytic obligations.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeDualFrequenciesHaveClassGenerators`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualIdealUnit`, `heckeDualClassIdeals`, `heckeDualClassFrequency`
- `heckeDualClassFrequency_ne_zero`, `heckeDualFrequencyIdeal_classFrequency`
- `absNorm_heckeDualProductIdeal`, `norm_heckeDualClassFrequency`
- `finiteHeckeFourierCoefficient_classFrequency`
- `heckeDualClassShift`, `heckeDualIdealUnit_class_inv`
- `heckeDualClassPermutation`, `heckeDualClassPermutation_apply`

All three main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeDualFrequenciesHaveClassGenerators.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
