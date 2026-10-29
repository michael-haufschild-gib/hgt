# Actual dual Hecke kernels are unit covariant

- **ID:** hecke-dual-theta-kernels-are-unit-covariant
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual theta unfolding](../1-in-progress/hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** For a finite-primitive Hecke character, simultaneous multiplication of an actual trace-dual frequency by a global unit and translation of the place profile by its logarithm leave the actual finite-Fourier-weighted parity kernel invariant. Negative log coordinates translate by `x+log(u)`.

## Proof

The parity kernel transforms by the actual infinite sign character of
the unit. Finite Fourier covariance supplies the reciprocal finite
residue character. On global units, the product of finite and infinite
characters is one, and the infinite sign has square one. Thus the
reciprocal finite character cancels the parity sign exactly.

Substituting weighted logarithmic coordinates gives translation by
`-log(u)` for a positive profile. Replacing `x` by `-x` gives translation
by `+log(u)` for the negative profile of the actual dual average.

All identities use the actual Fourier coefficient and actual global
unit; no separate covariance assumption is introduced.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeDualThetaKernelsAreUnitCovariant`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualThetaKernel`
- `heckeParityKernel_unit`
- `inverse_finite_mul_infinite_globalUnit`
- `heckeDualThetaKernel_unit`
- `heckeDualThetaKernel_unit_as_logTranslate`
- `heckeDualThetaKernel_unit_as_negativeLogTranslate`

Both main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeDualThetaKernelsAreUnitCovariant.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
The infinite unit/class unfolding remains a separate obligation.
