# Exact Mellin integrals for nonzero field elements

- **ID:** hecke-field-element-kernels-have-exact-mellin-integrals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual theta unfolding](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** For every nonzero number-field element, the actual Hecke parity kernel has an absolutely convergent whole-log Mellin integral on `Re(s)>0`, with coefficient `sgnψ(a)|Norm(a)|^(-s)` and the exact Gamma/Jacobian factor. The negative logarithmic profile has the same integral.

## Proof

The weighted sum of the place logarithms is `log|Norm(a)|`, including
nonintegral elements. Separating the real parity monomial gives its actual
infinite sign character. Radial/log coordinates therefore express the
Mellin density as

```
sgnψ(a)|Norm(a)|^(-s) * archimedeanKernel(s, radialLog(p)+logProfile(a)).
```

The previously proved product Gamma integral is absolutely integrable
on `Re(s)>0`. Translation invariance and the exact radial-coordinate
Jacobian transfer this to the field-element density. The absolute mass
is `||Norm(a)^(-s)||` times one common archimedean mass. Fubini then gives

```
Mellin(integral_over_logSpace parityKernel(a))(MArgψ(s))
  = sgnψ(a)|Norm(a)|^(-s) Γψ(s)/(degree * 2^unitRank).
```

Negation preserves Haar measure on the entire log space, so the
negative profile used by dual theta has the same convergence and value.
No integrality assumption or unproved analytic input is required.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeFieldElementKernelsHaveExactMellinIntegrals`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `sum_mult_heckeElementLogProfile_field`
- `heckeParityKernel_eq_exp`, `heckeParityKernel_logMellin_eq`
- `integrable_heckeParityKernel_logMellin`
- `integral_norm_heckeParityKernel_logMellin`
- `integral_heckeParityKernel_logMellin`
- `mellinConvergent_integral_heckeParityKernel`
- `mellin_integral_heckeParityKernel`
- `integral_heckeParityKernel_negativeLogProfile`
- `mellinConvergent_integral_heckeParityKernel_negative`
- `mellin_integral_heckeParityKernel_negative`

All five main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeFieldElementKernelsHaveExactMellinIntegrals.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
The actual dual class Mellin sum remains a separate obligation.
