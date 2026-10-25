# Zeta coefficients of the digital circle profile

- **ID:** biarithmetic-digital-circle-fourier
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Proof status:** Direct Lean source check and all three transitive axiom audits passed.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** For `0<gamma<1`, periodizing `frac(exp y) exp(-gamma*y)` at circumference `L>0` gives Fourier coefficient `-zeta(s)/(L*s)` at `s=gamma+2*pi*i*m/L`.

## Proof

The seed is integrable: on the positive half-line it is bounded by `exp(-gamma*y)`, and
on the negative half-line by `exp((1-gamma)*y)`. Under `x=exp y`, its Fourier transform
becomes the fractional-part Mellin integral

`integral_0^infinity frac(x) x^(-s-1) dx=-zeta(s)/s`, `0<Re(s)<1`.

The corpus already proves that Mellin identity on the entire strip. It also proves the
Fourier coefficient theorem for arbitrary integrable periodizations, without continuity
or pointwise convergence assumptions: the coefficient at integer `m` is `1/L` times the
line transform at `m/L`. Combining these results gives the formula.

For the golden family, `L=log5` and `a=exp(gamma*L)`. The reindexing of the periodization
is the bilateral digit profile after division by `exp(gamma*y)`. The algebraic source,
pointwise profile, and Hilbert cyclic-span comparisons remain explicit separate bridges.
In particular this coefficient theorem asserts no zeta nonvanishing on an arithmetic progression.

## Verification

- [x] Dependency-closed proof plan from the corpus's strip Mellin and L1 periodization results.
- [x] Lean general-strip seed, integrability, line transform, and circle coefficients.
- [x] Direct source check, axiom audit, and umbrella import.

Lean: `BiarithmeticGeometry/DigitalCircleFourier.lean`.
Audited declarations: `integrable_digitalLogSeed`, `fourier_digitalLogSeed`,
and `fourierCoeff_digitalCircleProfile`. All report only `propext`,
`Classical.choice`, and `Quot.sound`.

Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/DigitalCircleFourier.lean`.
Umbrella import wired; umbrella not compiled.
