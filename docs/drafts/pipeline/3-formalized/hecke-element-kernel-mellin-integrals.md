# Exact actual-element Hecke Mellin integrals

- **ID:** hecke-element-kernel-mellin-integrals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Archimedean Mellin integrals](hecke-archimedean-mellin-integrals.md)
- **Statement:** For every nonzero algebraic integer `a` and `Re s>0`, the Mellin transform of its actual whole-unit-log theta-kernel integral equals `heckeValue((a))*N((a))^(-s)*GammaFactor(s)/(degree*2^unitRank)`, with proved absolute convergence.

## Proof

Put `u_v=q-P(x)_v+log(v(a))`, with `P` the actual weighted-zero unit profile
and `t=exp(2q)`. The weighted log norm gives
`sum m_v*u_v=degree*q+log N((a))`. The parity sum separates into the radial
parity degree and the logarithm of the positive real monomial. The Gaussian
sum becomes precisely the trace-coordinate squared norm multiplied by `t`.

Finite residue weight times the actual real sign character equals
`heckeValue((a))`, including the noncoprime zero case. At Mellin argument
`(degree*s+parityDegree)/2`, these identities express the full actual
logarithmic Mellin density as `heckeValue((a))*N((a))^(-s)` times the
archimedean product kernel translated by the element's logarithmic profile.

Haar translation and the proved radial Jacobian transfer absolute
integrability from that product kernel for `Re s>0`. Fubini is applied only
after this joint integrability proof. The existing exact Gamma integral
then gives the stated value. Applying the same measure transformation to
the norm proves an exact absolute-mass factorization, not just convergence
of the complex-valued integral.

## Lean verification

Module: `HeckeLFunctions/HeckeElementKernelsHaveExactMellinIntegrals.lean`.

- `sum_mult_heckeElementLogProfile` identifies the principal-ideal log norm.
- `heckeThetaKernel_eq_exp` identifies the actual arithmetic kernel.
- `heckeThetaKernel_logMellin_eq` is the exact pointwise translated-kernel identity.
- `integrable_heckeThetaKernel_logMellin` proves joint absolute integrability.
- `integral_norm_heckeThetaKernel_logMellin` gives exact absolute-mass separation.
- `mellinConvergent_integral_heckeThetaKernel` and
  `mellin_integral_heckeThetaKernel` prove convergence and the Mellin value.

Five main transitive axiom audits returned only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeElementKernelsHaveExactMellinIntegrals.lean`.
Wired into the Hecke umbrella; umbrella not compiled.

The absolute ideal-class series exchange is now formalized on
`3-formalized/hecke-unit-averaged-mellin-is-ideal-class-series.md`.
