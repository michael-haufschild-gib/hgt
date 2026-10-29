# Archimedean Gamma factors in actual Hecke Mellin unfolding

- **ID:** hecke-archimedean-mellin-integrals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke theta Mellin unfolding](../1-in-progress/hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Statement:** Actual nonzero-element Hecke kernels have absolutely convergent Mellin integrals for `Re s>0`, with their principal-ideal character coefficient, norm power, and standard Gamma product. The inverse-class sum may be exchanged with the Mellin integral on `Re s>1`.

## Proof

For a nonzero integral element `a`, put `a_v=|v(a)|`, place multiplicity
`m_v`, and real parity `epsilon_v`. Write `n=[K:Q]`, `k=sum epsilon_v`,
`t=exp(2q)`, and `u_v=q-P(l)_v+log(a_v)`. The product formula gives
`sum m_v*u_v=n*q+log(|Norm(a)|)`. At Mellin argument `(n*s+k)/2`, the
kernel separates into the actual principal-ideal character, norm power,
and the product of logarithmic Gaussian kernels.

The radial and unit-log measure contributes `2^(r2+1)/n`. Each real
factor integrates to `GammaR(s+epsilon_v)/2`; each complex factor
integrates to `GammaC(s)/4`, using `GammaC(s)=2*(2*pi)^(-s)*Gamma(s)`.
Their product therefore has normalization `1/(n*2^unitRank)`.
Absolute convergence follows from the proved scalar Mellin integrability,
finite-product Fubini, and the exact radial logarithmic Jacobian.

The finite residue weight times the real sign character equals the actual
principal-ideal Hecke value, including the noncoprime zero case. Absolute
Mellin mass factors as the norm of the ideal summand times a common finite
archimedean mass. The existing absolute ideal series thus justifies the
infinite exchange and identifies the actual unit-theta transform with the
inverse-class L-series; unit torsion contributes its exact order.

## Lean modules and detailed proof cards

- `HTGeometry/LogarithmicGaussianMellin.lean`:
  [scalar and finite-product Gamma integrals](logarithmic-gaussian-mellin-integrals.md).
- `HeckeLFunctions/HeckeThetaWeightsArePrincipalIdealCharacters.lean`:
  [actual principal coefficient](hecke-theta-weights-as-principal-ideal-characters.md).
- `HeckeLFunctions/HeckeGammaFactorsAreArchimedeanMellinIntegrals.lean`:
  [Gamma normalization](hecke-archimedean-gamma-factor-normalization.md).
- `HeckeLFunctions/HeckeElementKernelsHaveExactMellinIntegrals.lean`:
  [actual element integrals](hecke-element-kernel-mellin-integrals.md).
- `HeckeLFunctions/HeckeUnitAveragedMellinIsTheIdealClassSeries.lean`:
  [infinite class exchange](hecke-unit-averaged-mellin-is-ideal-class-series.md).

All modules pass final direct source audits with `lake --old env lean`.
Audited principal declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Required consumer oleans exist; finished modules are wired
into their umbrellas. Global continuation and the primitive functional
equation remain separate programme obligations.
