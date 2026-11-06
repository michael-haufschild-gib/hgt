# Positive frequency averaging of the radial Bessel density

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6

For `x>0` and `0≤η<π/2`,

`∫_(b∈ℝ) cosh(ηb) Re K_ib(x) db = π exp(−x cos η)`.

For `q≥1`, `p>−1`, and `T_p(τ,q)=∫_(u>q)u^p Re K_(2iτ)(2u)du`,

`∫_(b∈ℝ) cosh(ηb) T_p(b/2,q) db`
`=π∫_(u>q)u^p exp(−2u cos η)du`.

Both moments converge absolutely, including the joint frequency/radius
integral. Consequently the same positive frequency average of the actual
first-atom density `F=4T_(7/2)−6T_(3/2)−6q^(5/2)Re K_(2iτ)(2q)` is

`π[4∫_(u>q)u^(7/2)e^(−2cu)du−6∫_(u>q)u^(3/2)e^(−2cu)du`
`−6q^(5/2)e^(−2cq)]`, where `c=cos η`.

## Proof

The Schläfli source `exp(−x cosh z)` is holomorphic on
`|Im z|<π/2`, with exponential decay on every closed substrip.
Its real Fourier transform is `2K_(2πiξ)(x)`. The corpus strip inversion
theorem, evaluated at `iη`, gives the first identity after rescaling
frequency. Its absolute convergence follows from the same strip decay.

Choose `η<θ<π/2`. Order reflection and the shifted Schläfli contour give,
for `u≥1`,

`|cosh(ηb) K_ib(2u)| ≤ C_θ e^(−u cos θ)e^(−(θ−η)|b|)`,

where `C_θ=∫_(t>0)exp(−cos θ cosh t)dt<∞`. The radial factor follows
from `2u cosh t≥u+cosh t`. Multiplication by `u^p` gives an integrable
product majorant. Fubini proves the power-tail identity; linearity gives
the signed first-atom combination.

These identities concern positive averaging in frequency. They do not
assert positivity of the full arithmetic aperture spectrum.

## Lean

`CompletedArithmeticForms/BesselOrderCoshMoment.lean`:
`integral_cosh_besselOrder`, `integrable_cosh_besselOrder`.

`CompletedArithmeticForms/BesselTailCoshMoment.lean`:
`integral_cosh_besselPowerTail`, `integrable_cosh_besselPowerTail`,
`integral_cosh_besselFirstAtomTailDensity`,
`integrable_cosh_besselFirstAtomTailDensity`.

Both canonical modules checked. Capstone dependency audits use only
`propext`, `Classical.choice`, `Quot.sound`.
