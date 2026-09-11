# EDQ all-frequency divisor-coefficient positivity

- **ID:** EDQ-POSITIVE-DIVISOR-FREQUENCY
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement rejected:** At arbitrarily large cutoffs `N`, all coefficients
  `sum_(d|l,d<=N) mu(d)*tau(l/d)` are nonnegative.

## No-go closure

- **Exact killing theorem:**
  `RHTower.DeletionDivisorFrequency.negative_frequency_every_large_cutoff`
  gives, for every `N>=1024`, a coefficient `-1` in `[2*N+2,4*N]`.
  `not_cofinal_all_frequency_nonnegative` closes the quantified contradiction.
- **Strongest positive survivor:**
  `sharp_cofinal_sign_boundary` proves nonnegativity at every frequency
  through `2*N+1` and exact cofinal sharpness at the next integer.
  `coeff_four_mul_band` also gives the exact plateau
  `T_N(4*m)=1-2*mu(2*m)` whenever `m>=2` and `m<=N<2*m`.
- **New insight:** Completing the Möbius convolution does not make the
  retained frequency tail positive. Its first guaranteed positive band is
  sharp even additively. Every large cutoff has a negative coefficient
  within four times its size, so choosing a cofinal subsequence cannot
  remove the sign obstruction.
- **Status:** Both signs and their precise cutoff dependence are proved in
  [the Lean module](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionDivisorFrequencyBoundary.lean).
  The every-cutoff strengthening is proved in
  [the coverage module](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionDivisorFrequencyCoverage.lean).
  Paper proof and targeted build are recorded on
  [the formalized card](../3-formalized/edq-divisor-frequency-sign-boundary.md).

This closes the stated cofinal coefficient-positivity shortcut. It does not
retire EDQ, prove a lower bound on its full signed energy, or rule out signed
cancellation estimates on selected cutoffs. Harmonic compensation and
cancellation between frequencies remain part of the open source estimate.
