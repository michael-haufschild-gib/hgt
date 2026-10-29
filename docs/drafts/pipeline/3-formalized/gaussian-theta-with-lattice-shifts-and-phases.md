# Gaussian theta with lattice shifts and phases

- **ID:** hecke-gaussian-theta-characteristics
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; Gaussian theta inversion for full lattices
- **Statement:** For every full lattice map `B`, vectors `v,w`, and `a>0`,
  `Σ_n exp(2πi⟨Bn+v,w⟩) exp(−a‖Bn+v‖²)` equals
  `|det B|⁻¹ (π/a)^(d/2) Σ_k exp(2πi⟨v,B⁻ᵀk⟩) exp(−(π²/a)‖B⁻ᵀk−w‖²)`.
  Both sums converge absolutely.

## Purpose

This gives Gaussian theta inversion for lattice residue cosets and additive characters.
Finite multiplicative-character Gauss sums, real parity factors, arithmetic duality,
and unit-domain Mellin integration remain separate obligations.

## Proof

Write the spatial shift as `Bz`. On a bounded coordinate set `‖x‖∞≤R`, the translated
coordinate `x+z` lies in the ball of radius `R+‖z‖∞`. The proved unshifted Gaussian
majorant at that radius therefore supplies normal convergence on the affine lattice.
Taking `x=0` proves absolute convergence. The modulation factor has norm one, so it
preserves these bounds and integrability.

Combining Fourier exponents proves that modulation by `w` shifts dual frequency by `w`.
Translation by `v` supplies `exp(2πi⟨v,ξ⟩)`. Pullback by `B` replaces frequency with
`B⁻ᵀξ` and contributes the inverse absolute determinant. The Gaussian transform thus
gives the displayed Fourier samples. Their absolute summability follows from the same
affine-lattice estimate with lattice map `B⁻ᵀ`, shift `−w`, and rate `π²/a`.
Actual-function Euclidean Poisson summation applies with every convergence condition
proved. Extracting scalar factors gives the identity. Substituting `a=πt` proves its
conventional theta normalization with factor `t^(−d/2)` and dual rate `π/t`.

## Lean declarations

In [GaussianThetaCharacteristics.lean](../../../../formal/GaloisForLFunctions/HTGeometry/GaussianThetaCharacteristics.lean),
namespace `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`:

- `latticePhase`, `fourier_mul_latticePhase`
- `gaussian_summable_affine_translates`, `summable_norm_gaussian_affine_lattice`
- `gaussianModulation`, `integrable_gaussianModulation`, `fourier_gaussianModulation`
- `fourier_affine_gaussianModulation`
- `summable_norm_gaussianModulation_affine`, `summable_norm_dual_gaussian_phase`
- `gaussian_lattice_poisson_with_characteristics`, `gaussian_theta_characteristics`

## Dependencies and validation

The proof imports the formalized [full-lattice Gaussian theorem](gaussian-theta-inversion-for-full-lattices.md)
and reuses actual-function Poisson summation and affine Fourier covariance. Mathlib's
`Integrable.comp_add_right` proves translation preserves integrability.

Normal convergence, affine Fourier covariance, and normalized theta inversion pass
transitive axiom audits using only `propext`, `Classical.choice`, and `Quot.sound`.
The final direct `lake --old env lean` source audit passes without warnings. The module
is wired into `HTGeometry.lean`; no umbrella was compiled. Its olean is built for
the written parity-Gaussian consumer. No limit overrides or unproved analytic
premises were added.

## Next use

[Weighted number-field trace pairing](number-field-trace-pairing-in-weighted-real-coordinates.md)
proves the required pairing normalization. Actual arithmetic dual-lattice identification,
ideal theta inversion, and uniform exponential tails are now formalized. Polynomial
real parity factors and finite multiplicative-character transforms remain open.
