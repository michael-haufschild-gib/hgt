# Gaussian theta with lattice shifts and phases

- **ID:** hecke-gaussian-theta-characteristics
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Hecke L-functions HL7; Gaussian theta inversion for full lattices
- **Statement:** For every full lattice map `B`, vectors `v,w`, and `a>0`,
  `Σ_n exp(2πi⟨Bn+v,w⟩) exp(−a‖Bn+v‖²)` equals
  `|det B|⁻¹ (π/a)^(d/2) Σ_k exp(2πi⟨v,B⁻ᵀk⟩) exp(−(π²/a)‖B⁻ᵀk−w‖²)`.
  Both sums converge absolutely.

## Goal

Supply theta inversion for ideal-lattice residue cosets and additive characters.
Finite multiplicative-character Gauss sums, real parity factors, arithmetic duality,
and unit-domain Mellin integration remain separate obligations.

## Gates

- [x] 0 → 1: precise statement and dependency audit started.
- [ ] 1 → 2: dependency-closed proof.
- [ ] 2 → 3: exact Lean theorem, direct source audit, transitive axiom audit.

## Corpus audit

- `HTGeometry/GaussianLatticeTheta.lean`: unshifted Gaussian inversion and normal
  convergence. The source and all four final transitive axiom audits pass; its olean is built.
- `HTGeometry/AffineLatticePoisson.lean`: actual-function Fourier covariance under
  translation and invertible linear maps.
- `RHTower/SoninPacketFourierModulation.lean`: scalar `fourier_exp_mul`.
- The completed characteristics search did not locate an arbitrary-dimensional
  affine Gaussian formula. Scalar Jacobi-theta translation identities also appear
  but do not discharge this statement.

## Approach

1. Translate the normal Gaussian majorant using the coordinate vector `B⁻¹v`.
   On `‖x‖∞≤R`, use the existing majorant at radius `R+‖B⁻¹v‖∞`.
2. Modulation has norm one, so the same bounds prove absolute convergence.
   Translation preserves integrability; multiplication by the phase preserves it
   by domination.
3. Fourier modulation shifts frequency by `w`; translation supplies
   `exp(2πi⟨v,ξ⟩)`. Linear covariance replaces `ξ` by `B⁻ᵀk`.
4. Dual Gaussian absolute convergence follows from step 1 for `B⁻ᵀ` and shift `−w`.
   Apply the actual-function Euclidean Poisson theorem and extract constants.

## Status

The complete scratch compiles without warnings. Normal convergence on affine lattices,
Fourier covariance, and normalized theta inversion pass transitive axiom audits using
only `propext`, `Classical.choice`, and `Quot.sound`. The source is now
`HTGeometry/GaussianThetaCharacteristics.lean`, wired into the umbrella, and undergoing
its final direct source audit. No olean is needed yet because no written consumer imports it.
