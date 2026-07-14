# Finite KMS energy-origin gauge

- **ID:** `finite-kms-energy-origin-gauge`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scope:** general `HTGeometry`; no zeta-specific hypothesis
- **Lean parents:** `FiniteKMSWightman.lean`, `FinitePassiveResponse.lean`,
  `ThermalKrylovMoments.lean`

## Claim

Adding one constant `c` to every finite Hamiltonian energy rescales the partition function by
`exp(-beta*c)` but leaves unchanged:

- every normalized Gibbs probability;
- every symmetric KMS/Wightman half-density and transition intensity;
- Gibbs purity;
- every thermal Liouvillian gap moment;
- the finite KMS passive response.

This is the exact energy-origin gauge of finite equilibrium quantum mechanics.  It lets every
KMS-based hypertranscendental carrier normalize one energy level to zero without introducing or
later discharging an invariance hypothesis.

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/FiniteKMSPurityNormalization.lean` proves the partition
rescaling and transports energy-origin invariance through normalized Gibbs values, Wightman
half-densities, transition intensities, purity, all Liouvillian moments, and passive responses.

## Gates

- [x] prove the partition rescaling law
- [x] prove Gibbs, Wightman, intensity, and purity invariance
- [x] apply the invariance directly to thermal moments and passive response
- [x] direct module check, axiom audit, lint, and diff integrity; no full build requested
- [ ] RH
