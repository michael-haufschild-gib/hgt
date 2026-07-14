# Finite KMS energy-origin gauge

- **ID:** `finite-kms-energy-origin-gauge`
- **Stage:** 1-in-progress
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

## Gates

- [ ] prove the partition rescaling law
- [ ] prove Gibbs, Wightman, intensity, and purity invariance
- [ ] apply the invariance directly to thermal moments and passive response
- [ ] run target build, axiom audit, and lint
- [ ] RH
