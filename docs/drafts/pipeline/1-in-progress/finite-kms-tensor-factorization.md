# Finite KMS tensor factorization

- **ID:** `finite-kms-tensor-factorization`
- **Stage:** 1-in-progress
- **Type:** THEOREM, `[BRIDGE]`
- **Scope:** general `HTGeometry`; no zeta-specific hypothesis
- **Lean parent:** `formal/GaloisForLFunctions/HTGeometry/FiniteKMSWightman.lean`

## Claim

For two independent finite Hamiltonians with additive product energy, the canonical partition,
Gibbs state weight, KMS/Wightman half-density, transition intensity of a product observable, and
Gibbs purity factor exactly into their two subsystem values.

This is the composition law required to build finite quantum realizations of a general
hypertranscendental constraint from independent local sectors.  In particular, it places the
finite prime-product purity calculation under the same generic finite-KMS calculus rather than
treating each arithmetic product as an isolated identity.

## Gates

- [ ] prove partition and normalized Gibbs factorization
- [ ] prove Wightman half-density and product-observable intensity factorization
- [ ] prove multiplicativity of Gibbs purity
- [ ] run target build, axiom audit, and lint
- [ ] RH
