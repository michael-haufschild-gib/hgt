# Finite KMS tensor factorization

- **ID:** `finite-kms-tensor-factorization`
- **Stage:** 3-formalized
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

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/FiniteKMSPurityNormalization.lean` proves exact factorization
of the partition, normalized state weights, Wightman half-density, product-observable transition
intensity, and Gibbs purity for additive product Hamiltonians.

## Gates

- [x] prove partition and normalized Gibbs factorization
- [x] prove Wightman half-density and product-observable intensity factorization
- [x] prove multiplicativity of Gibbs purity
- [x] direct module check, axiom audit, lint, and diff integrity; no full build requested
- [ ] RH
