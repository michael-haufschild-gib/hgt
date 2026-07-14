# Finite KMS purity normalization

- **ID:** `finite-kms-purity-normalization`
- **Stage:** 1-in-progress
- **Type:** THEOREM, `[BRIDGE]`
- **Scope:** general `HTGeometry`; no zeta-specific hypothesis
- **Lean parent:** `formal/GaloisForLFunctions/HTGeometry/FiniteKMSWightman.lean`
- **Physics sources:** John C. Baez, *Rényi Entropy and Free Energy*, Entropy **13** (2011),
  1434--1452, arXiv:1102.2098; Atsushi Iwaki and Chisa Hotta, *Purity of thermal mixed quantum
  states*, Phys. Rev. B **106** (2022), 094409, DOI `10.1103/PhysRevB.106.094409`.

## Claim

For every nonempty finite Hamiltonian spectrum, the canonical Gibbs probabilities and symmetric
KMS/Wightman half-density already present in `HTGeometry` satisfy

```text
sum_a p_beta(a)^2 = Z(2 beta) / Z(beta)^2,
sum_a sum_b w_beta(a,b)^2 = 1,
sum_a w_beta(a,a)^2 = Z(2 beta) / Z(beta)^2.
```

The first identity is the order-two Gibbs Rényi value.  The second says that the KMS half-density
kernel has unit Frobenius/Hilbert--Schmidt mass without a separately supplied normalization
hypothesis.  The third identifies its diagonal mass with thermal purity.

## Direct corpus application

The result must be stated only in terms of the existing `finiteGibbsPartition`,
`finiteGibbsStateWeight`, and `finiteKMSWightmanWeight`.  It strengthens the generic KMS interface
used by finite passive response, detailed balance, atomic thermal realization, and prime-log KMS
modules.  A zeta specialization is a consumer, not part of the theorem.

## Gates

- [ ] prove the Gibbs purity/partition-ratio identity
- [ ] prove unit full squared mass of the KMS half-density
- [ ] prove diagonal squared mass equals Gibbs purity and the partition ratio
- [ ] identify at least one direct existing consumer
- [ ] run target build, axiom audit, and lint
- [ ] RH
