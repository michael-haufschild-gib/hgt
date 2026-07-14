# Finite prime Möbius transfer as a Loschmidt amplitude

- **ID:** `mobius-prime-loschmidt-purity-survival`
- **Stage:** 1-in-progress
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** standard finite-spectrum quantum dynamics applied to the existing prime source
- **Physics source:** G. Styliaris, N. Anand, L. Campos Venuti, and P. Zanardi,
  *Quantum coherence and the localization transition*, Phys. Rev. B **100** (2019), 224204,
  DOI `10.1103/PhysRevB.100.224204`, especially Appendix C.

## Direct corpus target

For a finite prime aperture `S` and real `sigma`, the existing normalized signed transfer

```text
L_S(z) = product_(p in S) (1-p^(-sigma) exp(-log(p) z))/(1+p^(-sigma))
```

has the squarefree expansion

```text
L_S(i n) = sum_(T subset S) (-1)^|T| P_sigma(T) exp(-i n log product(T)),
```

where `P_sigma` is the already-formalized normalized squarefree Bernoulli law.  This is the
Loschmidt amplitude of a finite diagonal Hamiltonian with squarefree energy levels
`log product(T)` and signed diagonal weights.

Unique factorization separates the squarefree products.  Gelfond--Schneider separates their
unitary time-one phases: equality of two phases would make a nontrivial positive rational number
raised to `I` algebraic.  The existing finite-exponential-pencil theorem should therefore give

```text
Cesaro_n |L_S(i n)|^2 -> sum_(T subset S) P_sigma(T)^2 > 0.
```

The right side is the collision probability, equivalently the purity of the dephased squarefree
Bernoulli state.  In particular the finite signed prime transfer cannot converge to zero along
imaginary integer time by phase cancellation.

## Why this is a direct application

The theorem consumes, without a new abstract interface:

1. `finitePrimeSignedSchurTransfer_squarefreeExpansion` and
   `finitePrimeSquarefreeProbability` from `MobiusFiniteSchurTransfer`;
2. `primeSupportProduct_injective` from `PrimeWordSynchronizedCluster`;
3. the in-tree Gelfond--Schneider theorem for phase nondegeneracy;
4. `tendsto_finiteExponentialPencil_cesaro_norm_sq` and
   `not_tendsto_finiteExponentialPencil_zero`.

This adds a quantitative cancellation-resistant value law to an existing arithmetic transfer.
It does not claim a cofinal-in-aperture lower bound and does not prove RH.

## Candidate competition

1. **Quantum dephasing / Schur multiplier.** Rejected.  The paper-level diagonal-Fock card already
   records the abstract Schur-product implication, and the only unconditional concrete
   specialization found here kills all cross-node coupling.
2. **Lee--Yang logarithmic derivative as a passive response.** Deferred.  A useful version needs a
   source-value or cofinal convergence theorem; the finite abstract response alone does not close
   the existing prime--archimedean comparison premise.
3. **Loschmidt purity of the signed prime transfer.** Selected because it is an exact identity for
   an existing source object and has two existing downstream theorem consumers.

## Gates

- [ ] formalize the squarefree phase and coefficient normal form
- [ ] prove unit modulus and phase injectivity
- [ ] identify `L_S(i n)` with the finite exponential pencil
- [ ] prove the exact Cesaro purity limit
- [ ] prove non-decay along imaginary integer time
- [ ] run axiom, build, umbrella, and lint checks
- [ ] RH
