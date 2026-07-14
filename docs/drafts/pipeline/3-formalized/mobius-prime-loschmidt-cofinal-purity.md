# Cofinal prime Möbius Loschmidt purity

- **ID:** `mobius-prime-loschmidt-cofinal-purity`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** standard Loschmidt-purity and Euler-product calculus on the existing source
- **Parents:** `mobius-prime-loschmidt-purity-survival`,
  `SquarefreeMoebiusNormalization.lean`
- **Physics source:** G. Styliaris, N. Anand, L. Campos Venuti, and P. Zanardi,
  *Quantum coherence and the localization transition*, Phys. Rev. B **100** (2019), 224204,
  DOI `10.1103/PhysRevB.100.224204`, Appendix C.

## Claim

The finite theorem gives

```text
Purity(S,sigma)
 = product_(p in S) (1+p^(-2 sigma))/(1+p^(-sigma))^2.
```

For `sigma>1`, the existing squarefree Euler product turns the cofinal finite-aperture limit
into the exact nonzero value

```text
product_p (1+p^(-2 sigma))/(1+p^(-sigma))^2
 = zeta(2 sigma)^3 / (zeta(4 sigma) zeta(sigma)^2).
```

This strengthens finite non-decay to a cofinal survival law in the absolutely convergent
half-plane.  It does not address the critical strip directly: at and below the Euler boundary the
same product need not retain a positive limit.

## Direct corpus application

The proof consumes the existing finite purity product, `squarefree_eulerProduct_tprod`, and the
general `HasProd`/`Multipliable` API.  No new abstract normalization interface is introduced.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/PrimeMobiusLoschmidtCofinalPurity.lean` proves the factor
multipliability, exact zeta ratio, cofinal finite-product convergence, nonzero limit, and failure of
cofinal convergence to zero.

## Gates

- [x] prove multipliability of the squarefree Euler factors on `sigma>1`
- [x] prove the infinite purity zeta-ratio identity
- [x] prove cofinal convergence of the finite Loschmidt purities
- [x] prove the limiting value is nonzero
- [x] direct module check, axiom audit, lint, and diff integrity; no full build requested
- [ ] RH
