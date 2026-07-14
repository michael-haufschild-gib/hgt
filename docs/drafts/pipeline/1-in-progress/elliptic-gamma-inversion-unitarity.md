# Elliptic-gamma inversion as a reflected-value eliminator

- **ID:** elliptic-gamma-inversion-unitarity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** physics transfer from elliptic-gamma solvable lattice models to the general HTGeometry product hierarchy
- **Statement:** In the repository's centered additive coordinate, reflection `z ↦ σ - z` swaps the forward and backward elliptic-gamma products, hence on the regular locus `Γ(σ-z)=Γ(z)⁻¹`; the logarithmic kernel is reflection invariant.

## Goal

Add a source-general value relation, independent of zeta, that eliminates reflected elliptic-gamma
values and reflected logarithmic kernels throughout HTGeometry.  The direct corpus test is that the
theorem must consume the existing product and log-kernel definitions, propagate regularity across
reflection, and provide reusable simplification lemmas rather than a physics-named wrapper.

## Gates

- [x] 0 → 1 in-progress: exact product involution identified; centered-coordinate convention checked symbolically; existing corpus searched; direct consumers named
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorems compile directly, axiom audit and lint pass
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics source and transfer

Spiridonov's elliptic-beta-integral solution identifies elliptic-gamma Boltzmann weights with
star-triangle relations, superconformal indices, and Kramers-Wannier-type dualities.  Kels' review of
solvable edge-interaction models uses the normalized inversion law `W(α|a,b)W(-α|a,b)=1` as a
partition-function reduction.  The transferable algebraic atom is the elliptic-gamma inversion
`Γ(x;p,q) Γ(pq/x;p,q)=1`.

- V. P. Spiridonov, *Elliptic beta integrals and solvable models of statistical mechanics*,
  arXiv:1011.3798.
- A. P. Kels, *Quasi-classical expansion of the star-triangle relation and integrable systems on
  quad-graphs*, arXiv:1602.07076.

## Approach

1. Prove `x(τ,σ-z) x(τ,z) = p q`, so the centered additive coordinate realizes
   multiplicative reflection as `z ↦ σ-z` rather than the uncentered textbook shift.
2. Prove pointwise that `pq/x` swaps every forward and backward argument and factor.
3. Lift the swaps through `tprod` to the two entire products.
4. On the regular locus, cancel the swapped quotient to obtain reciprocal and product-one laws,
   with regularity transported automatically to the reflected point.
5. Lift the same argument swap through `tsum` to prove reflection invariance of the logarithmic
   kernel and its additive pullback.

## Log

- 2026-07-14 — physics-first literature audit and existing-declaration search isolated the missing
  inversion theorem; no numerical computation and no RH literature used.
