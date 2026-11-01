# Shifted sampling grids preserve the full correlation kernel

- **Stage:** 0-backlog
- **Type:** CANDIDATE / ROUTE 4.3 OBSTRUCTION
- **Parent:** [Argon routes](../1-in-progress/argon-quasi-rh-and-critical-proportion.md).

## Exact existing input

For every admissible window φ and every grid origin b,
`AdmWindow.hasSum_vHatR_mul b γ₁ γ₂` identifies

`Σ_{k∈Z} φ̂(γ₁−b−2πk/L) φ̂(γ₂−b−2πk/L)`

with `L (φ²)^ (γ₁−γ₂)`. The right side is independent of b.
Thus translating a complete critical-spacing sampling grid cannot change its Gram
correlations or remove their zeros. This identity alone is already in the corpus;
repackaging it is not the target.

## New target

Prove that uniformly bounded shifts of the actual finite grid change bulk-pair
normalized correlations by `O(1/T)`, using the derivative-Parseval tail bound.
Then transfer this to an `o(N)` change in the actual sub-threshold rank–trace slack,
with the necessary finite Gram norm and boundary census bounds discharged.

This would refute a macroscopic gain obtained solely by translating the same sampling
grid while retaining the window. The positive survivor is a precise separation:
window changes or a genuinely different analysis operator may alter the bulk Gram;
a change of complete sampling basis does not. Incommensurable spacings require their
own sampling/normalization argument and are not covered by the translation claim.

## Gates

- [ ] Search for an existing actual finite-grid translation theorem.
- [ ] Uniform finite-grid comparison with actual boundary error.
- [ ] Rank–trace transfer and exact scope of the no-go formalized.
- [ ] Positive survivor beyond basis invariance audited.
