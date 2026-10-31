# Nonzero proper subgroup carriers have a canonical relative split

- **ID:** NONZERO-PROPER-SUBGROUP-RELATIVE-SPLIT
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Integer Haar splitting](../3-formalized/finite-index-haar-carriers-split-modulo-polynomial-kernels.md); [proper-subgroup index law](../3-formalized/proper-subgroup-carriers-preserve-polynomial-fibre-indices.md).
- **Statement:** For every nonzero proper additive subgroup `H<ℚ`, every Hermitian finite-index affine kernel with translation reading `1_H` has a unique decomposition `k=P+ψ∘slope+q`: `P` is positive with successor `1_H`, `ψ` is Hermitian with `ψ(1)=0`, and `q` is a finite-rank Hermitian polynomial-fibre kernel vanishing on translations and dilations. Moreover `κ(k)=κ(ψ∘slope+q)≥κ(ψ)`.

## Proof route

Choose `a∈H`, `a≠0`, and conjugate by dilation `a` to normalize the subgroup to contain one. The zero-axis polynomial correction then removes the unit-period defect. The remaining column representation is locally periodic under every rational translation. Its moving forms are nonnegative, monotone under cyclic subgroup enlargement, and uniformly bounded on each vector by the reciprocal-quotient-order orbit formula.

For a proper subgroup containing one, the quotient orders of `1/n!` tend to infinity. Indeed, choose `r∉H`. Given `M`, take `n` beyond the denominators of every `r/d`, `1≤d≤M`. If the order `d_n` were at most `M`, then `r/d_n=m/n!` for an integer `m`, while `d_n/n!∈H`, forcing `r∈H`. This proves vanishing of the discarded identity pairing without a prime-height estimate.

The remaining construction must produce an affine-invariant factorial moving-form limit whose remainder kills every translation difference and factors through slope. Vanishing of the discarded identity pairing would preserve the successor. Transport through dilation conjugation would then give the claimed decomposition. The proved proper-subgroup polynomial index and rigidity laws would determine its residual index and uniqueness.

## Verification boundary

`BiarithmeticGeometry/Affine/SubgroupFactorialOrders.lean` proves
`tendsto_subgroupOrder_factorialStep` and `tendsto_inv_subgroupOrder_factorialStep`:
for every proper subgroup containing one, factorial-step quotient orders tend to
infinity and their reciprocals tend to zero. The direct Lean audit passed with
transitive axioms only `propext`, `Classical.choice`, and `Quot.sound`.
The proper-subgroup polynomial index and rigidity laws are also formalized.

The full relative split still lacks a dependency-closed paper proof and Lean
formalization of the general subgroup moving-form limit and transport of the
polynomial correction. The zero subgroup has no nonzero period and is outside
this existence claim.

## Gates

- [x] Factorial quotient-order divergence and reciprocal vanishing formalized.
- [ ] Audit normalization, finite-rank transport, and all limit dependencies on paper.
- [ ] Formalize the exact split and index law in the existing topic subfolders.
- [ ] Direct `lake --old env lean` checks and standard transitive axiom closures.
