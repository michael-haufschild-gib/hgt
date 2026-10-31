# Nonzero proper subgroup carriers have a canonical relative split

- **ID:** NONZERO-PROPER-SUBGROUP-RELATIVE-SPLIT
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Integer Haar splitting](../3-formalized/finite-index-haar-carriers-split-modulo-polynomial-kernels.md); [proper-subgroup index law](../1-in-progress/proper-subgroup-carriers-preserve-polynomial-fibre-indices.md).
- **Statement:** For every nonzero proper additive subgroup `H<ℚ`, every Hermitian finite-index affine kernel with translation reading `1_H` has a unique decomposition `k=P+ψ∘slope+q`: `P` is positive with successor `1_H`, `ψ` is Hermitian with `ψ(1)=0`, and `q` is a finite-rank Hermitian polynomial-fibre kernel vanishing on translations and dilations. Moreover `κ(k)=κ(ψ∘slope+q)≥κ(ψ)`.

## Proof route

Choose `a∈H`, `a≠0`, and conjugate by dilation `a` to normalize the subgroup to contain one. The zero-axis polynomial correction then removes the unit-period defect. The remaining column representation is locally periodic under every rational translation. Its moving forms are nonnegative, monotone under cyclic subgroup enlargement, and uniformly bounded on each vector by the reciprocal-quotient-order orbit formula.

For a proper subgroup containing one, the quotient orders of `1/n!` tend to infinity. Indeed, choose `r∉H`. Given `M`, take `n` beyond the denominators of every `r/d`, `1≤d≤M`. If the order `d_n` were at most `M`, then `r/d_n=m/n!` for an integer `m`, while `d_n/n!∈H`, forcing `r∈H`. This proves vanishing of the discarded identity pairing without a prime-height estimate.

The factorial moving-form limit is affine invariant; its remainder kills every translation difference and factors through slope. The vanishing identity pairing preserves the entire successor. Transport back through the dilation conjugation gives the claimed decomposition. The proper-subgroup polynomial index law gives its exact residual index. Polynomial rigidity of positive carriers gives uniqueness; evaluation on dilations then determines `ψ` and `q` separately.

## Verification boundary

Corpus searches found the integer-Haar slope index and splitting uniqueness, not this general existence theorem. Quotient-order divergence, subgroup moving-form limits, and transport of the polynomial correction still need Lean proofs. The zero subgroup has no nonzero period and is outside this existence claim.

## Gates

- [ ] Audit normalization, finite-rank transport, and all limit dependencies on paper.
- [ ] Formalize the exact split and index law in the existing topic subfolders.
- [ ] Direct `lake --old env lean` checks and standard transitive axiom closures.
