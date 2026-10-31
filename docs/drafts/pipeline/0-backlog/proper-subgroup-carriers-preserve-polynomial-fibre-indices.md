# Proper subgroup carriers preserve polynomial-fibre indices

- **ID:** PROPER-SUBGROUP-POLYNOMIAL-INDEX
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Haar polynomial index law](../1-in-progress/haar-addition-preserves-index-on-polynomial-translation-fibres.md); [subgroup successor classification](../1-in-progress/continuous-affine-dilations-classify-subgroup-indicator-successors.md).
- **Statement:** For every proper additive subgroup `H<ℚ`, every positive-definite affine kernel `P` with translation reading `1_H`, and every Hermitian kernel `h` with polynomial translation fibres, `κ(P+h)=κ(h)`, including infinite index.

## Goal

Extend the exact residual-index law from integer Haar carriers to every proper rational subgroup. Properness is sharp: for `H=ℚ`, the constant kernels `P=1` and `h=−1` sum to zero, while `h` has a negative one-point Gram.

## Approach

Every proper rational subgroup is bounded at some finite place. For nonzero `H`, rescale by a nonzero member to obtain a subgroup containing one, then use its finite prime height; rescaling back multiplies the norm bound by a constant. For `H={0}`, any prime and bound `1` suffice. Write `|q|_p≤C` for `q∈H`.

For a fixed finite affine family and polynomial degree bound `n`, choose `L` with `p^L>n`. Use translation nodes `i p^(−M−Lt)`, `1≤i≤n`, in blocks indexed by `t`. Within a block, a nonzero node difference has p-adic norm at least `p^M/n`. Between blocks, the node valuations differ because `v_p(i)<L`; the ultrametric equality gives the same bound. Choose `M` so this bound exceeds `C` times every original column's slope norm. All nonzero rescaled node differences then lie outside `H`, making each translated column family orthonormal for `P`.

In each block, binomial finite-difference weights reproduce evaluation at zero for polynomials of degree below `n`. Averaging over `N` blocks preserves every polynomial Gram entry and reduces the positive Gram's diagonal to a fixed constant divided by `N`. Positive-semidefinite Cauchy–Schwarz gives the same bound on all its entries. Gram compression, passage to the limit, and the positive-addition inequality give equality of indices.

## Novelty and verification boundary

Corpus searches found the integer-Haar slope index law and homogeneous rescaling invariance. Neither covers arbitrary subgroup successors and nonhomogeneous polynomial fibres. The integer-Haar polynomial extension and the finite-prime-height inputs have complete drafts pending audits. The arbitrary-subgroup norm reduction and separated quadrature grid still need exact Lean implementations.

## Gates

- [ ] Dependency-closed paper audit of the subgroup norm reduction and all-pairs node separation.
- [ ] Exact Lean index law and full-subgroup counterexample in existing topic subfolders.
- [ ] Direct `lake --old env lean` audits and standard transitive axiom closures.
