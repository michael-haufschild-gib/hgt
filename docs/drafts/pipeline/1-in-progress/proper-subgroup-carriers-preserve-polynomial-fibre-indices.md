# Proper subgroup carriers preserve polynomial-fibre indices

- **ID:** PROPER-SUBGROUP-POLYNOMIAL-INDEX
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Haar polynomial index law](../3-formalized/haar-addition-preserves-index-on-polynomial-translation-fibres.md); [subgroup successor classification](continuous-affine-dilations-classify-subgroup-indicator-successors.md).
- **Statement:** For every proper additive subgroup `H<ℚ`, every positive-definite affine kernel `P` with translation reading `1_H`, and every Hermitian kernel `h` with polynomial translation fibres, `κ(P+h)=κ(h)`, including infinite index.

## Goal

Extend the exact residual-index law from integer Haar carriers to every proper rational subgroup. Properness is sharp: for `H=ℚ`, the constant kernels `P=1` and `h=−1` sum to zero, while `h` has a negative one-point Gram.

## Paper proof

Choose `r∉H`. For any finite family of nonzero rational coefficients `c_j`,
choose `N` at least every denominator of `1/c_j`. Write
`1/c_j=m_j/N!` with `m_j∈ℤ`, and put `q=r/N!`. Then
`m_j(c_j q)=r`, so `c_j q∉H` for every `j`. This uses only closure of
`H` under integer multiples; it includes the zero subgroup.

Fix a finite affine family with nonzero slopes `a_i` and a polynomial degree
bound `n`. For each number of blocks, start with distinct rational nodes
`x_(j,t)=j/(n+1)^(t+1)`, `1≤j≤n`. Apply the preceding argument to all
nonzero coefficients `(x_v−x_u)/a_i`. The scaled nodes `q x_(j,t)` are
pairwise distinct modulo `a_i H` for every original column. Their translated
column families are therefore orthonormal for the successor `1_H`.

Binomial finite-difference weights on each block reproduce evaluation at zero
for every polynomial of degree below `n`. Averaging over `M` blocks preserves
every polynomial Gram entry and gives the positive Gram diagonal `C/M`, where
`C` is the squared norm of the fixed binomial weights. Positive-semidefinite
Cauchy–Schwarz bounds every positive Gram entry by `C/M`. The grid scale may
depend on `M`; the reproduced polynomial Gram is unchanged. Compression and
lower semicontinuity give `κ(h)≤κ(P+h)`. Positive addition gives the reverse
inequality, including infinite indices.

For `H=ℚ`, `P=1` and `h=−1` have sum zero, while the one-point Gram of `h`
is negative. Thus properness is exact.

## Polynomial rigidity

Two positive carriers `P,Q` of the same proper successor cannot have a nonzero
polynomial-fibre difference. Apply the index law to `Q+(P−Q)=P`: the difference
has index zero and is positive definite. Its identity value is zero, so the
positive-kernel norm bound makes it identically zero. This extends the existing
slope-only uniqueness law to arbitrary polynomial translation fibres.

## Novelty and verification boundary

Corpus searches found the integer-Haar slope law, homogeneous rescaling,
and finite-index rigidity of divisible quotients. None gives this polynomial
index law. The finite-grid avoidance argument above needs no prime-height or
p-adic bound. Complete Lean drafts include the index law, sharp converse, and
polynomial rigidity; all remain unverified.

## Gates

- [x] Dependency-closed paper proof, including all-pairs grid separation and the full-subgroup counterexample.
- [ ] Exact Lean index law and full-subgroup counterexample in existing topic subfolders.
- [ ] Direct `lake --old env lean` audits and standard transitive axiom closures.
