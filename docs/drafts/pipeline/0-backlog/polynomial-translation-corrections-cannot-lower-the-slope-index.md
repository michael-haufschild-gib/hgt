# Polynomial translation corrections cannot lower the slope index

- **ID:** HAAR-POLYNOMIAL-SLOPE-INDEX-MONOTONICITY
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** [Relative Haar splitting](../1-in-progress/finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
- **Statement:** If `p` is positive definite with integer Haar successor, `ψ` is Hermitian on `ℚˣ`, and `Q` is Hermitian with polynomial translation fibres and zero dilation reading, then `κ(ψ)≤κ(p+ψ∘slope+Q)`.

## Proposed extraction

Fix a nonempty finite family of slopes `a_i`. Choose `M` bounding the degrees of the translation polynomials for `Q` at all ratios `a_j/a_i`. For `1≤s≤M+1`, put

`c_s=(-1)^(s+1) binom(M+1,s)`.

Finite differences give `Σ_s c_s P(sx)=P(0)` for every polynomial of degree at most `M`. Set `L=M+2`, choose rational `0<ε<min_i |a_i|`, and use nodes `b_(s,t)=εs/L^(t+1)`, `0≤t<N`, with weights `c_s/N`.

The nodes are distinct and lie in `(0,ε)`, so the Haar translation reading makes each slope's translates orthonormal. Their weighted positive Gram matrix has diagonal `C_M/N`, where `C_M=Σ_s c_s²`; Cauchy–Schwarz bounds every entry by the same quantity.

The weights sum to one and reproduce evaluation at zero through degree `M`. Applying this identity in both translation variables kills the entire `Q` Gram matrix, because its remaining value is `Q(D_(a_j/a_i))=0`. The slope Gram matrix is unchanged. Weighted compressions of the full kernel therefore tend to the slope Gram matrix, and lower semicontinuity of negative index should give the stated inequality.

## Consequence for the positive survivor

A [stronger polynomial-fibre index equality](../1-in-progress/haar-addition-preserves-index-on-polynomial-translation-fibres.md) now has a complete paper argument: the same quadrature preserves arbitrary polynomial Gram entries while removing the positive Haar matrix. Lean verification remains open.

Subadditivity and the existing exact Haar-plus-slope law give the opposite estimate

`κ(p+ψ∘slope+Q) ≤ κ(ψ)+κ(Q)`.

Thus polynomial corrections could add negative directions but could not repair a slope defect. This would sharpen the general finite-rank perturbation window for the canonical relative split. No additivity formula is asserted: the correction and slope directions can overlap.

## Novelty and verification boundary

`Haar/IndexPreservation.lean` proves the case `Q=0` by uniform translation averages. `Index/FiniteRankPerturbations.lean` allows loss of as many negative directions as the correction's rank. Neither supplies polynomial-annihilating averages with vanishing positive norm.

The finite-difference quadrature, node separation, polynomial Gram cancellation, and resulting index comparison remain to be audited and formalized. No complete Lean proof is claimed.

## Gates

- [ ] Audit every quadrature and polynomial degree step on paper.
- [ ] Formalize the exact slope-index comparison in the existing topic subfolders.
- [ ] Direct `lake --old env lean` audit and standard transitive axiom closure.
