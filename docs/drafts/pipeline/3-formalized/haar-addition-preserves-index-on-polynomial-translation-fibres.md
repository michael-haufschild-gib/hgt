# Haar addition preserves index on polynomial translation fibres

- **ID:** HAAR-POLYNOMIAL-INDEX-PRESERVATION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Relative Haar splitting](../1-in-progress/finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
- **Statement:** If `p` is positive definite with integer Haar successor and `h` is Hermitian with polynomial translation fibres on `Aff(ℚ)`, then `κ(p+h)=κ(h)`, including infinite index.

## Polynomial quadrature

For a nonempty finite family `g_i=T_(β_i)D_(a_i)`, choose `M` bounding the degrees of the fibre polynomials of `h` at every ratio `a_j/a_i`. Put `L=M+2` and `c_s=(-1)^(s+1) binom(M+1,s)` for `1≤s≤M+1`. The `(M+1)`st finite difference gives

`Σ_s c_s P(sx)=P(0)` for every polynomial `P` of degree at most `M`.

In particular, `Σ_s c_s=1`. Choose rational `0<ε<min_i|a_i|`. For `N≥1`, use nodes `b_(s,t)=εs/L^(t+1)`, `0≤t<N`, with real weights `w_(s,t)=c_s/N`. Averaging the preceding identity over `t` reproduces evaluation at zero through degree `M`.

All nodes lie in `(0,ε)` and are distinct. If `t<u`, equality of two nodes would imply `sL^(u−t)=r` with `1≤s,r<L`, which is impossible. For each fixed `i`, distinct translated columns have difference `(b_(r,u)−b_(s,t))/a_i`, a nonzero rational of absolute value less than one. It is not an integer, so the Haar reading makes these columns orthogonal with unit diagonal.

## Index argument

Compress the Gram matrices along the weighted columns `T_b g_i`. For `p`, the resulting positive matrix `P_N` has diagonal

`δ_N=(Σ_s c_s²)/N`.

Semidefinite Cauchy–Schwarz gives `|(P_N)_(ij)|≤δ_N`, hence `P_N→0` entrywise. For `h`, the entry before averaging is its fibre polynomial at

`(β_j−β_i+b'−b)/a_i`.

It has degree at most `M` in each of `b,b'`. Apply quadrature in each variable. The compressed matrix is exactly the original Gram matrix of `h` on the `g_i`. Thus the corresponding compression of `p+h` is `Gram_h(g)+P_N`.

Every compressed index is bounded by `κ(p+h)`. Lower semicontinuity at the Hermitian limit gives `index(Gram_h(g))≤κ(p+h)`; the empty family contributes zero. Taking the supremum proves `κ(h)≤κ(p+h)`. Positivity of `p` gives the reverse inequality.

## Consequences

Taking `h=ψ∘slope+Q`, with `Q` polynomial on translation fibres and zero on dilations, gives

`κ(ψ) ≤ κ(ψ∘slope+Q) = κ(p+ψ∘slope+Q)`.

The first inequality is restriction to the dilation subgroup. This strengthens the [slope-index comparison](polynomial-translation-corrections-cannot-lower-the-slope-index.md): the positive Haar summand preserves the entire residual index, not only the slope contribution. No additivity between slope and polynomial terms is asserted.

## Lean formalization

`AdelicKreinGeometry/Haar/PolynomialIndexPreservation.lean` proves
`negIndex_add_positive_haar_polynomial`, including infinite indices. Its corollaries
`negIndex_positive_haar_slope_polynomial_eq`,
`negIndex_slope_le_positive_haar_polynomial`, and
`negIndex_positive_haar_slope_polynomial_le` give the exact residual index and
both slope/polynomial bounds.

Polynomial reproduction and separated rational grids are in
`BiarithmeticGeometry/Affine/PolynomialQuadrature.lean`, `SmallTranslationGrids.lean`,
and `TranslationQuadrature.lean`. `HeckeKreinToeplitz/Index/WeightedGrams.lean`
provides the compression and positive-matrix bounds.

All five modules passed direct `lake --old env lean` audits. The printed endpoint
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
