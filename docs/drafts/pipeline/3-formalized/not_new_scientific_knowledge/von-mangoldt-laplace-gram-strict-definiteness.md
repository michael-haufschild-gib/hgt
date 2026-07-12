# Von Mangoldt Laplace Gram strict definiteness

- **ID:** von-mangoldt-laplace-gram-strict-definiteness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) -- BRIDGE
- **Source:** the actual unsquared von Mangoldt prime-power Laplace channel
- **Statement:** Every finite resolved von Mangoldt Laplace Gram matrix on distinct positive nodes
  is positive definite; consequently its determinant is strictly positive.

## Theorem

For distinct positive real nodes `x_i`, let

\[
E_{ij}=-\frac{\zeta'}{\zeta}(1+x_i+x_j)
      =\sum_{n\ge2}\frac{\Lambda(n)}{n},n^{-x_i}n^{-x_j}.
\]

Lean proves

\[
E\succ0,
\qquad
\det E>0.
\]

The earlier source theorem established only `E` positive semidefinite.

## Strictness mechanism

It is enough to retain the powers of the single prime `2`.  For
`m=1,...,N`, their feature vectors are

\[
\bigl(2^{-m x_i}\bigr)_i.
\]

The base nodes `2^{-x_i}` are distinct, so these vectors form a diagonally shifted Vandermonde
matrix.  Hence every nonzero coefficient packet has a nonzero feature on at least one power
`2^m`.  Its von Mangoldt weight is strictly positive, while every other prime-power contribution
is nonnegative.  The full quadratic form is therefore strict.

This is classical exponential/Vandermonde Gram theory in the actual Euler-source coordinates.  It
is useful source infrastructure but is not classified as new scientific knowledge.

## Lean certificate

The implementation is `PrimeLaplaceGramStrict.lean`.  Principal declarations include:

- `resolvedStrictPrimeLaplaceGram_eq`
- `exists_primePower_feature_combination_ne_zero`
- `dotProduct_resolvedStrictPrimeLaplaceGram_eq_tsum`
- `vonMangoldtPrimeLaplaceGram_posDef`
- `det_vonMangoldtPrimeLaplaceGram_pos`

## Positive top-down consequence

The Euler block in the polar--prime--Gamma colligation has no finite-dimensional null direction.
Therefore a successful completed-source passivity theorem cannot obtain its sign by restricting to
an Euler-blind coefficient subspace.  It must construct a channel-resolved incidence section in
which the shifted polar, critical Mellin, and Gamma channels orient this full-rank Euler block.

This is compatible with the independent `constraint x orientation` geometry: the strict Euler
Gram supplies orientation on every finite prime packet, while translated differential relations do
not select how that orientation couples to the completed theta/Gamma constraint.

## Gates

- [x] 0 -> 1: strictness reduced to one prime-power ladder
- [x] 1 -> 2: Vandermonde and positive-series proof completed
- [x] 2 -> 3: exact module builds and the capstones are axiom-clean
- [ ] 3 -> 4: construct the cofinal completed-source incidence section and prove passivity
