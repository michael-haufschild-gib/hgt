# Square-root bounds for actual hyperelliptic orientation counts

- **ID:** RIAC-curve-orientation-square-root
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)
- **Lean:** [HyperellipticOrientationCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/HyperellipticOrientationCounts.lean)

## Independent arithmetic counts

Let `F` be a finite field of odd cardinality `q` and `f∈F[X]` squarefree
of odd degree `m`. For each `n≥0`, take the actual degree-`n!` extension
`E/F` and the finite point set `C(E)={(x,y):y²=f(x)}⊔{∞}`.

`B_n` counts Frobenius-stable `S_n`-orbits of `C(E)^n`. `A_n` counts
stable orbits of `C(E)^n×{±1}` for the action
`σ·(x,ε)=(σ·x,sign(σ)ε)`. Frobenius fixes the orientation label.
Both natural-number counts are defined directly from finite arithmetic
sets. Collisions and both labels in degrees zero and one are retained.

## Exact comparison and cancellation

For the actual reciprocal roots `α_i` of the hyperelliptic L-polynomial,

`A_n−B_n = [t^n](1+t)(1+qt)∏_i(1+α_i t)⁻¹`,

`|A_n−B_n| ≤ (2q+2)(n+1)^(m−1)(√q)^n`.

The coefficient identity only needs odd degree. The bound additionally
uses squarefreeness. Neither theorem assumes splitting, simple roots,
Weil-circle membership, a point-count formula, or a cancellation estimate.

## Proof

1. [Signed transporter counting](riac-elliptic-orientation-quotients.md)
   cancels collisions and converts the original cover-minus-base count
   into intrinsic orientations of invariant point supports.
2. [Principal minors](riac-orientation-determinant.md) identify that sum
   with `[t^n]det(1+tP_φ)` for the actual Frobenius permutation matrix.
   Its trace powers count actual fixed points.
3. [Fixed-field descent](riac-hyperelliptic-fixed-points.md) gives
   `Tr(P_φ^d)=q^d+1−Σ_i α_i^d` for each `1≤d≤n`; each such `d` divides
   `n!`. No equality for all iterates in a single ambient field is used.
4. [Finite-degree Newton comparison](riac-truncated-trace-comparison.md)
   identifies the required coefficients. Schur triangulation retains
   multiplicities; adjoining the actual root multiset makes positive
   power sums agree with those of `1,q` through degree `n`. Reciprocal
   multiplication preserves that finite-degree agreement.
5. The already derived Stepanov theorem proves every `|α_i|≤√q` without
   a splitting hypothesis. The product of geometric series has coefficient
   norm at most `(n+1)^(m−1)(√q)^n`; the two numerator factors cost `2q+2`.

## Lean declarations

`hyperellipticOrientationCoverCount`, `hyperellipticTupleOrbitCount`,
`matrixOrientationPolynomial_perm`, `hyperellipticOrientationCover_sub`,
`hyperellipticOrientationCover_bound`.

Direct Lean check and three transitive axiom audits: only `propext`,
`Classical.choice`, `Quot.sound`. The general trace-comparison module has
16 further clean audits.

## Boundary

At horizon `N=q^n`, the bound is `√N` times a polynomial logarithmic loss
for a fixed curve. Constants depend on `q` and the curve degree. No
uniform-genus estimate or integer-height transfer follows. Signed
cancellation of the actual integer indices,
`Σ_p index_p(N)=1−M(N)`, remains open.
