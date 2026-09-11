# Path cochains: an explicit three-vertex reduction

**Status:** paper proof for the next topology dependency; not formalized. This is an elementary proof of the classical path-independence-complex suspension law, not a novelty claim. It supports the spectrum branch in `../1-in-progress/chronological-topological-spectrum.md`.

## Actual face complex and grading

Let P_n have vertices 0,…,n−1 and edges between consecutive integers. Faces are all nonadjacent subsets, including the empty face. Reduced cochains are functions on these faces. A cochain in occupation degree j is supported on faces of cardinality j; its topological degree is j−1. The coboundary is the usual alternating sum over vertex deletions. Thus the empty-face slot is included and the differential raises j by one.

The corpus already proves the incidence-sign identities, δ²=0, and full-simplex cone contraction in `SimplicialCochainComplex.lean` and `SimplexConeContraction.lean`. These are suitable algebraic primitives. Existing `HochsterCohomologyEquiv.lean` defines actual reduced-cohomology quotients, but its codimension indexing needs care; do not replace graded cohomology with an Euler-count recurrence.

## Explicit reduction for n≥3

Write B for the tail path on vertices 3,…,n−1. Define maps on face cochains:

`(Kf)(σ) = 0` if 0 or 1 belongs to σ; otherwise `(Kf)(σ)=f({0}∪σ)`.

`(qf)(τ)=f({1}∪τ)−f({0}∪τ)` for tail faces τ.

`(Jg)(σ)=g(σ\{1})` if 1 belongs to σ; otherwise `(Jg)(σ)=0`.

All faces in these evaluations are legitimate. If 1∈σ, the path condition excludes 0 and 2, so σ\{1} lies in B. If 1∉σ, adjoining 0 is legitimate. K and q lower occupation degree by one; J raises it by one.

The exact identities on path faces are

`δK+Kδ = id−Jq`, `qJ=id`, `qδ=−δq`, `δJ=−Jδ`.

For σ containing 0, the sole nonzero contribution in δK removes 0, giving f(σ), and Jq and Kδ vanish. For σ containing 1, the sole nonzero contribution in δK removes 1 and equals f({0}∪(σ\{1})); Kδ vanishes, so the residual is qf. For σ containing neither 0 nor 1, the ordinary cone identity applies and Jq vanishes. The minus signs in the chain-map laws arise because the inserted vertex precedes every tail vertex; terms deleting that inserted vertex cancel in qδ. Also qJ=id follows directly since Jg vanishes on faces containing 0.

Consequently q and J induce inverse cohomology isomorphisms with a shift of one in occupation degree: every cocycle differs from Jqf by the explicit coboundary δKf, and q detects exactly when this residual is a coboundary. This proves `H̃^(j−1)(Ind(P_n)) ≅ H̃^(j−2)(Ind(P_(n−3)))` with the augmentation slots retained.

For natural-number indexing in Lean, state the shift as occupation `j+1` on P_(n+3) versus occupation j on P_n. Treat occupation zero on nonempty paths separately as zero. Do not let truncated natural subtraction turn a negative-degree group into the augmentation slot.

## Base cases and actual multiplicities

- n=0: only the empty face; one class in occupation degree 0.
- n=1: the two-term augmented simplex complex is exact.
- n=2: faces ∅,{0},{1}; the differential sends a scalar to the two equal singleton values. The difference of singleton values identifies one class in occupation degree 1; all other degrees vanish.

Induction gives one class in occupation j for n=3j or n=3j−1 (where the length is nonnegative), and none for n=3j+1. For the physical pairing paths n=2d−1, d≥1, this gives exactly one class at every occupation j≥1 across the whole degree tower. More explicitly, d=3k+2 supplies occupation 2k+1 and d=3k+3 supplies occupation 2k+2; d=3k+1 contributes nothing.

This is the grading needed for the eta trace. The coefficients must be obtained from this actual cohomology reduction in Lean; a function defined to equal these multiplicities would not establish the geometric spectrum.

## Implementation order

Define finite path faces and their relation to nonnegative separated-support probes. Prove the local maps and identities on actual face evaluations, reusing the existing sign and cone lemmas. Construct or connect the graded quotient and induced inverse maps. Then prove the base cases, the all-degree multiplicity classification, and the paired trace. Relabeling the tail by subtracting three requires an order-preserving bijection so that incidence signs transport correctly.
