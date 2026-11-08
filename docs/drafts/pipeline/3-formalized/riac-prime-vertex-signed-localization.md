# Signed localization at arithmetic prime vertices

- **ID:** RIAC-prime-vertex-localization
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), signed localization
- **Result:** Actual local relative singular-homology indices summing to `1−M(N)`, with the connected-core correction retained.

## Arithmetic objects

On the prime-product realization, use
`F(x)_p=(p+1)x_p/Σ_q(q+1)x_q`. This preserves every face and cutoff,
is homotopic to identity, and fixes precisely the prime vertices.
The projective chart `y_q=x_q/x_p`, `q≠p`, identifies the open star
with the cone of supports whose union with `{p}` satisfies the product cutoff.
The local flow is `y_q(t)=exp(t(log(q+1)−log(p+1)))y_q(0)`.

Let `B_p` bound both upper mass `Σ_(q>p)y_q` and lower mass
`Σ_(q<p)y_q` by one. Its exit `E_p` has upper mass one.
The compact block has only the apex as a full invariant orbit, in its
interior; every escaping forward orbit crosses the compact exit.
The block contracts radially. Deleting lower coordinates deformation
retracts the exit onto the actual upper-link realization.
These constructions and the cubic-range index theorem are
[formalized](../3-formalized/riac-prime-vertex-exit-indices.md).

## Full localization theorem

Define `ι_p(N)=χ(H_*(B_p,E_p;ℚ))` using actual relative singular chains.
At a prime vertex `p≤N`, the all-cutoff comparison is

`ι_p(N)=Σ_(S: all q∈S prime and q>p, p·∏S≤N) (−1)^|S|`.

The empty face is included when `p≤N`. Invalid ambient labels contribute
zero. In `Fin(B+3)`, the construction uses precisely those labels; `B≥N`
contains every arithmetic face. The resulting formulas are

`Σ_p ι_p(N)=1−M(N)` for `N≥1`,

`Σ_(2p≤N) ι_p(N)=1−M(N)−#{p prime : N/2<p≤N}` for `N≥4`.

No local definition uses `M(N)` or the Weil form. The construction also proves
finite dimensionality of every rational local relative homology group, vanishing in high degrees,
and exact conjugacy between time one of the local flow and `F` in the chart.

## Proof mechanism

The [finite-face singular Euler theorem](../3-formalized/finite-face-singular-euler.md)
proves homology finiteness and the alternating face formula from the actual
positive-coordinate good cover, relative excision and inclusion-exclusion.
Apply it to the upper link. The contractible block and exit equivalence give
`ι_p=1−χ(upper link)`, hence the augmented face count above. Insert `p`
to identify upper-link faces with faces whose least vertex is `p`.
These classes partition all nonempty prime faces. Their product bijection
with squarefree integers gives the Mertens identity. Upper-half prime
components each have empty exit and index one, yielding the core correction.

## Lean verification

[PrimeVertexSignedLocalization.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeVertexSignedLocalization.lean)
proves `primeVertexRelativeHomology_finite`,
`primeVertexRelativeIndex_eq_signedCount`, `primeVertexRelativeIndex_sum_mertens`,
`primeCoreVertexRelativeIndex_sum` and `primeVertexMap_projective_conjugacy`.
The production file passed its direct Lean check. Eleven capstone audits use
only `propext`, `Classical.choice` and `Quot.sound`; the generic singular-homology
bridge passed the same audit.

## Scope and classical comparison

The verified cubic formula is `ι_p(N)=1−#{q>p prime : pq≤N}` for
`p≤N≤p³`; Bertrand intervals prove these indices are unbounded below.
Signed local indices therefore permit cancellation despite many fixed points.
The construction supplies no quantitative cancellation bound, product-formula
height or dependence on the imaginary zero parameter.

[Banchoff's polyhedral critical-point theory](https://www.math.brown.edu/tbanchof/swork/cpacfep.html)
and [Conley index foundations](https://www.impan.pl/en/publishing-house/banach-center-publications/all/47/0/110882/on-foundations-of-the-conley-index-theory)
are classical predecessors. The construction concerns explicit arithmetic
isolating pairs and their relative singular Euler characteristics. A general
identification with Brouwer fixed-point index is a separate assertion.
