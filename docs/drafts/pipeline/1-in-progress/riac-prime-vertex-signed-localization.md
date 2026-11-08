# Signed localization at arithmetic prime vertices

- **ID:** RIAC-prime-vertex-localization
- **Stage:** 1-in-progress
- **Type:** CONSTRUCTION
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md), signed localization
- **Target:** Construct an actual self-map of the prime complex, identify its isolated fixed vertices and prove local index formulas whose sum recovers its arithmetic Euler characteristic.

## Arithmetic map

On the actual barycentric realization of the prime-product complex, use
`F(x)_p=(p+1)x_p/(Σ_q (q+1)x_q)`. This preserves every face and cutoff, and
interpolating the positive weights from `1` to `p+1` gives a homotopy from
identity. Distinct prime weights force the fixed points to be exactly
the prime vertices. [PrimeVertexDynamics.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeVertexDynamics.lean)
formalizes the map, homotopy and fixed-point classification. The construction uses prime labels, independently of
`M(N)` and the Weil form.

## Local geometry and required comparison

Near vertex `p`, a coordinate in direction `q` expands precisely when `q>p`.
The proposed exit-link model consists of prime faces with labels greater
than `p` and product at most `N/p`. Its signed augmented face count is

`ι_p(N)=Σ_(S: all q∈S exceed p, p·∏S≤N) (−1)^|S|`.

A proof must identify this number with an actual local fixed-point or
relative Conley index of `F`; naming the combinatorial sum an index does
not discharge that comparison. Partitioning nonempty faces by their least
prime then gives the proposed localization `Σ_p ι_p(N)=1−M(N)`.
The connected core must retain its isolated-prime correction.

## Scope

This target permits many fixed points and signed indices. Upper-half prime
vertices remain isolated fixed points of index one. No square-root bound or
sign cancellation is assumed. The unresolved central step is the topological
local-index comparison, beyond the known Euler face partition.

## Actual local model

Use projective coordinates `y_q=x_q/x_p` for `q≠p`, with `y_p=0`.
The inverse inserts apex coefficient one and divides by `1+Σy_q`.
Allowed supports are precisely faces whose union with `{p}` satisfies the
original product cutoff. The local flow is

`y_q(t)=exp(t(log(q+1)−log(p+1)))y_q(0)`.

The candidate isolating block bounds both `Σ_(q>p)y_q` and `Σ_(q<p)y_q`
by one. Its forward exit has upper mass one. Deleting stable coordinates
linearly preserves that exit and retracts it onto the actual upper-link
realization. [PrimeVertexLocalFlow.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeVertexLocalFlow.lean)
formalizes the chart, continuous flow, compact block and exit, maximal
invariant set, interior condition, exit crossing, relative positive
invariance, block contraction and exit-to-link homotopy equivalence.
Both modules passed final Lean checks and standard-axiom audits. The
full-range singular-homology count comparison is still open.

For `p>√N`, the upper link is empty. For `p³>N`, it has no edges, so
the proposed local index reduces to `1−#{q>p : pq≤N}`. These are
arithmetic consequences to verify after the exit-pair comparison.

## Signed singular-homology target

Define the local integer by `χ(H_*(B_p,E_p;ℚ))` for the constructed
block and exit. At `p≤N≤p³`, the target is

`χ(H_*(B_p,E_p;ℚ))=1−#{q prime : p<q, pq≤N}`.

The block contracts radially. Its exit retracts onto the upper link.
Two distinct upper vertices would contribute `pqr>p³`, so this link is
a finite discrete space. Relative singular-homology additivity then
gives the displayed integer, without a face-sum definition of the index.
The construction and this singular-homology comparison are
[formalized](../3-formalized/riac-prime-vertex-exit-indices.md).

The local indices are also proved unbounded below. At `N=p³`, each
Bertrand interval `(2^j p,2^(j+1)p]`, for `j<k` and `2^k≤p`, supplies
a distinct upper neighbour below `p²`. Thus the index is at most `1−k`.
This is a local cancellation mechanism, with no global Mertens bound.

## Classical comparison

[Banchoff's polyhedral critical-point theory](https://www.math.brown.edu/tbanchof/swork/cpacfep.html)
is the classical predecessor for vertex Euler localization.
[Conley index foundations](https://www.impan.pl/en/publishing-house/banach-center-publications/all/47/0/110882/on-foundations-of-the-conley-index-theory)
provide the invariant-set framework. The arithmetic contribution sought
here is the actual prime-product flow, exit geometry and signed local
integer; neither general theory is claimed as new.
