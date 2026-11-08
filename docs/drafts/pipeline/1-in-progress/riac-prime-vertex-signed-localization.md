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
the prime vertices; the map, homotopy and fixed-point classification passed
the scratch Lean check. Production audit remains pending. The construction uses prime labels, independently of
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
realization. These chart, flow and retraction constructions are being
formalized; the singular-relative-homology comparison is still open.

For `p>√N`, the upper link is empty. For `p³>N`, it has no edges, so
the proposed local index reduces to `1−#{q>p : pq≤N}`. These are
arithmetic consequences to verify after the exit-pair comparison.
