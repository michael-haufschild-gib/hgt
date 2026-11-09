# The critical Green kernel on projective p-adic vertices

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B133: realize the local resolvent on the actual adelic carrier.

For `g∈GL₂(ℚ_p)`, set `M(g)=maxᵢⱼ|gᵢⱼ|_p` and
`R(g)=|det g|_p/M(g)²`. Prove that

`G_s(gK,hK)=p^s/(p^(2s)−1) · R(g⁻¹h)^s`

is well-defined on `PGL₂(ℚ_p)/PGL₂(ℤ_p)` and satisfies
`(p^s+p^(1−s)−A_p)G_s(x,·)=δ_x` for every `s>0`, with the
actual prime adjacency already constructed in
`ThePrimeAdjacencyOnTheAdelicCarrier.lean`.

## Matrix reduction

Integral multiplication cannot increase `M`, by the ultrametric inequality;
applying the inverse gives equality for integral units. Scalar multiplication
cancels from `R`. Move a maximal entry to the upper left. Integral row and
column shears reduce `g`, up to scalar, to `diag(1,d)` with
`0<|d|_p=R(g)≤1`. Hence `R=1` precisely at the base vertex.

For `|d|_p<1`, discreteness gives `|d|_p≤p⁻¹`. Among the actual neighbour
representatives `diag(1,p)` and `[[p,−b],[0,1]]`, `b∈𝔽_p`, the term
`b=0` has ratio `pR`, and the other `p` terms have ratio `R/p`.
At `|d|_p=1`, all `p+1` ratios equal `1/p`. This proves the resolvent
identity directly, without presupposing a tree identification.

## Remaining scope

The matrix invariance, reduction and neighbour law require formalization.
This local kernel alone supplies neither the globally periodized operator
nor Weil's diagonal. Those remain the targets of the global carrier card.
