# Exact graph closure of the prime augmentation

- **ID:** RIAC-prime-boundary-closure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Completed prime boundary](riac-completed-prime-boundary.md)

## Statement

Let `j_δ` embed finite prime chains in their Hilbert completion `H` with
squared norm `Σ_p p^δ|a_p|²`, and let `d_s(a)=Σ_p p^(−s)a_p`.
The actual finite-support graph is `G={(j_δ(a),d_s(a))}`. For every
`s∈ℂ` and `δ∈ℝ`,

- if `2 Re(s)+δ>1`, `closure(G)=graph(φ_s,δ)`, where `φ_s,δ` is the
  unique bounded Riesz extension;
- if `2 Re(s)+δ≤1`, `closure(G)=H×ℂ`.

Consequently `G` is dense in the whole product exactly in the second region.

## Proof

In the bounded region the extension agrees with every finite boundary.
Its closed graph contains `G`, hence contains its closure. Conversely,
finite chains are dense in `H`; continuity of `u↦(u,φ_s,δ(u))` puts
every point of the extension graph in `closure(G)`.

In the complementary region the established finite unit-response packets
put `(0,1)` in `closure(G)`. This closure is a complex linear subspace,
so it contains every `(0,z)`. Subtracting `(0,d_s(a))` from each finite
graph point gives `(j_δ(a),0)`. Density of `j_δ` and closedness give every
`(u,0)`; addition gives the entire product. In the bounded region `(0,1)`
is excluded from the graph, proving the converse in the density criterion.

## Scope and positive survivor

The theorem classifies the scalar closed relation while retaining the
original finite boundary and prescribed conductor norm. It concerns the
union of all finite cutoffs. The positive survivor is the exact bounded
graph above the threshold and the complete relation classification elsewhere.

The [critical exterior theorem](riac-critical-exterior-graph-closure.md)
gives the whole-product classification in every exterior degree at and
below the same threshold. Bounded-region
[higher-degree contraction](../0-backlog/riac-completed-prime-koszul.md),
zero detection and square-root signed cancellation remain open.

## Lean statements

[PrimeBoundaryGraphClosure](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeBoundaryGraphClosure.lean):
`primeWeightedGraphSubmodule_coe`, `primeWeightedBoundary_closure_eq_univ`,
`primeWeightedBoundary_closure_eq_graph`, `primeWeightedBoundaryGraph_dense_iff`.

The direct module check passes. All four printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
