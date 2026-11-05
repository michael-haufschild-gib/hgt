# Distinct coherent clusters have the multiplicity threshold

- **ID:** distinct-coherent-clusters-have-the-multiplicity-threshold
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A36, distinct-ordinate obligation.

## Statement

Fix `k≥1`, `0<δ≤1/2`, `0<a≤L/2`, a centre `γ₀`, and any `ε>0`.
Every configuration consisting of the doubled on-line lattice of density `L`
and `k` simple reflected pairs at depth `δ`, with distinct ordinates
`|γ_j−γ₀|<ε`, is window-positive at `a` if and only if

`k·pairEnergy(δ,a)≤L`.

Above this threshold there are distinct ordinates in every such neighbourhood
and a compact `C²` test with negative Weil form. The equivalence quantifies over
all clusters in the neighbourhood; it does not assign the same onset to each
fixed distinct cluster.

## Proof

[PROVED HERE] The existing multi-pair lower bound is

`Re W(f,f) ≥ 2(L−Σ_j pairEnergy(δ,a))∫|f|²`.

It gives positivity whenever `k·pairEnergy≤L`, for every choice of ordinates.

If `L<k·pairEnergy`, the exact multiplicity-pair theorem supplies a compact
`C²` test `f`, supported in `[-a,a]`, whose form is negative for multiplicity
`k` at `γ₀`. Its transform `F` is entire. For `γ_j(t)=γ₀+t j`, define

`G(t)=2L∫|f|²+Σ_j 2Re(F(γ_j(t)−iδ) conjugate(F(γ_j(t)+iδ)))`.

This finite sum is continuous and `G(0)<0`. Hence `G(t)<0` for all sufficiently
small positive `t`. Choose also `tk<ε`. The ordinates are distinct and lie
within `ε` of `γ₀`; the exact multi-pair identity identifies their Weil form
with `G(t)`. This proves failure of universal positivity above the threshold.

## Lean inputs

- `windowPositiveAt_multiplicityPairConfig_iff`, `W_multiplicityPairConfig`.
- `W_multiPairConfig`, `re_W_multiPairConfig_ge_of_nodes`.
- `RHTower.EvenSector.differentiable_paperFT_of_compact`.

## Lean result

`WindowVisibilityLaw/DistinctCoherentClustersHaveTheMultiplicityThreshold.lean`:

- `exists_distinct_cluster_negative_of_lt_pairEnergy`.
- `windowPositiveAt_all_distinct_clusters_iff`.

Direct source check passed. Both transitive axiom audits report only
`propext`, `Classical.choice`, `Quot.sound`. The WVL umbrella imports the module.
