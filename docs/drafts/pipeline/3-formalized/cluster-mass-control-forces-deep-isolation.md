# Cluster mass control forces deep isolation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** Necessary geometry of the original `ClusterAt` exterior bound.
- **Statement:** If `ClusterAt` holds at a zero on or right of the critical
  line, every equally deep or deeper zero at a different ordinate must obey
  `4 ≤ κ(N,M)(1+(δ|γq−γρ|+1/10)²)`.

## Mechanism

Choose the opposite endpoint of the target's permitted centre window.
The companion lies outside the sector and hence outside every eligible
core. Its singleton mass already costs at least
`(∫v) exp(bρ((M+1)h−δ))/(1+(δ|γq−γρ|+1/10)²)`.
Compare with the allotted quarter-Turán signal. Multiplicity only
strengthens the lower bound.

## Consequence

Since `κ≤1`, a distinct ordinate within `1/δ` at equal or greater depth
precludes `ClusterAt`, irrespective of the allowed core cardinality.
Thus bounded clusters alone cannot discharge this particular mass
condition. The positive statement is an explicit necessary separation
law. Distinct ordinates of right-half-strip zeros satisfying `ClusterAt`
are consequently separated by more than `1/δ`; this follows by applying
the obstruction to the shallower member of each pair.
Width-centred box-camera bounds remain valid; general geometry
needed by that replacement receiver remains open.

Lean: `clusterAt_forces_deep_ordinate_gap`,
`not_clusterAt_of_nearby_deep_zero`, and
`clusterAt_distinct_ordinates_separated` in
`MultiscaleMollifiedZetaField/ClusterMassControlForcesDeepIsolation.lean`.
Single-file Lean check passed. No claim about existence of such ζ pairs.
