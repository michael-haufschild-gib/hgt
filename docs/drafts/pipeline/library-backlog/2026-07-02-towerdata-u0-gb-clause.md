# Ticket: U0 GB-clause for `bottcher_towerDataG` (one small delta, closes U0_phi)

`Bottcher.bottcher_towerDataG` (in-flight, BottcherTowerData.lean) produces the single-coordinate
tower certificate for `φ_c`. The U0_phi capstone consumes the SAME certificate through
`U0TowerBridge.u0_phi_independence_of_towerData` (proven, axiom-clean) with two additional
clauses, both cheap given the construction:

1. **`GBExt` clause**: a germ `GBExt : analyticSubring Ext` with
   `restrictAnalytic hUExt GBExt = u0AnSub hU_ext` — i.e. `u₀` continued to `Ext`.  Since `u₀`'s
   natural boundary is the unit circle, this is equivalent to `Ext ⊆ {z | 1 < ‖z‖}`
   (then `GBExt := u₀-germ on Ext` directly).
2. **`U ⊆ U0NaturalBoundary.Ext`**: automatic — `U ⊆ escapeOpen c` gives `2 < ‖z‖` on `U`.

For (1): the tower image `P0` and the deep lobes at depth `k ≥ 3` avoid the closed unit disk for
`‖c‖ ≥ 5` by the Green bound (points `‖z‖ ≤ 1` have `G(z) = G(f²z)/4 ≥ (2 log‖c‖ − 2)/4 ≈ h`,
while the depth-`k` pieces sit at levels `≤ 2h/2^k`); the shallow connector pieces need the
arc-gap: their norms are `≥ sqrt(gap·‖c‖)` since the σ-sections avoid the critical-value angle.
Threading these norm bounds through `exists_scaffold_chain`/`exists_matched_lobes` (where the
quantitative data lives) is natural in your construction and foreign as a bolt-on.

Useful proven bricks (U0TowerData.lean, axiom-clean): `tower_iterate_eq`
(`f^[m](T v) = T(v^{2^m})` with monotone-modulus intermediates), `radicand_welldef`
(dyadic-power agreement of two tower hits of one orbit).

With (1)+(2) added to the producer's Ext (either in `bottcher_towerDataG` directly for
`‖c‖ ≥ 5`, or as a variant), U0_phi closes by direct application — zero further wiring exists on
the U0 side.

## Update (same day): corrected geometry — the pinch, and the exact remaining bound

`bottcher_towerDataG` + `bottcher_transcendental_of_escape` landed (sorry-free, gate green) —
congratulations; the q62 Kummer core is closed unconditionally.

For the U0 GB-variant, the original sketch above is INCOMPLETE in one place: near the critical
saddle z = 0 the level curves at G = h + δ pass within ≈ sqrt(2δ‖c‖·(Hessian scale)) of 0, so a
tower image with log rlo − h → 0 genuinely enters the unit disk near the pinch — u₀ cannot
extend to that Ext, for ANY c. The fix that survives:
1. RESTRICT the tower to the sub-annulus with log rlo' ≥ h + 1/2 (a `TowerSection` restricts to
   any sub-annulus; the k-room comes from R₀ = M-large, NOT from rlo ↓ h) — then the P0-piece
   stays ≈ sqrt(‖c‖)-far from 0;
2. the deep lobes avoid the disk by POSITION (near the K_c-halves at ±sqrt(−c)), and the σ-connectors
   by the arc-gap norm bound sqrt(gap·‖c‖) — as before;
3. the ONLY genuinely new analytic input is the quantitative saddle bound for (1): points of the
   closed unit disk have G ≤ (2 log(‖c‖+1) + 2)/4 < h + 1/2 for ‖c‖ large — NOTE this is an
   UPPER bound on disk-G versus the P0-floor h + 1/2, i.e. G(z) ≤ (G-bound on f²(z))/4 with
   ‖f²(z)‖ ≤ (1+‖c‖)² + ‖c‖ — an ELEMENTARY two-iterate estimate (no Hessian needed!), giving
   disk ∩ {G > h + 1/2} = ∅ once (2log(‖c‖+1)+2)/4 ≤ h + 1/2, which holds for ‖c‖ ≥ C₀ since
   h = G(c)/2 ≥ (log(‖c‖/2))/2.  With (1)–(3), Ext ⊆ {|z| > 1} and GBExt := the u₀-germ.
So the GB-variant = your construction verbatim + the sub-annulus restriction + three elementary
norm estimates. My banked bricks (`U0TowerData.tower_iterate_eq`, `radicand_welldef`) and the
consumer (`U0TowerBridge.u0_phi_independence_of_towerData`) are ready.
