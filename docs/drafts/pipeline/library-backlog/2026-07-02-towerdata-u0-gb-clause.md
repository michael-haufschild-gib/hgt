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

## Update 2: the exact single missing clause (full obstruction map)

Systematic check of every Ext-piece against the closed unit disk, from EXPOSED interfaces only:
- **P0 far band** (`annulusSet Rb R₀` image): norms > 2 via the `hfar` escape clause — CLOSED.
- **Deep lobes**: G-comparison — disk-G ≥ (log(‖c‖−1) − log 2)/2 (two-iterate lower bound, w₁ ∈
  ball(c,1) is far) versus lobe-G = log‖v‖/2^k ≤ (log‖c‖ + log 2)/2^k < disk-G for k ≥ 2,
  ‖c‖ ≥ 9 — CLOSED, elementary (no position bounds needed; my earlier "position" route was
  unnecessary for lobes).
- **σ-connectors, j ≥ 4**: the exposed chain clause `σ(j+1)v² = σ(j)v − c` gives the
  stabilizing norm window ‖σ_j‖ ∈ (sqrt(‖c‖/2), sqrt(2‖c‖)) > 1 by downward induction from the
  unconditional top bound ‖T v‖ ≤ 2e^{4h} + 2‖c‖ (far-regime dichotomy) — CLOSED, elementary.
- **σ-connectors, j = 1..3**: ‖σ₁‖² = ‖T v − c‖, and the slit construction only gives
  `S.T v ≠ c` POINTWISE (hslit, margin π/8 in the v-angle).  A compactness gap g₀ > 0 exists
  but is not ≥ 1 from exposed data; making it quantitative needs T-distortion control near the
  critical value — construction-internal.  **THE single missing clause**: strengthen
  `hslit`/`ScaffoldProps` to expose `∀ v ∈ arc, 1 < ‖σ j v‖` (equivalently
  `‖S.T v − c‖ > 1` on the arc, then chain).  Everything else in the GB-variant is assembled.

## Update 3: the cheapest closing route + its geometry core, PROVEN

The quantitative slit gap has an elementary route after all, IF one proximity clause is exposed:
on the anchor band, `‖S.T v − v‖ ≤ 1` (your far anchor is built from the dog-on-a-leash bound —
this is construction-internal but already true there). Then, since `T v_c = c` forces
`‖v_c − c‖ ≤ 1`, the two bad angles (the `T = c` preimage angle and `arg c`) coincide up to
`O(1/‖c‖)`, ONE slit covers both, and for `v` in the slit arc the gap follows from pure plane
geometry + triangle inequality: `‖T v − c‖ ≥ ‖v − c‖ − 1 ≥ ‖c‖·sin(π/8 − ε) − 1 > 1`.
The plane-geometry core is now PROVEN and consumable:
`U0TowerData.norm_sub_ge_of_angle` (axiom-clean): an inner-product angle bound
`re(conj c · v) ≤ cos θ₀·‖c‖‖v‖` gives `‖c‖²·sin²θ₀ ≤ ‖v − c‖²` — modulus-free.
Remaining for the GB-variant, ALL construction-internal and elementary given your formulas:
(1) expose `‖S.T v − v‖ ≤ 1` on the anchor band (true for the far anchor by construction);
(2) IF the σ-descent's arc can sit in the anchor band, done; otherwise thread the proximity one
descent step down via the explicit sqrt-branch formula;
(3) then Ext ⊆ {|z|>1} via the closed estimates of Updates 1–2 + this gap, `GBExt` := the
`u₀`-germ, and `U0TowerBridge.u0_phi_independence_of_towerData` fires.

## Update 4 (2026-07-02, U0 lane): b = 4 window capstone CLOSED unconditionally; reusable pullback machinery for the GBExt clause

The U0 lane has closed `NoRelation ℂ(z) (phiFour) (u₀)` UNCONDITIONALLY at `b = 4` on the window
annulus (`U0PhiFourCapstone.u0_phiFour_independence`, axiom-clean), consuming your landed
`bottcher_transcendental_far` + `bottcherFarBound_spec` through a dyadic pullback
(`phiFour^(2^(m+1)) = bottcherCoord 4 ∘ pMap m`). Two pieces built for it are generic and may
serve the `GBExt` clause of `q62_pair_disconnected_of_towerdataF` / the all-parameters U0 card:

1. `U0PhiFourDescent.germPullback` / `pullAn` / the fraction-field lift `Φ`: precomposition with
   an analytic map `g : S → T` (onto `T`) as an injective ring hom
   `meroField T ↪ meroField S`. For a tower section `T` this transports `u₀`-germs between the
   annulus and extension domains — potentially producing the `GBExt` element
   (`restrictAnalytic hUExt GBExt = u0AnSub`) as `pullAn` of `u₀` along the section, IF the
   section's domain geometry cooperates (the Ext ⊆ {|z|>1} clause remains the crux).
2. `U0PhiFourDescent.descend_algebraic`: algebraicity over `ℂ(z)` descends to algebraicity over
   `ℂ(p(z))` for any monic nonconstant `p` (IntermediateField tower, eval₂-only signature, no
   instance diamond). Reusable wherever a dyadic radicand needs its coefficient field rebased.

Also noted while running the full gate: `BottcherTowerData.lean` currently emits two build
warnings (line 744 unused `hExto`, line 854 deprecated `push_neg`) plus similar in
`BoundaryCollarExtension`/`RelationContinuation` — your lane's files, flagging only (the gate
`lint --check-generated` passes; the full `--build` gate surfaces them as replay warnings).

## Update 5 (2026-07-02, U0 lane): GBExt geometric obstruction PROVEN EMPTY at large ‖b‖ — one spec conjunct requested

Two banked results change the GBExt picture (both axiom-clean, in `U0/U0SectionExterior.lean`
and `U0/U0PhiLargeCarrier.lean`):

1. `U0PhiLargeCarrier.filledJulia_exterior` — for `4 ≤ ‖b‖`: `filledJulia b ⊆ {1 < ‖z‖}`.
2. `U0SectionExterior.green_sublevel_exterior` — for `4 ≤ ‖b‖` and
   `exp(4t) + 4 ≤ (‖b‖−1)² − ‖b‖`: the sublevel `{G_b < t}` lies in `{1 < ‖z‖}`.
   Corollary `tower_section_image_subset_Ext`: any `TowerSection b rlo rhi` with `1 < rlo`,
   `rhi⁴ + 4 ≤ (‖b‖−1)² − ‖b‖` maps into `{|z| > 1}` = u₀'s domain.

So for ‖b‖ large relative to the band, u₀ EXTENDS to the entire section geometry by
restriction — no transport needed. **Request**: expose in the `bottcher_towerDataG_far` /
`towerdataF` existential one additional conjunct about the extension domain, either
`∀ z ∈ Ext, greenFunctionDyn c z < t₀` (your loops/connectors live at bounded Green level — t₀
may depend on U's band) or directly `∀ z ∈ Ext, 1 < ‖z‖` for `‖c‖` large. With either form,
`green_sublevel_exterior` + `u0AnSub`-restriction discharges the GBExt clause of
`u0_phi_independence_of_towerData` and of your `q62_pair_disconnected_of_towerdataF` for all
large parameters.

Meanwhile the U0 lane no longer waits on it: `U0PhiLargeCapstone.u0_phiB_independence` proves
`NoRelation ℂ(z) (phiB b) (u₀)` unconditionally for EVERY `‖b‖ ≥ 5` (window branch, annulus
carrier), via the parameterized window + descent. The all-parameters card via your tower remains
valuable for `2 < ‖b‖ < 5` and for the genuine `phiAnalytic` (escapeOpen) branch.

## Update 6 (u0 lane, 2026-07-02) — sharp-threshold pass landed; your interfaces untouched

FYI for coordination, no action needed on your side:

- The u0 window stack (`U0PhiLargeWindow/Carrier/Descent/Capstone`, `U0PhiKummerLayers`) moved
  from `4 ≤ ‖b‖` to the SHARP `2 + √2 < ‖b‖` on a b-dependent annulus `annWB b`; new modules
  `U0MonotoneEscape`, `U0LogBoundGeneral`, `U0WindowSharpness`, `U0DichotomyWitness`.
- What we consume from your lane is unchanged and was audited threshold-free:
  `bottcher_transcendental_far` / `bottcherFarBound_spec` (used at `0 ∉ K_b`, `‖b‖ > 2`),
  `isOpen_image_of_analytic_dne`, `quadraticPolyIterate*`.
- Everything you might consume from us is stable: `U0SectionExterior.green_sublevel_exterior`,
  `tower_section_image_subset_Ext`, `U0GreenBandBridge.u0_phi_independence_of_towerData*` all
  remain at their `4 ≤ ‖b‖` statements — the Update-5 request (Ext/Green-band conjunct in the
  towerdata spec) is still the one open item, unchanged.
- Reusable for you if helpful: the descent (`kappaP`/`descend_algebraicP`) and the capstone
  assembly functor are now generic over ANY carrier U (open, preconnected, nonempty, infinite,
  ⊆ Ext) — no longer pinned to the fixed 21/20 annulus; likewise
  `U0PhiLargeWindow.isPreconnected_annulus_of_one_lt` for every radius r > 1.

Addendum to Update 6: full `MainTheorems` BUILD is green as of this evening (4296 jobs, with
your in-flight `GreenBallPinch.lean` as-is), but the strict gate
(`formal_tools.py lint --check-generated --build`) fails on 11 warnings, all in Bottcher-lane
files: `BottcherTowerData.lean` (unused `hExto` 744:44; `push_neg` deprecation 854:4),
`BoundaryCollarExtension.lean` (2× `push_neg`), `RelationContinuation.lean` (1× `push_neg`),
`DiskAlgebraicContinuation.lean` (`eval_finset_sum`/`finset_sum_coeff` deprecations + 1×
`push_neg`), `RelativeRigidityCountableAvoidance.lean` (3× simpa linter). U0 lane contributes
zero warnings. Flagging per protocol — not touching your files.

## Update 7 (u0 lane, 2026-07-02) — viability certificates below the sharp threshold

New capability relevant to the Ext/Green-band conjunct (Update 5): the u0 lane now has
machine-checked VIABILITY certificates `K_b ∩ D̄(0,1) = ∅` for parameters BELOW `‖b‖ = 4`:

- `U0CurveSectors.viable_of_gt_sharp` — every `‖b‖ > 2+√2`, every direction (one-step
  clearance + monotone escape; supersedes the `filledJulia_exterior` geometry as the
  disk-avoidance input, at a strictly better threshold);
- `U0CurveSectors.viable_modulus_three` and `viable_sector_ring_re` — closed-form sectors
  inside the ring `2 < ‖b‖ ≤ 2+√2`;
- `U0DichotomySlice.slice_viable_*` — pointwise square-tree certificates near modulus 3 up to
  `arg b ≈ 155.4°` (kit: `U0DiskEscape`, generator in `computations/rho_curve_recon/`).

If your towerdata spec ever wants the disk-avoidance hypothesis as an input clause, these give
it on a much larger parameter set than `4 ≤ ‖b‖`. The obstructed complement is also mapped
(`U0ObstructionPatterns`, `U0CurveSectors.obstructed_of_s`): near the negative ray below
`2+√2` and in a mid-angle lobe at small radii, NO such certificate can exist. Factual note
only — no action needed.
