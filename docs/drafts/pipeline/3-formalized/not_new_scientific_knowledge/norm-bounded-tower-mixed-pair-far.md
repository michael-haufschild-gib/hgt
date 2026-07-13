# Norm-bounded radical tower: mixed and small-second disconnected q62 closes

- **ID:** norm-bounded-tower-mixed-pair-far
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** closes task B8 (#131) and the far×small region of W4 (#90); consumes the banked
  Green pinch (`GreenBallPinch`), patch localization (`PatchSquareLocalize`), wedge-slit scaffold
  (`BottcherScaffoldChain`), and the mixed capstone (`MixedPairCapstone`).
- **Statement:** For every disconnected `c₁` with `‖c₁‖ ≥ 1000` the dyadic radical tower of
  `φ_{c₁}` can be built with extension domains satisfying `∀ z ∈ Ext, 2 < ‖z‖`
  (`bottcher_towerDataG_mixed`).  Consequently `NoRelation ℂ(z) (φ_{c₁}) (φ_{c₂})` holds
  unconditionally on a common far domain for (i) every connected `c₂ ∈ M ∖ {0, −2}`
  (`q62_phiMero_mixed_far`) and (ii) every disconnected `c₂` with `‖c₂‖ ≤ 2`
  (`q62_phiMero_pair_far_smallSecond`) — the latter a region beyond the level-compatible
  hypothesis of `bottcher_towerDataF_pair`.

## Mechanism

The tower's pieces are norm-floored individually. The deep section is raised to inner radius
`max rlo e^{G_{c₁}(0)+1/8}` (`TowerSection.restrictLo`), placing it above the `closedBall 0 2`
Green-pinch band; every scaffold piece of depth `≥ 2` (`log RW = 7h/2 ≤ 4h − 1/2`) and every
lobe (`log rb ≤ 2h − 1/4`) lies below it; the single Green-critical piece — the depth-1 scaffold
arc — is handled by placing the scaffold slit at the angle of the critical-value ball
(`exists_slit_center_avoiding_patch`), giving `‖σ₁ v‖² = ‖S.T v − c₁‖ > 4` directly; the far
region `{Bmin < ‖z‖}` is beyond `2` trivially. Both consumers then read
`Ext ⊆ {2 < ‖z‖} ⊆ escapeOpen c₂` (as `‖c₂‖ ≤ 2`), so `GBExt` is the genuine `φ_{c₂}` germ;
transcendence of `φ_{c₂}` comes from the connected natural-boundary route in case (i) and from
`bottcher_transcendental_far` in case (ii).

A prior plan for the norm floor (orbit-growth window against the full section, and the pure
Green band-avoidance variant) is refuted: the deep section spans Green values `(h, > 4h+2)`,
violating both window ends, and the octave `R₀ > rlo²` forces the scaled bands to cover the
pinch level. The slit-window route above is the one that closes.

## Lean surface

- `MixedTowerExt.lean` — `TowerSection.restrictLo`; `exists_tower_ext_slit` (the extension
  domain on the prescribed-slit scaffold, with the piecewise export `∀ z ∈ Ext, 2 < ‖z‖`).
- `MixedTowerData.lean` — `bottcher_towerDataG_mixed`, `bottcherMixedBound(_spec)`,
  `q62_phiMero_mixed_far`; `subset_escapeOpen_of_two_lt_of_norm_le_two`,
  `q62_phiMero_pair_of_normBoundedTower`, `q62_phiMero_pair_far_smallSecond`.
- Axioms: `[propext, Classical.choice, Quot.sound]` for all listed theorems; umbrella
  `GaloisForLFunctions.Bottcher` builds (4230 jobs); `formal_tools.py lint` passes.

## Residual

- Mixed and small-second closes require `‖c₁‖ ≥ 1000` (pinch and patch constants are calibrated
  at `‖c‖ ≥ 100/1000`); below that the tower descends into `closedBall 0 2` and ball-avoidance
  is impossible — the residual needs `K_{c₂}`-steering or recalibration.
- Disconnected `c₂` with `‖c₂‖ > 2`: needs the tower floor strengthened to `‖z‖ > ‖c₂‖`
  (ball-`s` pinch, feasible for `‖c₂‖ ≲ √‖c₁‖`) — carded on #90/#110.
- The steering route (02-A) alone cannot supply `GBExt`: arcs avoiding `K₂` do not prevent the
  odd loop from *encircling* `K₂` pieces, which is what makes `φ_{c₂}` multivalued below its
  critical level. Recorded on #110.

## Addendum: parametric `s`-floor and the quadratic-gap region (same session)

The whole chain generalizes from floor `2` to floor `s` with `2 ≤ s`, `s² ≤ ‖c₁‖/40`:
parametric pinch (`abs_greenFunctionDyn_sub_crit_le_s` and contrapositives), `s²`-patch slit
(`patch_square_mem_closedBall_s`, `exists_slit_center_avoiding_patch_s`), `s`-floor tower
(`exists_tower_ext_slit_s`, `bottcher_towerDataG_normS`).  Consequences, all axiom-clean:

- `q62_phiMero_pair_far_smallSecond` / `q62_phiMero_pair_far_smallFirst` — disconnected
  `‖c_big‖ ≥ 1000` × disconnected `‖c_small‖ ≤ 2`, both orientations.
- `q62_phiMero_pair_far_general` / `_swapped` — disconnected pairs with the quadratic norm gap
  `‖c_big‖ ≥ 1000` and `300·(max 2 ‖c_small‖)² ≤ ‖c_big‖`, both orientations: the tower floor
  `s := max 2 ‖c_small‖` places the extension domain inside `escapeOpen c_small` directly.
- `q62_phiMero_mixed_far_swapped` — the mixed close in the connected-first orientation
  (`noRelation_symm`).

Residual for the disconnected pair (#90): comparable-norm pairs outside the level-compatible
locus.  The steering route cannot close them as arcs alone (loop-encircling obstruction — see
task #110); candidate routes are loop-winding-vanishing around `K₂` or subregional `hlevel`
verification.

## Addendum 2: placement-free master + negative settlement of the comparable-norm shortcut

- `q62_phiMero_norm_gap` (banked, axiom-clean): `0 ∉ K_{c₁}`, `‖c₁‖ ≥ 1000`,
  `c₂ ∉ {0, −2}`, `300·(max 2 ‖c₂‖)² ≤ ‖c₁‖` ⟹ `NoRelation` — no Mandelbrot placement
  hypothesis on `c₂` (the dichotomy routes to the mixed or the both-disconnected close).
- The comparable-norm remainder of the disconnected pair admits NO assembly shortcut
  [settled by estimate]: deep tower points sit at norm `≈ √‖c₁‖ ≈ √‖c₂‖`, where
  `G₂ ≈ h₂ + O(1) < 2h₂` — so both the `hlevel` clause of `bottcher_towerDataF_pair` and a
  univalence-shell (`{G₂ > 2h₂}`) variant of the norm-bounded tower fail there structurally.
  The comparable case is equivalent to the loop-monodromy problem (odd loop with zero winding
  around every `K₂` piece) — recorded on tasks #90/#110 as the genuine open core of W4.

## Addendum 3 (2026-07-03) — linear-gap conditional capstone banked

The linear-gap lane is now fully wired in Lean, axiom-clean
(`propext, Classical.choice, Quot.sound`):

- `Bottcher.exists_tower_ext_slit_s_withRoot` (`W4LinPack.lean`) — the s-floored slit tower
  exporting, besides the radicand package, an analytic `Φ` on the slim `Ext` with
  `Φ^{2^m} = φ_{c₂} ∘ f_{c₂}^{[m]}` and `Φ ≠ 0`; conditional on the named interface
  `ChainOverlapsConnected` (preconnectivity of deep consecutive scaffold overlaps).
- `Bottcher.bottcher_towerDataG_linGapRoot` (`W4LinPack.lean`) — the pair-capstone-shaped
  builder: far domain, both germ identifications (`a₁` for `φ_{c₁}`, `a₂` for `φ_{c₂}`),
  per-depth `Ext/F/aExt/GBExt/k` with radical clause, GB clause, and odd loops.
- `Bottcher.q62_phiMero_linGap` / `q62_phiMero_linGap_swapped` (`W4LinCapstone.lean`, NEW) —
  **[PROVED HERE, conditional]** `NoRelation (RatFunc ℂ) (phiMero c₁) (phiMero c₂)` for
  disconnected `c₁, c₂` with `‖c₁‖ ≥ 1000`, `‖c₂‖ ≥ 2`,
  `(√(2‖c₂‖)+1)² ≤ ‖c₁‖/300` (linear gap `‖c₂‖ ≲ ‖c₁‖/600`), conditional on exactly two
  connectivity interfaces of the `c₁`-tower: `hconnAll : ChainOverlapsConnected …` and
  `hconnFar :` far-band preconnectivity of the section image. No measure theory enters.

Comparison: the unconditional `q62_phiMero_norm_gap` reaches `‖c₂‖ ≲ √(‖c₁‖/300)`
(quadratic gap); the conditional linear-gap close reaches `‖c₂‖ ≲ ‖c₁‖/600`.

**[OPEN CORE]** interface discharge (task #140): the 3-component sub-case of
`ChainOverlapsConnected` (σ₁ not odd breaks injectivity propagation; routes A holonomy /
B arc-width re-cut / C dyadic signs recorded), and `hconnFar` (graph-band topology, likely
provable from the section fields). Gate at banking: `lake build GaloisForLFunctions.Bottcher`
4234 jobs OK, lint OK, `#print axioms` clean on all four names above.

## Addendum 4 (2026-07-03) — far-band interface eliminated; one interface remains

The `hconnFar` hypothesis is GONE from the linear-gap chain — dissolved by a re-cut, not proven
as stated (for an arbitrary section and norm cut it is likely refutable: a wavy band truncated
by a circle can disconnect).  The second-coordinate glue in `bottcher_towerDataG_linGapRoot`
now runs over the green-superlevel set `Efar = {G_c > max(2h, bottcherBallBound c)}` instead of
the norm cut: by the section's `level` field, `Efar ∩ Ext = S'.T '' annulusSet (max rlo' e^{tE}) R₀`
— the continuous image of a round sub-annulus, preconnected with no hypothesis.  The radicand
(`F'`) glue keeps its norm cut (its seam identity needs deep-far arguments `‖w‖ > Rb`); the two
glues now use different far regions, related by `Afar ⊆ Efar` (`green_far_gt`, with `Bmin`
carrying one extra max-component `exp(bottcherBallBound c + 2)`).

`q62_phiMero_linGap` / `_swapped` are now conditional on EXACTLY ONE interface:
`ChainOverlapsConnected` (task #140, 3-component sub-case).  Gate re-run: build 4234 jobs OK,
lint OK, `#print axioms` clean on all three names.

## Addendum 5 (2026-07-03) — ChainOverlapsConnected: refuted as stated, discharge design complete

**[REFUTED as stated]** The universally-quantified interface is false, and even the banked
construction's instance is false for slit centers `θs < −3π/8`.  Analysis (exp-chart, window
`(α,β) = (θs+π/8, θs+2π−π/8)`, width `L = 7π/4`):

- `W := {w ∈ A : w² ∈ A}` decomposes into components `W_m` indexed by the fold integer `m`
  (`2t − 2πm ∈ (α,β)`); valid `m`-sets are `{0,1}`, `{−1,0,1}` (iff `α < −π/4`), or `{0,1,2}`
  (iff `α > π/2`) — never more, and `{−1}`,`{2}` are mutually exclusive.
- The equality locus of `h₁ = σ_{j+1}∘sq` and `h₂ = σ_j` (two sections of the `f^[j+1]`-fibre
  over `S.T∘sq`, equal targets via the section FE) is clopen per component (no critical points
  of the iterate at working levels: `2^{j−i} ∉ (5/4, 7/4)`).
- **Antipode kill**: `E` on two adjacent components (`Δm = 1`, angular shift `π`) is
  contradictory — `(−w)² = w²` forces `σ_j w = σ_j(−w)`, against injectivity.  Antipodal pairs
  always exist between nonempty adjacent components (interval arithmetic).
- **Far-pair forcing (the refutation)**: pulling the chain back to the simply connected radial
  band and closing on the double cover, ALL windings are even — level 1: `2·wind(S.T−c) = 2`
  (the level curve at `2 log ρ > 2h` encloses `c`); levels ≥ 2: `0` because the loop's green
  level `2 log ρ / 2^i ≤ 7h/4 < 2h = G(c)` puts `c` OUTSIDE (windInt_eq_zero_of_level_lt).
  Hence the transported tower closes, `E_m ⟺ E_{m+2}`, and in the `{−1,0,1}` configuration the
  banked fold-1 doubling window (`hσdbl`, which certifies `E` on the `m = 1` END component)
  forces `E_{−1}` too: the overlap is genuinely TWO pieces.  Both routes A (holonomy — the
  monodromy is trivial, so it cannot kill the far pair) and the fear behind the 3-component
  crux are settled by this computation.

**[DISCHARGE DESIGN — no open mathematics remains]** Fold-parity is a branch choice:
flipping the sign of `σ_{j+1}` swaps which fold-parity class of windows carries the doubling
identity, and fold-`p` windows exist for BOTH `p = 0` (`2J ⊆ (α,β)`, no shift — nonempty for
every `θs`) and `p = 1` (the banked `2J − 2π` window).  Choose per configuration:
`{−1,0,1}` → `p₀ = 0` (certified component `W₀` = middle); `{0,1,2}` → `p₀ = 1` (`W₁` =
middle); `{0,1}` → either.  Then the certified component is the ONLY component of its parity
class, and every other component is adjacent to it — killed by antipode.  So
`E`-locus = exactly the certified component, overlap `= σ_j''(that component)` — preconnected,
and nonempty (the window survives), which also feeds the glue's nonemptiness.  The proof needs
only: certified window + antipode + clopen + component decomposition — the transport is not
used in the positive direction.

Execution steps (all Lean, task #140): (1) generalize `exists_scaffold_chain_window` with a
fold-parity input `p₀ ∈ {0,1}` (fold-0 variant of `sq_mem_arcAnnulus` and the `J`-window
arithmetic); (2) thread the parity through the chain construction (sqrt sign per level);
(3) prove the re-cut interface (component decomposition in the exp chart, clopen equality via
local injectivity of the iterate, antipode intervals); (4) instantiate in
`exists_tower_ext_slit_s_withRoot` with the `θs`-config test; (5) drop `hconnAll` from
`bottcher_towerDataG_linGapRoot` — `q62_phiMero_linGap` becomes UNCONDITIONAL.

## Addendum 6 (2026-07-03) — ChainOverlapsConnected DISCHARGED; linear-gap q62 UNCONDITIONAL

**[PROVED HERE]** `Bottcher.q62_phiMero_linGap` / `_swapped` now carry NO interface hypotheses:
disconnected `c₁, c₂` with `‖c₁‖ ≥ 1000`, `‖c₂‖ ≥ 2`, `(√(2‖c₂‖)+1)² ≤ ‖c₁‖/300` satisfy
`NoRelation (RatFunc ℂ) (phiMero c₁) (phiMero c₂)` unconditionally.  Axiom-clean
(`propext, Classical.choice, Quot.sound`); build 4235 jobs; lint passed.

The discharge, per the addendum-5 design (all in `W4LinOverlap.lean` + `W4LinPack.lean` +
`BottcherScaffoldChain.lean`):

* toolbox — `sq_window_decomposition` (the squaring window = 3 fold slots under
  `α ∈ [−π/4, 7π/4]`), `sections_eventuallyEq_of_orbit_ne_zero` (covering sections through a
  noncritical point agree locally), `scaffold_orbit_ne_zero` (`2^{j−k} ∉ (5/4, 7/4)`),
  `agree_locus_all_or_none` (clopen dichotomy), `not_both_adjacent_folds_agree` (antipode kill,
  free real slot offsets), `scaffold_lobe_overlap_eq/_preconnected` (lobe clause via `S.inj`),
  `sq_mem_arcAnnulus_fold0`, `fold0_window_exists`, `arcAnnulus_shift_two_pi`;
* assembly — `scaffold_scaffold_overlap_preconnected`: the consecutive overlap equals
  `σ_j''S₁` (the certified fold slot) exactly;
* the interface as a theorem — `chainOverlapsConnected_of_normalized` for
  `θs ∈ [−3π/8, 13π/8]`;
* wiring — the chain lemma and `withRoot` now accept `θs ≤ 2π` (dead `hαbounds` removed, two
  `MixedTowerExt` call sites weakened), and `bottcher_towerDataG_linGapRoot` renormalizes the
  slit center by `+2π` when it falls below `−3π/8` (`arcAnnulus_shift_two_pi` transports the
  patch-avoidance clause), proves the interface inline, and no longer takes `hconnAll`.

The capstone surface rows in `formal/README.md`, `CLAUDE.md`, `AGENTS.md` gained
`Bottcher.q62_phiMero_linGap`.  The disconnected×disconnected branch of q62 now covers:
level-compatible pairs (original), quadratic gap (unconditional), linear gap `‖c₂‖ ≲ ‖c₁‖/600`
(unconditional) — the remaining open regime is comparable norms (OP16-A, task #138/#90).

## Addendum 7 — concrete finite-root-tower capstones (`Bottcher.q62_phiMero_*_roots`)

The abstract two-coordinate Kummer descent `KummerRootApplications.noRelation_pow_descent_both`
(`χ^m = F`, `η^n = G`, `NoRelation K F G ⟹ NoRelation K χ η`; descend first coord, flip with
`Bottcher.noRelation_symm`, descend second, flip back) is field-generic, so it applies to the two
shipped disconnected-pair capstones directly.  `GaloisForLFunctions/Bottcher/Q62RootTower.lean` (top-level,
imported by `MainTheorems`) instantiates it at the CONCRETE inverse-Böttcher coordinates:

* `q62_phiMero_linGap_roots` — for the linear-gap regime (`‖c₁‖≥1000`, `‖c₂‖≥2`,
  `(√(2‖c₂‖)+1)² ≤ ‖c₁‖/300`), on the common far domain `U` every `p`-th root of `φ_{c₁}` in
  `meroField U` is algebraically independent over `ℂ(z)` of every `q`-th root of `φ_{c₂}`;
* `q62_phiMero_norm_gap_roots` — same conclusion for the quadratic-gap/mixed regime
  (`‖c₁‖≥1000`, `c₂∉{0,-2}`, `300·(max 2‖c₂‖)² ≤ ‖c₁‖`), consuming `q62_phiMero_norm_gap`.

So the finite-root-tower independence is now stated at the genuine Böttcher coordinates, not only
abstract field elements: every `2^j`-th Böttcher root of one coordinate is independent of every
`2^k`-th root of the other in the two unconditional gap regimes.  Axiom-clean
(`propext, Classical.choice, Quot.sound`); the Böttcher-lane files are untouched — the file only
consumes the two capstones and the descent.  Capstone rows in `formal/README.md`, `CLAUDE.md`,
`AGENTS.md` gained `Bottcher.q62_phiMero_linGap_roots`, `Bottcher.q62_phiMero_norm_gap_roots`.

Addendum 7 extension — a third concrete root-tower capstone `Bottcher.q62_phiMero_mixed_far_roots`
(gap-free) covers the MIXED regime: far disconnected `c₁` (`‖c₁‖≥1000`) × ANY connected
`c₂ ∈ mandelbrot ∖ {0,-2}`, with no norm-gap hypothesis — strictly broader than the mixed branch of
`norm_gap_roots`.  It consumes `q62_phiMero_mixed_far` (mixed case needs no E–vS rigidity; the
disconnected coordinate's monodromy settles it).  So the shipped concrete finite-root-tower surface
now spans: linear-gap disconnected, quadratic-gap disconnected, and the full mixed regime (all of
Mandelbrot minus two points for the second parameter).  Axiom-clean, MainTheorems green, lint pass.

## Addendum 8 — comparable-norm no-go findings (verified, so the team does not re-attempt)

Two routes toward the still-open disconnected×disconnected COMPARABLE-norm regime
(`‖c₁‖/600 < ‖c₂‖ < 600‖c₁‖`, both disconnected) were traced to structural dead-ends this session:

1. **The linear-gap winding machinery is structurally gap-bound — it cannot reach comparable norms
   by tuning constants.**  In `bottcher_towerDataG_linGapRoot` (`W4LinPack.lean`) the gap is consumed
   at `hsmall`: `2·s²·‖c‖ + s⁴ + 1 ≤ (‖c‖² − ‖c‖)/100` with `s² ≈ 2‖c₂‖`.  The binding term
   `2s²‖c‖ ≈ 4‖c₂‖‖c‖` must sit below `‖c‖²/100`, forcing `‖c₂‖ ≲ ‖c‖/400`.  Reaching `‖c₂‖ ≈ ‖c‖`
   would require `4‖c‖² ≤ ‖c‖²/100`, impossible.  The winding-parity mechanism needs the `c₂`
   coordinate's contribution DOMINATED by `c`'s; that domination IS the gap.  Constant optimisation
   (relaxing `1/100`) at best moves `1/600` to another fraction `≪ 1`, never to comparable norms.
   ⟹ comparable norms need the genuinely different OP16-A enclosure argument, not a sharper constant.

2. **The index-formula (Zdunik-free) route also rests on a conditional deep input.**  Its endpoint
   `IndexWiring.phiMero_transcendental_via_index_eventual_fixedB` gives single-coordinate
   transcendence only under `hinput`: at every bulk period-`p` cycle root, the relation-derived
   branch has nonzero derivative (`deriv g z ≠ 0`).  That branch-nonvanishing datum is the connected-
   case difficulty repackaged (the smooth-piece analog), not an unconditional closure.  Both
   both-connected routes in the tree (SmoothPieceRigidity #118 and the index route) are conditional.

Neither is a Lean gap to grind; both are genuine mathematical inputs (external OP16-A; deep dynamical
rigidity).  Concrete root-tower surface extended this session to the swapped mixed orientation:
`Bottcher.q62_phiMero_mixed_far_roots_swapped` (connected `c₁ ∈ M∖{0,-2}` × far disconnected `c₂`).
