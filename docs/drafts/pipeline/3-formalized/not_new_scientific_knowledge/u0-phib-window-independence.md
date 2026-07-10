# u₀ ⟂ Böttcher window branch: unconditional algebraic independence, all ‖b‖ > 2+√2 (SHARP)

- **ID:** u0-phib-window-independence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Source:** window closure of the `u0_phi_independence` program (U0 card family); consumes the
  q62 lane's `Bottcher.bottcher_transcendental_far`.
- **Statement:** In the meromorphic germ field of the b-dependent window annulus
  `{1 < |z| < rB b}`, the c-velocity `u₀` and the constructed Böttcher window branch `phiB b`
  satisfy no nonzero bivariate polynomial relation over `ℂ(z)`, for every parameter
  `‖b‖ > 2+√2` — and likewise for every dyadic Kummer layer `phiBRoot k b` (`2^k`-th roots).
  No hypotheses.  The threshold is EXACT: `window_threshold_sharp` pairs the coverage with an
  obstruction witness at `b = −(2+√2)` (see card `window-threshold-sharp`).

## Goal

Banks the mission-level value-relation statement `u₀ ⟂ φ_b` unconditionally on an OPEN SET of
parameters, with the whole radical tower above the branch included.  The natural-boundary object
(`u₀`, boundary `|z| = 1`) and the constraint-side dynamical object (`φ_b`, fixed by the Böttcher
functional equation) are proven algebraically foreign over `ℂ(z)` in a faithful carrier — the
germ field, where `NoRelation` is a statement about the actual functions.  Non-circularity: no
tower certificate, no `GBExt` clause, no windowed continuation hypothesis; every analytic input
is constructed in-tree.

## Lean surface

- `U0PhiLargeCapstone.u0_phiB_independence` — `NoRelation ℂ(z) (phiB b) (u₀)`, `‖b‖ > 2+√2`.
- `U0PhiKummerLayers.u0_phiBRoot_independence` — every layer `phiBRoot k b`, `‖b‖ > 2+√2`.
- `U0WindowSharpness.window_threshold_sharp` — the two-sided sharp-threshold pair.
- `U0PhiFourCapstone.u0_phiFour_independence` — the seed instance `b = 4` (separate branch
  normalization, same architecture).
- Cards: `FullyProvenNewTargets.u0_phiB_independence_card`, `u0_phiBRoot_independence_card`,
  `u0_phiFour_independence_card`.
- Files: `formal/GaloisForLFunctions/U0/U0PhiLargeWindow.lean`, `U0PhiLargeCarrier.lean`,
  `U0PhiLargeDescent.lean`, `U0PhiLargeCapstone.lean`, `U0PhiKummerLayers.lean`
  (+ the `U0PhiFour*` seed files).

## Proof shape

Window branch `phiB b z = exp(½(log b + log(1 + z²/b) + tail(z² + b)))`, analytic across the
unit circle on the b-dependent disk `ball 0 (rB b)` (the branch is rotated through `log b`;
`1 + z²/b` stays in the right half-plane).  The far field is `{‖w‖ > xStar ‖b‖}` — everything
beyond the escape fixed point `xStar B = (1+√(1+4B))/2` — which the fixed-point identity
`xStar² = xStar + B` makes EXACTLY forward invariant with uniform series ratio `< 1`; far entry
is by monotone escape (linear growth above the fixed point, no rate constant), which is what
works arbitrarily close to the threshold where the escape rate degenerates.  A relation `P(phiB, u₀) = 0` in the germ field splits by `u₀`-columns after
a germ-level double-sum swap: positive columns with a surviving coefficient germ die against the
natural-boundary window engine (`u0_windowed_no_relation_nondegenerate`, after clearing
`ℂ(z)`-denominators and descending to a pointwise identity); vanishing columns die against
`phiB_transcendental` (see card `phib-window-transcendence`), column polynomial by column
polynomial.  Kummer layers inherit transcendence up the root tower (`IsIntegral.pow`) and reuse
the φ-generic engine.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proof carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]` for the full chain;
      `lake build` green; formal lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — b = 4 window capstone closed; parameterized to ‖b‖ ≥ 4; Kummer layers added.
- 2026-07-02 — B₀ lowered 5 → 4 (far radius ‖b‖−23/20, growth 7/5); window obstruction proven for real b ∈ [−2−√2,−2) (see `U0WindowObstruction`): coverage below 2+√2 requires direction-dependent hypotheses.
- 2026-07-02 — dichotomy companion: window viability at fixed modulus is direction-dependent
  (`window-dichotomy-modulus-three`, witnesses b = ±3).
- 2026-07-02 — SHARP PASS: threshold lowered ‖b‖ ≥ 4 → ‖b‖ > 2+√2 (exact). Far field
  rewritten to the fixed-point radius `xStar ‖b‖` (exactly invariant, margins vanish); carrier
  is the b-dependent annulus `annWB b`; entry by monotone escape (`U0MonotoneEscape`); general
  log bound `U0LogBoundGeneral`. `window_threshold_sharp` banks the matched pair.
