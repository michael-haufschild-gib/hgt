# The Böttcher window branch is transcendental over ℂ(z) (all ‖b‖ ≥ 4)

- **ID:** phib-window-transcendence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Source:** φ-side residue of the window engine; consumes the q62 lane's
  `Bottcher.bottcher_transcendental_far` + `bottcherFarBound_spec`.
- **Statement:** For every `‖b‖ ≥ 4` (and `b = 4`), the window branch `phiB b` is transcendental
  over `ℂ(z)` in the meromorphic germ field of the annulus `{1 < |z| < 21/20}`.

## Goal

The `u₀`-degree-0 case of the window capstone, and a standalone value-relation fact: the window
germ of the Böttcher coordinate carries no algebraic relation over the rational functions, on a
carrier where it coexists with natural-boundary objects.  Also the template for transporting far
transcendence to any bounded window along a polynomial escape map.

## Lean surface

- `U0PhiLargeDescent.phiB_transcendental` (`‖b‖ ≥ 4`); `U0PhiFourDescent.phiFour_transcendental`
  (`b = 4`); `U0PhiKummerLayers.phiBRoot_transcendental` (all dyadic root layers).
- Cards: `FullyProvenNewTargets.phiB_transcendental_card`, `phiFour_transcendental_card`.
- Files: `formal/GaloisForLFunctions/U0/U0PhiFourDescent.lean`, `U0PhiLargeDescent.lean`,
  `U0PhiKummerLayers.lean`.

## Proof shape

Dyadic pullback: `phiB^(2^(m+1)) = bottcherCoord b ∘ pMapB m` on the window
(`phiB_pow_iterate`), with `pMapB m = f^[m] ∘ f` a monic polynomial escape map whose image of the
annulus is an open connected infinite carrier beyond the far bound (`exists_far_carrier_B`;
derivative nonvanishing because every chain-rule factor is a far-field iterate).  An algebraic
relation for `phiB` descends from `ℂ(z)`-coefficients to `ℂ(p(z))`-coefficients through the
finite tower `κ(ℂ(z)) ⊆ κ(ℂ(z))⟮[z]⟯` (monic witness `p(T) − X`; `IntermediateField` +
`isIntegral_trans`, eval₂-only signatures), then transports through the germ-field pullback
`meroField (image) ↪ meroField (annulus)` to an algebraic relation for the genuine far Böttcher
germ — contradicting `bottcher_transcendental_far`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proof carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — b = 4 descent closed; generalized to arbitrary monic p and all ‖b‖ ≥ 4.
- 2026-07-02 — B₀ lowered 5 → 4 across the descent chain.
