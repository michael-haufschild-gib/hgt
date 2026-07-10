# Germ-field machinery: coefficient descent, pullback transport, assembly functor, Green-band consumer

- **ID:** germfield-descent-transport-machinery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** infrastructure extracted from the window-capstone closure; consumed by
  `u0-phib-window-independence` and `phib-window-transcendence`; offered to the q62 lane.
- **Statement:** Four reusable bricks on the faithful carrier `meroField`:
  (1) `descend_algebraicP` — algebraicity over `ℂ(z)` descends to `ℂ(p(z))` for any monic
  nonconstant `p ∈ ℂ[z]`; (2) `germPullback`/`pullAn` and its fraction-field lift — precomposition
  with an analytic surjection is an injective embedding of germ fields; (3)
  `u0_window_independence_of_transcendental_engine` — branch germ + transcendence + window engine
  ⟹ `NoRelation ℂ(z) (branch) (u₀)`; (4) `u0_phi_independence_of_towerData_{exterior,greenBand}`
  — the all-parameters tower consumer with the `GBExt` clause replaced by exterior/Green-band
  geometry.

## Goal

Separates the reusable field-theoretic and germ-functorial layer from the specific branches.
(1) rebases dyadic radicand coefficient fields; (2) transports transcendence/relations along
polynomial escape maps; (3) turns any future window branch into a `u₀`-independence theorem
mechanically (already instantiated three times: `phiFour`, `phiB`, `phiBRoot k`); (4) reduces
the all-parameters U0 card at large `‖b‖` to ONE spec conjunct in the q62 lane's tower
certificate (their extension domains lie in a Green band / the exterior).

## Lean surface

- `U0PhiLargeDescent.kappaP`, `descend_algebraicP` (generalizing `U0PhiFourDescent.kappa`,
  `descend_algebraic`); `U0PhiFourDescent.germPullback`, `pullAn`, `pullAn_injective`;
  `U0PhiLargeCapstone.u0_window_independence_of_transcendental_engine`;
  `U0GreenBandBridge.u0_phi_independence_of_towerData_exterior`,
  `u0_phi_independence_of_towerData_greenBand`, `restrictAnalytic_u0AnSub`.
- Card: `FullyProvenNewTargets.u0_phi_independence_greenBand_card`.
- Files: `formal/GaloisForLFunctions/U0/U0PhiFourDescent.lean`, `U0PhiLargeDescent.lean`,
  `U0PhiLargeCapstone.lean`, `U0GreenBandBridge.lean`.

## Notes

The two `RatFunc ℂ`-algebra structures on the same `meroField` (standard `ρ` and
compose-with-`p` `κ`) never coexist in one instance scope: all statements are eval₂-only, the
`IntermediateField` tower runs under a single `letI`.  This is the pattern that avoided the
instance diamond flagged at planning time.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proof carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — extracted during the b = 4 closure and its parameterization; Green-band consumer
  banked awaiting the q62-lane conjunct (ticket Update 5).
