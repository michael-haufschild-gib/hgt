# Literal causal onset transgression

- **ID:** HB-COT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` (read-only) · shared HB/FZZ-P/PW-B/RBH causal-extinction seam
- **Statement:** The compact translation defect of the literal fixed-onset theta source is the boundary transgression whose advanced-minus-retarded two-leg Green class is the mixed horizon monodromy jump, has vanishing plus-plus jump, and obeys optical reciprocity.

## Goal

This is a source-pure producer, with no RH premise.  Its three conclusions are exactly `hpm`, `hpp`, and `hreciprocity` of `d4BMXiMixedHorizon_retardedSection_eq_advancedSection_iff`; that theorem then makes the literal causal cut vanish iff `Re q = 1/2`.  The established common-current equivalence closes HB, FZZ-P, PW-B, and RBH simultaneously.

## Frozen evidence and reframe

The familiar primitive is a retarded/advanced inverse.  The reframe makes the fixed-onset translation defect primitive and derives the relative inverse from it.  Corpus basis:

| Established shadow | Required consequence of COT |
| --- | --- |
| `fullNullResponse_wave`, `fullNullResponse_eq_retarded_reduced` | literal retarded forced Goursat field |
| `D4BMFullSourceAdvanced.response`, `response_null_coordinates`, both horizon limits | literal future field is admitted but has no asserted wave/Peierls identity |
| `reducedDefect_eq`, `defectDensity_late_zero`, `response_translation` | onset defect is exact, compact in source time, and survives as the only translation anomaly |
| `d4BMXiMixedHorizon_retardedSection_eq_advancedSection_iff` | exact target triple: mixed jump, ++ zero, optical reciprocity |
| F329/F330/F331 | direct canonical matching, same-pole Schwarz, and same-clock horizon traces cannot replace a two-leg source transgression |

**Risky prediction:** the physical mixed residual maps to `d4BMXiMixedHorizonComplexMonodromyJump • u`, whereas the plus-plus residual maps to zero, for every Xi copy without a critical-line assumption.  A proof therefore yields the common current-extinction theorem, not a receiver relabelling.

## Conjecture attack

1. `[BRIDGE]` Prove backward Goursat--Duhamel for the future convolution, retaining the characteristic `h = 0` source term.  Falsifier: a nonzero uncancelled axis/infinity term.
2. Lift that identity to the literal gauge-fixed two-leg source and identify the mixed and ++ jumps.  Falsifier: source-preserving lift produces a common-response correction only; such corrections leave the causal cut invariant.
3. Prove Green reciprocity for the same transgression pairing, not by ordinary conjugation (which preserves retarded support).  Falsifier: the source pairing has a non-optical residual term.

## Gates

- [x] 0 → 1: corpus novelty search, source-purity audit, full proof chain, and falsifiers stated.
- [ ] 1 → 2: unconditional paper proof of all three conclusions; no unproved operator premise.
- [ ] 2 → 3: closed Lean theorem(s), targeted `lake env lean` checks and final leaf audits.
- [ ] 3 → 4: standalone proof and certificate.

## Status

No claim of proof or literature novelty.  Broad 2026 ArXiv word searches (`Duhamel`, `Goursat`, `transposition`) returned no transferable result; corpus deep search finds no literal advanced-source-to-Teukolsky/Peierls bridge.  First attack is the backward Goursat--Duhamel bridge.

`[BRIDGE — CLOSED AT WEAK-FIELD LEVEL]` `ThetaCuspHawkingBMFullFieldOnsetTransgression` now proves the missing compact-test transport: translated tests preserve smoothness, compact support and physical radial support; `weakWaveTest` commutes with the exact time shift; and nested target volume has its explicit right-Haar invariance.  Consequently the literal `lift + future response - cap` field has the translated full original weak forcing equation.  Its `sourceFactor` difference has exactly `onsetDefectForcingDensity`, retaining the full square and gradient source channels.  The leaf source-checks with `lake env lean`; it is wired into `RHTower.lean`.  Its isolated Lake audit was stopped after replaying >13,000 unrelated dependencies, so no `.olean`/axiom-audit claim.

**Whole-route meaning:** COT's backward Goursat--Duhamel obligation is now closed in the unconditional compact-test weak sense, together with zero ingoing datum and the exact translated past datum.  The sole live COT edge is no longer temporal/source transport: prove a characteristic uniqueness upgrade and literal gauge-fixed two-leg lift which identifies this defect with `hpm`, proves `hpp`, and establishes `hreciprocity`.  No current-extinction or RH conclusion follows before that edge closes.

**Next conjecture (strong-upgrade chain):** Multiply the literal corrected future field by `parameter`. `future_source_balance` and `combinedCap_eq_fixed` reduce it exactly to the compact future pulse, `parameter*lift - timeAngularSeedField`, and direct-minus-image `fixedSeedArm`/`fixedSquareArm` tails. Prove that explicit remainder has the physical strong Goursat equation and the already-established two horizon data; characteristic uniqueness then identifies the future and retarded representatives, after which the literal gauge-fixed two-leg lift must prove `hpm`, `hpp`, and `hreciprocity`. A nonzero axis or infinity term in the fixed-arm equation kills COT; a regularity theorem without this Goursat identity does not advance the route.

**Alternative conjecture (Laplace-uniqueness chain):** Let `S` be the literal `causalCuspSourceVector` and form its finite onset defect `S(·+T) - sourceFactor(T) • S`. The corpus already proves `S` has causal support, weighted `L²` admission, an exact Bochner-Laplace transform to `cuspResidualVector`, and the transformed resolvent is the unique `jointWaveSolution`. Prove the literal future translation defect has this same Bochner-Laplace transform, retaining its finite onset boundary term; resolvent uniqueness and Hardy/Laplace injectivity would then identify the two fields without a pointwise strong-Goursat proof. This would close the same backward bridge and feed the unchanged two-leg `hpm`/`hpp`/`hreciprocity` chain. Falsifier: an uncancelled axis/infinity boundary term or failure of the future defect to lie in the source's weighted `L²` class. A source-only transform identity is not enough; it must identify the literal future convolution.

**Derivative subchain (regularity only; not a COT endpoint):** Prove `timeOnsetFirst + timeOnsetSecond` has every physical decay exponent `0 ≤ c < 2`; combine the existing horizon factor with this estimate to obtain the same two-variable integrable majorant for `timeReducedFirst`; then differentiate the literal full future convolution under its native direct-minus-image integral. Iteration would supply strong time jets for the future representative. This contributes only to the strong-Goursat leg above: it cannot imply the fixed-arm wave identity, characteristic uniqueness, or any of `hpm`/`hpp`/`hreciprocity`. The staged Lean proof follows this chain, but its source audit currently stops at pre-existing missing oleans; it is not a closure claim.
