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

`[BRIDGE]` The exact two-end onset-defect boundary condition is now source-checked in `ThetaCuspHawkingBMOnsetTransgressionHorizon`: zero ingoing datum and the translated past datum.  The direct `lake build` final audit was stopped because it replayed more than 12,000 unrelated modules; no `.olean` or axiom claim is made.  The active hard problem is temporal realization of the literal future convolution as the advanced boundary value of the already self-adjoint `jointEnergyOperator`.
