# Quiet flank growth endgame

- **ID:** quiet-flank-growth-endgame
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[PROVED HERE]`
- **Date:** 2026-07-10
- **Paper source:** `../../2-fully-proven/new/quiet-flank-growth-support-radius.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/QuietFlankGrowth.lean`
- **Statement:** If a variable-knot quiet-contour coefficient estimate is bounded by a flank
  envelope `H(M)<=C R^M`, then every coefficient with `R<n` vanishes; a nonzero coefficient
  satisfies the exact bound `n<=R`.

## Delivered declarations

- `perronSupportScale`
- `HasQuietFlankCoefficientBound`
- `tendsto_flank_product_of_geometric_envelope`
- `coefficient_eq_zero_of_quiet_flank_decay`
- `coefficient_eq_zero_of_geometric_quiet_flank`
- `perronSupportScale_le_of_ne_zero_geometric_quiet_flank`
- `coefficient_index_le_flank_radius`
- `perronSupportScaleAt`
- `HasVariableQuietFlankCoefficientBound`
- `coefficient_eq_zero_of_geometric_variable_quiet_flank`
- `coefficient_index_le_exact_flank_radius`

## Scope

- `[PROVED]` The geometric-envelope ratio test is independent of the functional equation that
  produced the flank bound.
- `[PROVED]` The support conclusion is one-sided; no equality with a freely chosen majorant is
  claimed.
- `[PROVED]` The fixed-knot Perron scale is `n-1/2`; quantifying over knot widths
  `0<delta<1` sharpens the support conclusion to `n<=R`.
- `[OPEN CORE]` The generic analytic contour producer from an abstract left-rectangle flank bound is
  not yet factored out of `QuietCrossingConductor.lean`.
- `[PROVED]` The variable-knot source required by this interface is formalized in the companion card
  `variable-perron-kink.md`.

## Verification

- Standalone source compile: PASS.
- No full or umbrella build was run for this module.

## Gates

- [x] 0 -> 1: exact Prop interface isolated.
- [x] 1 -> 2: ratio-test and coefficient-vanishing proofs complete.
- [x] 2 -> 3: formalized and standalone compile passes.
- [ ] 3 -> 4: blocked on the generic analytic contour producer and paper integration.

## Verification update

- Target module build: PASS (`8475/8475`); no umbrella build was run.
- Scratch `#check`: PASS for the six principal fixed- and variable-knot theorems.
- Scratch `#print axioms`: each principal theorem uses only
  `{propext, Classical.choice, Quot.sound}`.
- The earlier verification line recording only the standalone source compile is superseded by this
  stronger targeted check.
