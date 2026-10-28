# Signed index payment on complete logarithmic cells

- **ID:** acs-complete-cell-index-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Statement:** The original full arithmetic form `finiteCellWeil` is nonnegative on every finite real complete-cell coefficient vector, with the Gamma, prime, and both pole contributions retained.

## Target

Prove the signed index estimate on the source-complete cells constructed in `CompleteWeilSourceTransfer.lean`. Their approximation of arbitrary finite compact C² source families is formalized. Positivity of separated narrow sections does not settle this estimate.

## Constraints

- Derive every analytic input from the actual arithmetic source.
- No form-defined effectivity hypothesis or assumed positive residual.
- Preserve all successor cells, full Gamma jump energy, and both poles.
- Any proved intermediate mathematical statement must be formalized immediately; no stage-2 parking.

## Current evidence

- `exists_completeFiniteSourceTransfer` recovers the original Weil intersections and polarized Gram entries on one common complete-cell system.
- `finiteCellWeil_original_surface_limit` realizes `finiteCellWeil c 0 1 X` by compact C² tests on the original surface. The same smoothing preserves both pole coordinates and exact Hecke subdivision; its first `X` cell sections are linearly independent at every scale.
- Independent separated-section positivity has a support restriction; complete cells fill the gaps.
- [Balanced complete-cell effectivity](../3-formalized/acs-complete-cell-haar-effectivity.md) is formalized and audited. `exists_haarTail_roughWeil_floor` gives one fixed lower index and a unit-mass floor for all finite signed balanced tails, independently of the upper horizon. `exists_smooth_haar_effectivity` gives, for every dimension, one common smoothing scale with exact dimension, a half-mass floor, Riemann–Roch, ampleness, and Hodge index on the source-defined range. The prime, Gamma, and pole estimates retain all original terms. This proper subspace does not settle the pair averages, low-index directions, or their full mixed coupling.
- Full-source effectivity and the signed Gamma–prime–pole index bound remain unproved.

## Log

- 2026-10-28 — Opened after formalizing full finite-source transfer. Investigating actual signed payment; no new sign claim is certified.

- 2026-10-28 — [Smooth complete-cell realization](../3-formalized/acs-smooth-hecke-complete-sections.md) is formalized and audited. Exact source realization and arithmetic compatibility are available; full signed index payment remains open.
