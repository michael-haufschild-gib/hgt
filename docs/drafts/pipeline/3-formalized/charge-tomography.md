# Charge tomography: the off-line divisor reconstructed from circle averages of log‖ξ‖

- **ID:** charge-tomography
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** ../../door/bucket-the-seam-archimedean-obstruction.md (holography face) · welds ModulusHolography ↔ ValMeasure/ValuationProfile
- **Statement (delivered):** `[PROVED HERE]` The two-circle modulus slope of `log‖ξ‖` recovers the local vanishing order, and this holographic readoff is welded to the census/valuation side (previously disconnected). Three theorems:
  - `rh_iff_forall_modulusSlope_eq_zero`: RH ⟺ the modulus-slope order field vanishes on the open right half — a single real-valued vanishing criterion (not the per-level root-of-unity form).
  - `exists_radii_discJump_eq_sum_modulusSlope`: the integer census jump `discJump t` (the atom feeding `valProfile`/`valMeasure`) equals a finite sum of modulus circle-average slopes — the census, hence the whole off-line divisor, is a functional of the modulus data.
  - `rh_iff_forall_height_sum_modulusSlope_zero`: RH ⟺ every height's reconstructed order sum vanishes (off-line locus = support of the reconstructed field).
- **Lean:** `RHTower.rh_iff_forall_modulusSlope_eq_zero`, `RHTower.exists_radii_discJump_eq_sum_modulusSlope`, `RHTower.rh_iff_forall_height_sum_modulusSlope_zero` in `formal/GaloisForLFunctions/RHTower/ChargeTomography.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound}. `lake build` green.

## What was new vs. the corpus
ModulusHolography already had per-point order recovery (`xi_circleAverage_slope_eq_order`) and a per-level exp/root-of-unity RH criterion, but stated in `analyticOrderAt xi` terms and never connected to `DiscJump`/`ValMeasure` (which live in separate files and drive `valProfile`, `offLineHeights`, RH). The weld — the census jump reconstructed as a sum of modulus slopes — is the new cross-file content, together with the crisp real-valued RH criterion. Attack-as-false caught that the *valuation-weighted* `valMeasure` is the wrong object for RH (a simple off-line zero has `filtrationLength = 0`, contributing zero mass): the RH-controlling object is the census support, not the depth-weighted mass. The reconstruction is stated for the census jump (support-correct), not valMeasure.

## Log
- 2026-07-07 — created directly in 3-formalized (paper proof + Lean together).
