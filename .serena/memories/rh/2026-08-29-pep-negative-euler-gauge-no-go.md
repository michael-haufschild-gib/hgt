# PEP negative-Euler gauge route killed (2026-08-29)

Route PEP chain was: all-negative Helson Euler source → canonical continuation `ζ(2s)/ζ(s)` → source-faithful projective/exponent-zero gauge or opposite-sheet pairing → pole-free `1/2 < Re(s) < 1` → RH.

New Lean module: `formal/GaloisForLFunctions/RHTower/ProjectiveEulerNegativeSheetGaugeNoGo.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

Key closed terminal theorem: `exists_exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_rh`. Existence of even one exponent-zero gauged pole-free negative sheet is equivalent to RH. Parameterwise theorem: `exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis`. Canonical theorem: `canonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis`.

Strongest positive survivor: `analyticMultiplier_eq_zero_of_cancels_canonicalNegativeEulerSheet_pole`. Any analytic multiplier canceling a negative-sheet pole at a right-half zeta zero must itself vanish there, so it is not a projective unit. `exponentZeroGaugeCanonicalNegativeEulerSheet_divisor_polarity` proves full multiplicity preservation. Generic local infrastructure: `analyticAt_mul_analyticUnit_iff` and gauge specialization.

Interpretation: source-faithful projective gauges cannot supply PEP LAND. Opposite-sheet norm pairing cancels only by importing the zeta zero divisor and therefore erases polarity. PEP has no surviving mechanism; a replacement must change the source and is a different route.

Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.ProjectiveEulerNegativeSheetGaugeNoGo` passed; axiom audit only `[propext, Classical.choice, Quot.sound]`. Repository lint reported unrelated pre-existing umbrella-reachability failures, none involving new module.

Cards: `docs/drafts/pipeline/3-formalized/pep-negative-euler-gauge-rigidity-no-go.md` and `docs/drafts/pipeline/5-failed/pep-projective-euler-polarity.md`. Frontier map was not edited (read-only).