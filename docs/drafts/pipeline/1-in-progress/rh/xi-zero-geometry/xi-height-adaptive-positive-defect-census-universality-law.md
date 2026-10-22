# Xi height-adaptive positive-defect census universality law

## Status

- Stage: 1-in-progress
- Lean target: `GaloisForLFunctions.RHTower.XiHeightAdaptivePositiveDefectCensusUniversalityLaw`

## Theorem-generated route

Source statements were read first:

- `boxOrderSum_eq_pred_add_distinct`
- `boxHedenmalmCommonOrderSum_eq_pred`
- `boxSquareOrderSum_eq_order_add_excess`
- `riemannHypothesis_of_xiNatHeightAdaptiveHedenmalmAdjacentCensus`
- `riemannHypothesis_of_rhLadder_one_of_xiNatHeightAdaptiveLinearQuadraticCensus`

Both routes decompose an upper census as a lower census plus a defect.  Congruence modulo a
height-adaptive power of two makes that defect divisible by the modulus; an independent envelope
makes it smaller than the same modulus.  Positivity of the defect on every nonempty box forces
emptiness.  Only the defect interpretation differs: distinct-zero count versus nonsimplicity
excess.

## Candidate law

For arbitrary natural-valued upper, lower, and defect box censuses, if upper equals lower plus a
bounded defect, every nonempty box makes the defect positive, and upper and lower collide modulo a
height-adaptive power of two larger than the defect, then RH follows.  Hedenmalm adjacent and
linear--quadratic censuses map to this single interface.

## Open audits

- Exact Lean check
- Axiom audit
- Literature novelty audit
