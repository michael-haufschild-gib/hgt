# Möbius critical soft-hard reporter-escape universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul`
- `tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient`
- `mobiusCriticalShiftChannel_weakly_tendsto_zero`

## Survivor

The hard cutoff Ward profile divided by the soft damped Fisher profile tends `4` at vanishing
positive aperture.  Hence the hard profile is positive throughout some punctured aperture
neighborhood.  On that same neighborhood, every fixed bounded reporter of the critical Möbius
shift channel fails to track both the co-moving soft coefficient and one quarter of the calibrated
hard profile.

This transports reporter escape from the soft moving tangent to the independently constructed hard
cutoff boundary.

## Proof skeleton

Combine the hard `/(2u)` asymptotic with `(1+u)^2 -> 1` to obtain the hard/soft ratio `4`.
Eventually positive ratio and positive soft profile imply a positive hard profile.  Fixed reporters
converge weakly to zero, whereas the soft and quarter-hard targets have nonzero limits; uniqueness
of limits gives both contradictions.

## Novelty audit

Pending post-formalization literature search.
