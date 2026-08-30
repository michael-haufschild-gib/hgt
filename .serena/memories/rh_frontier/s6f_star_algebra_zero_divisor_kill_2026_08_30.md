# S6F D1 star-algebra zero-divisor route kill (2026-08-30)

## Formal result
New module:
`formal/GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveD1StarAlgebraZeroDivisorNoGo.lean`

Wired into:
`formal/GaloisForLFunctions/HTGeometry.lean`

Main declarations:
- `ModularThetaSourcePositiveD1RightStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular`
- `ModularThetaSourcePositiveD1LeftStarAlgebraContravariantCarrier.exists_nonzero_diagonal_not_leftRegular`
- `modularThetaSourcePositive_no_D1_regularStarAlgebraContravariantCarrier`

## Mathematical classification
For any algebra-valued contravariant carrier containing the actual D1 cyclic source string, the exact source-sl2 relations force a nonzero source vector whose diagonal value is not left regular. Right contravariance requires no involution. Left contravariance uses only StarRing and Hermitian diagonals.

Proof core: choose nonzero u,v with E u = 0, F v = u, and E v != 0. Contravariance forces a scalar c annihilated by pair(u,u). If pair(u,u) were left regular, c = 0, hence pair(E v,E v)=0 while E v != 0. The left-handed variant applies star to move the annihilator to the right.

## Route consequence
Killed chain:
regular algebra-valued contravariant source-sl2 carrier containing D1
→ singular/unbounded or indefinite Gram/Shapovalov realization
→ finite TCD/S6F gate
→ cofinal all-order landing
→ Weil positivity
→ RH.

This strictly strengthens the earlier bounded positive-operator no-go: it assumes no positivity, boundedness, norm, topology, dimension, completeness, or Hilbert structure.

Positive survivor/classification: any remaining contravariant realization must expose an actual diagonal zero divisor/isotropic diagonal on the D1 cyclic string. Therefore moving to unbounded, singular, or indefinite carriers does not rescue the route unless it accepts precisely this degeneracy.

## Verification
- Direct: `lake env lean GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveD1StarAlgebraZeroDivisorNoGo.lean` passed.
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1StarAlgebraZeroDivisorNoGo` passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- New module warning-free.
- Global `scripts/formal_tools.py lint` remains red solely because of unrelated pre-existing unreachable RHTower/HTGeometry modules; this new module is reachable.
- Frontier map was read-only and untouched by this work.

## Remaining hard core
`TCD-D1-BOUNDARY-FLUX`: prove theta-specific positive null-line crossing at every singular actual D1 point, equivalent in current reduction to global D1 positivity. This remains the finite TCD/S6F gate.
