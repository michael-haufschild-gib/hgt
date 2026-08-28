# HC24: FZZ parity quadratic eigenphase completion (2026-08-28)

Route: FZZ-P. Status: formalized, target-built, axiom-audited.

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityQuadraticEigenphaseCompletion.lean`.

Four quadratic channels derived from the literal conjugate source pair cover the unit circle:
`y^2`, `star(y)^2`, `y*star(y)=1`, and `-(y*star(y))=-1`. HC23 realizes the required upper-left
square root at positive scale. Every channel has norm one.

Local endpoint:
`exists_pos_fzzCigarParityQuadraticEigenphase_eq_dyadicMellinCharacter_iff` says exact channel
realizability is equivalent to `Re rho=1/2`.

Global endpoint:
`fzzCigarParityQuadraticEigenphaseDivisorComplete_iff_rh` says channel completeness for every
open-strip zeta zero is equivalent to RH.

Novel survivor: degree-one source incidence is cofinally incomplete (F13), while degree two has
complete phase capacity. Remaining burden is dynamical, not kinematic: derive a fixed,
source-first FZZ interaction law that lands divisor modes in these channels without choosing a
scale/channel from the divisor.

Audit: direct Lean and target-only build passed; eleven audited endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Frontier map was not edited.
