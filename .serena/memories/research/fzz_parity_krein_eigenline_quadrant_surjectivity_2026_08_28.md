# HC23: FZZ parity Krein eigenline quadrant surjectivity (2026-08-28)

Route: FZZ-P. Status: formalized, target-built, axiom-audited.

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityKreinEigenlineQuadrantSurjectivity.lean`.

The balanced positive-imaginary literal FZZ source eigenline fills exactly the strict upper-left
unit quadrant as scale varies over `beta>0`. Key identity:

`(-Re y(beta))^2 = P(beta)P(4 beta)/P(2 beta)^2
 = (a^2+1)^2/((a+1)(a^4+1))`, where `a=exp(beta)`.

The rational function is continuous, equals one at `a=1`, and is bounded by `4/a`. IVT gives
every squared radius in `(0,1)`, then unit norm and sign data determine the complex phase.

Main endpoint:
`exists_pos_fzzCigarParityKreinEigenline_eq_iff_unit_upperLeft`.

Novel survivor: F13's linear obstruction is sharp. The conjugate eigenpair fills the strict left
semicircle exactly and misses precisely the right half plus boundary. This feeds HC24.

Audit: direct Lean and target-only build passed; audited endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Frontier map was not edited.
