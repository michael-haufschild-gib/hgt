# HC26: FZZ parity fixed-monomial determinism no-go (2026-08-28)

Route: FZZ-P. Status: formalized no-go with positive survivor.

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityFixedMonomialDeterminismNoGo.lean`.

No fixed monomial `beta ↦ y(beta)^n` is both unit-circle phase-complete and injective on positive
physical scales. Degrees 0--4 are incomplete. For every `n>=5`, explicit upper-left roots at
angles `3*pi/4 +/- pi/n` are distinct but have equal `n`th powers; HC23 realizes them at distinct
positive scales.

Strong endpoint:
`exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq_of_complete` says every complete fixed
monomial has a constructive two-scale collision.

Global no-go:
`not_fzzCigarParityFixedMonomialPhaseComplete_and_scaleInjective`.

Positive survivor: HC25's quintic is minimally phase-complete. New required datum is a source-native
observable beyond phase that separates collision scales. Phase-only fixed-monomial dynamics is
retired.

Audit: direct Lean and target-only build passed; six audited endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Frontier map was not edited.
