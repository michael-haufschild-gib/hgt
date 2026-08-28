# FZZ parity phase-only fixed-monomial determinism no-go

Status: failed/retired
Route: FZZ-P
Date: 2026-08-28

## Retired proposal

Use one fixed monomial phase `beta ↦ y(beta)^n` both to cover every critical unit phase and to
determine one unique positive physical source scale.

## Exact obstruction

HC26 proves the proposal impossible for every natural degree. Degrees zero through four are
phase-incomplete. At every degree `n>=5`, two explicit distinct upper-left source roots separated by
angle `2*pi/n` have the same `n`th power. HC23 realizes them at distinct positive scales. Hence no
fixed monomial phase map is both complete and scale-injective.

Formal theorem:
`not_fzzCigarParityFixedMonomialPhaseComplete_and_scaleInjective` in
`FZZCigarParityFixedMonomialDeterminismNoGo.lean`.

## Strongest positive survivor

HC25's degree-five orbit remains the least fixed monomial with full unit-circle phase capacity.
HC26 strengthens that survivor with explicit collision geometry at every complete degree:
`exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq_of_complete` constructs two distinct
positive source scales with equal reported phase from any completeness proof.

## New insight

The post-HC25 obstruction is not phase coverage or channel choice. It is lost scale information.
Any viable deterministic FZZ landing mechanism must augment phase by at least one source-native
observable that separates collision fibres.

## Lean status

Exact obstruction and positive survivor are fully formalized, wired, target-built, and
axiom-audited. No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration occurs.

## Route decision

Retire every phase-only fixed-monomial deterministic landing proposal. Continue only with joint
phase-plus-amplitude, derivative, orientation, or interaction-coefficient source laws.
