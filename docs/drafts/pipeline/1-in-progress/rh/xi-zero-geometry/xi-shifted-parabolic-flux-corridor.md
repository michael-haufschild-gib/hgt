# Xi-shifted parabolic flux corridor

Status: C6 formalized; next conjunction under hostile audit

## Corpus lead

`XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFloor` gives one degree-uniform threshold
with `1/4 < w^4 * sourceAction(w,n)` in every sufficiently large positive actual block.
`XiShiftedCanonicalAdmissionAdaptiveMixedSourceIntegralLaw` identifies cumulative Jacobi flux with
the full future integral of that same source action on a positive right ray. Neither module currently
transports the pointwise source floor through the exact tail budget.

## C6 — tail-integrated parabolic floor

Conjecture: one universal `W` forces

`1 / (4*a) ≤ cumulativeJacobiFlux(a,n)`

for every `a ≥ W^2`, every `n ≥ 2`, whenever the actual `(n+4)` block stays positive on
`[a,∞)`. Consequently, strictly beyond terminal frontier `T_(n+2)`, dimensionless flux satisfies

`1/4 ≤ w^2 * cumulativeJacobiFlux(w^2,n)`.

Mechanism: rewrite source floor in mass coordinate as
`1/(4*y^2) < sourceAction(sqrt y,n)`, compare set integrals on `(a,∞)`, and use
`∫_a^∞ (4*y^2)⁻¹ dy = 1/(4*a)` plus exact full-tail source budget.

## Hostile audit

- This does not imply RH: fixed-degree arcsine recession predicts much larger limiting
  dimensionless flux `((2*n+1)/2)`.
- It is a new uniform mass-degree statement, not obtainable from fixed-degree limits because the
  corpus has a closed delayed-switch order-of-limits countermodel.
- Reciprocal-clock upper bound combined with this floor gives only a broad corridor, not a
  contradiction. Missing datum remains stronger degree-uniform capital or cross-degree transport.
- No computation, reporter, reflection aggregate, RH premise, or external axiom is used.

## Verification ledger

- Corpus search: no existing cumulative-flux parabolic lower-bound theorem found.
- Scratch proof: `/tmp/ParabolicFluxCorridorChecks.lean`, closed with
  `lake env lean /tmp/ParabolicFluxCorridorChecks.lean`.
- Promoted module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFluxCorridor.lean`.
- Direct source check: passed.
- Exact target build: passed; no umbrella build run.
- Axiom audit, all four public theorems: `[propext, Classical.choice, Quot.sound]`.
- Umbrella import: wired into `formal/GaloisForLFunctions/RHTower.lean`.
