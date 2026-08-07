# Return-excised replica coarea-incidence law (2026-08-07)

Formalized a stronger return-removal step for the Brown–Susskind frontier.

## Exact advance
For finite source measure `mu`, measurable target-independent return set `R`, complete target capture `E_a`, occupied replica Hilbert number `h_r`, and occupied-image pair kernel `k_(r,Z)`, define

`A_(r,Z)(mu;R) = integral_(R^c x R^c) k_(r,Z) d(mu x mu)`.

Lean proves:

`mu.real E_a <= mu.real R + sqrt(h_r * A_(r,Z)(mu;R)) / a^r`.

Equivalent squared residual law:

`(a^r * (mu.restrict R^c).real E_a)^2 <= h_r * A_(r,Z)(mu;R)`.

This removes return points before covariance is formed, so no mixed `R x R^c` or `R^c x R` pairs survive. Return mass is paid once with coefficient one. Source fibre-sheet multiplicity, complete occupied endpoint image, duplicate target invariance, and exact-return zero invariance remain.

## Failed conjectures
- Pair-relation partition after covariance: exact but leaves or charges mixed return/nonreturn collision.
- Infimum over arbitrary return sets: circular because `R = E_a` trivializes residual action. Return filtration must be fixed independently by a physical recurrence observable.

## Files
- Lean: `formal/GaloisForLFunctions/HTGeometry/QuenchedReplicaReturnExcisionLaw.lean`
- Card: `docs/drafts/pipeline/3-formalized/return-excised-replica-coarea-incidence-law.md`
- Master updated: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`
- Umbrella: `formal/GaloisForLFunctions/HTGeometry.lean`

## Verification
- direct `lake env lean`: PASS
- final `lake build GaloisForLFunctions.HTGeometry.QuenchedReplicaReturnExcisionLaw`: PASS (8659 jobs)
- axioms: only `propext`, `Classical.choice`, `Quot.sound`
- full lint reports no error in new module; unrelated unwired modules remain elsewhere.

## Remaining core
Choose a physical, target-independent return level for ordinary fixed-q Gaussian static local Hamiltonians, bound `P(R)`, and prove growing-replica decay of `A_(r,Z)(mu;R)` strong enough to beat `h_r`.