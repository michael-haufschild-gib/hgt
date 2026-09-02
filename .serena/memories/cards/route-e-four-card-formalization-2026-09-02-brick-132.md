# Route E four-card formalization — brick 132

Goal remains active. Added unconditional no-premise leaf:
`formal/GaloisForLFunctions/RHTower/Sieve/GrowingReciprocalMarkerCapacityAggregation.lean`.

Public theorem:
- `RHTower.Sieve.tendsto_growingReciprocalMarker_aggregateBlockScale`

It proves the exact schedule aggregation
[
[K(X)(H(X)/\log X)]/[H(X)/\log\log X] \to 1/\log 2,
]
using the literal natural floor and subtraction by four already present in `growingReciprocalMarkerBlockCount`. This is the analytic-free paper passage from per-block equation (30) to schedule normalization (7), not a target-count assertion.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/Sieve/GrowingReciprocalMarkerCapacityAggregation.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerCapacityAggregation` passed 2011/2011.
- `#print axioms` on the new theorem: only `[propext, Classical.choice, Quot.sound]`.
- Module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.
- Growing-marker Stage-2 card appended with exact progress and remains Stage 2.

Important audited obstruction:
- Existing unconditional `averagedMeanSquare_moebius` cannot be upgraded to card's required `o(1/log X)` by merely extracting rates from current explicit budget.
- `tendsto_nonSpectralBudget` is majorized by a term containing `C / log(log x)` (plus a rapidly vanishing window/sqrt term), so multiplying current proved budget by `log x` does not tend to zero.
- Remaining substantive growing-marker gate is still the uniform quantitative Menon–Halász mean-square inequality over the `ceil(log log X)` length grid. It was not assumed.

Previous brick: `mem:cards/route-e-four-card-formalization-2026-09-02-bricks-124-130` plus the Kloosterman residue-multiplicity brick described in current task summary.
