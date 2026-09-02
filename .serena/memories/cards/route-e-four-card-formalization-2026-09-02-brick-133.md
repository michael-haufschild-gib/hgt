# Route E four-card formalization — brick 133

Goal remains active. Added second unconditional no-premise leaf:
`formal/GaloisForLFunctions/RHTower/CofactorAmplifiedDyadicSliceCount.lean`.

Definitions:
- `RHTower.CofactorParity.cofactorAmplifiedSliceLower U = (log U)^(10999/10000)`
- `RHTower.CofactorParity.cofactorAmplifiedSliceUpper U = 2*(log U)^(11/10)`
- `RHTower.CofactorParity.cofactorAmplifiedDyadicSlices U`: exact integer exponent interval with ceiling/floor endpoints.

Public theorem:
- `RHTower.CofactorParity.tendsto_card_cofactorAmplifiedDyadicSlices_div_logLog`

It proves exact card equation (6a) at the literal band:
[
\#\mathrm{slices}(U)/\log\log U \to 1/(10000\log 2).
]
Both ceiling/floor errors are retained and bounded by one before normalization. No exponent-range widening or surrogate schedule.

Verification:
- direct `lake env lean GaloisForLFunctions/RHTower/CofactorAmplifiedDyadicSliceCount.lean` passed
- targeted `lake build GaloisForLFunctions.RHTower.CofactorAmplifiedDyadicSliceCount` passed 8974/8974 (large cached dependency replay due root module import; do not repeat)
- new theorem axioms only `[propext, Classical.choice, Quot.sound]`
- leaf wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built
- cofactor Stage-2 card appended; remains Stage 2
- scratch removed; no Lean/lake processes

Same turn also added `mem:cards/route-e-four-card-formalization-2026-09-02-brick-132`.
