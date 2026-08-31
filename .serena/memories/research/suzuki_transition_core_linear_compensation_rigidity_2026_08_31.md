# Suzuki transition-core linear compensation rigidity (2026-08-31)

## Result

Closed positive growing-rank Cartan fission producer class for shared HB/FZZ-P/RBH/PW-B source route `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`.

New unconditional theorem:

`RHTower.eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow`

If
`suzukiRectangularWardDefect L (transitionCore - correction) (8*n)`
is eventually bounded below, then
`correction (8*n) >= n/576`
eventually.

Consequences:
- `RHTower.no_sublinear_transitionCore_rectangularWardProducer`: no correction with `correction(8n)/n -> 0` can close rectangular Ward premise.
- `RHTower.tendsto_suzukiRectangularWardDefect_completedGrowingRankCartanFission_eight_mul_atBot`: actual completed positive growing-rank Cartan fission Ward defect tends to `-∞` for every width.
- `RHTower.no_growingRankPositiveCartanFission_rectangularWardProducer`: closed no-premise producer-class kill.

Mechanism: unconditional Xi rectangular curvature envelope is `O(sqrt n)`; exact positive transition core satisfies `E_(8n) >= n/288`; semiboundedness forces linear positive correction. Actual fission is `F_N = E_N + 2R_N`, `R_N >= 0`, so effective correction `E_N-F_N <= 0`.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreLinearCompensationNoGo.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Formalized card: `docs/drafts/pipeline/3-formalized/suzuki-transition-core-linear-compensation-rigidity.md`
- Retired route: `docs/drafts/pipeline/5-failed/suzuki-positive-growing-rank-cartan-fission-ward-producer.md`

## Verification

- direct `lake env lean`: pass
- targeted `lake build GaloisForLFunctions.RHTower.SuzukiTransitionCoreLinearCompensationNoGo`: pass 11979/11979
- axioms: only `propext`, `Classical.choice`, `Quot.sound`
- global `scripts/formal_tools.py lint` blocked by unrelated pre-existing unreachable `GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicInertia`

## Survivor

Growing rank alone is dead. Viable source assembly must construct coefficient-faithful signed atomic–continuous compensation carrying at least linear mass along `8n`, while leaving rectangular residual uniformly lower-semibounded. Bounded, sublinear, purely positive, fixed-rank, fixed-scale, and literal positive growing-rank completions are excluded.

Frontier map remained read-only.