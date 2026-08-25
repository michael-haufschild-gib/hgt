# Irregular Stokes cubic cover-weighted terminal dissipation (2026-08-25)

## Result

For every unit-Rees completed-Xi cubic Malgrange landing, the activated canonical Stokes block energy dominates the strictly positive inverse-cover-weighted terminal energy
`W = sum_a (1 / N_a) * terminalEnergy_a`.

For arbitrary contracted/unit moving landings:
`T1 + W1 + A*r0^2 <= T0 + A*r1^2`, where `A = -globalRankCoefficient > 0`.
If rank magnitude is preserved, `T1 + W1 <= T0`; terminal energy therefore contracts by an explicit cover-degree-weighted amount.

Proof uses coefficient-generated pendant cuts privately: choose one branch per orbit, prove selected pendant edges injective, restrict nonnegative block sum, and identify each selected term as `(1/N)*x_i^2`. No source map, landing existence, or new hypothesis.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicCoverWeightedTerminalDissipation.lean`
- Card: `docs/drafts/pipeline/3-formalized/route-p-cubic-cover-weighted-terminal-dissipation.md`
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`
- Frontier map remained untouched/read-only.

## Verification

Targeted module check passed. All three public declarations depend exactly on `[propext, Classical.choice, Quot.sound]`. Scratch and five temporary `.olean` interfaces removed. No umbrella build.

Related: `mem:research/irregular_stokes_cubic_moving_charge_rank_terminal_balance_2026_08_25`.