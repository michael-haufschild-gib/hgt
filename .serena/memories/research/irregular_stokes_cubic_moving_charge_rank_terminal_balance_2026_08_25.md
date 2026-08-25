# Irregular Stokes cubic moving-charge rank–terminal balance (2026-08-25)

## Result

Strengthened moving-charge Rees dissipation to a universal exact law requiring no relation between contracted and unit charges.

For arbitrary cubic Xi Malgrange landings
- `x₀` at all Rees parameters zero,
- `x₁` at all Rees parameters one,

write (T_j=\sum_a \mathrm{terminalEnergy}_a(x_j)), (B_1=\sum_a \mathrm{blockEnergy}_a(x_1)), (r_j=\mathrm{commonRank}(x_j)), and (A=-\mathrm{globalRankCoefficient}). Then:
[
T_0+A r_1^2=T_1+B_1+A r_0^2,qquad A>0,qquad B_1>0.
]

Consequences:
- Terminal-isometric transport ((T_0=T_1)) forces strict rank-magnitude inflation (r_0^2<r_1^2).
- Rank-magnitude-preserving transport forces exact terminal dissipation (T_0=T_1+B_1) and (T_1<T_0).

The existing dissipation theorem was refactored as the second corollary.

## Scientific significance

This classifies every moving coefficient-generated Rees landing pair without assuming a source map. Search found source-side polarization isometries, but no coefficient-faithful bridge into `compatibleCharges`; no such bridge was invented. Any terminal-isometric wild/Stokes transport capable of landing the cubic Xi target must inflate physical rank magnitude.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicMovingChargeReesDissipation.lean`
- New card: `docs/drafts/pipeline/3-formalized/route-p-cubic-moving-charge-rank-terminal-balance.md`
- Companion card updated: `docs/drafts/pipeline/3-formalized/route-p-cubic-moving-charge-rees-dissipation.md`
- Frontier map remained untouched/read-only.

## Verification

Targeted module check passed after adding balance theorem and refactoring dissipation. Both affected public declarations depend exactly on `[propext, Classical.choice, Quot.sound]`. Scratch and generated `.olean` files were removed.

Related memories: `mem:research/irregular_stokes_cubic_moving_charge_rees_dissipation_2026_08_25`, `mem:research/irregular_stokes_cubic_local_ramification_capacity_2026_08_25`.
