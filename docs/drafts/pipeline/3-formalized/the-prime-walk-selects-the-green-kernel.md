# The prime walk selects the Green kernel

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: distinguish a point-source solution from the actual minimal Green kernel.
- **Statement:** For the actual uniform walk `P_p=A_p/(p+1)` on projective
  p-adic vertices, `G_{p,1}(x,y)=(p+1)⁻¹ Σ_{k≥0} P_p^k δ_x(y)`.
  This is the least nonnegative supersolution of `(p+1−A_p)u≥δ_x`.

## Proof

The source identity telescopes finite walk sums, leaving `P_p^N G_{p,1}`.
The intrinsic ratio satisfies `0<R≤1`, so `G_{p,1}` is bounded by a fixed
positive multiple of `G_{p,1/2}`. The tempered source identity gives
`P_p G_{p,1/2}≤ρ_p G_{p,1/2}`, where `ρ_p=2√p/(p+1)<1`.
Positivity of the actual adjacency sum then bounds the remainder by
`C ρ_p^N G_{p,1/2}`, which tends to zero. Iterating any nonnegative
supersolution bounds every finite walk sum and gives minimality.

This identifies `(p+1)G_{p,1}(v,v)−1=1/(p−1)` as the total return
mass after time zero. It does not construct a global adelic regularization.

## Lean status

`ThePrimeWalkSelectsTheGreenKernel.lean`, namespace `PrimeWalk`:

- `walkStep_one`, `walkMass_nonneg`, `walkMass_le_one`: actual uniform walk.
- `harmonic_iter_bound`, `greenPartial_eq`: geometric remainder and exact telescope.
- `hasSum_walkGreen`: convergent occupation sum equals the intrinsic kernel.
- `localGreen_isLeast`: least nonnegative supersolution, with no boundedness assumption.
- `hasSum_returns`: return probabilities after time zero sum to `1/(p−1)`.

Plain `lake --old env lean` passes without warnings. All four audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The [full branch selection](the-minimal-branch-of-the-adelic-green-kernel.md)
also identifies the critical walk sum and the positive harmonic excess below the minimal branch.
