# BAG: the self-return threshold is the distance to nonvanishing targets; power-saving receiver

**Route:** BAG (deterministic ζ self-return). **Obstacle attacked:** the self-target at a point
not known to be zero-free (review-2110 O5: "exclude a zero from the disc with no intermediate
estimate").

**Date opened:** 2026-10-21.

## Goal

Sharpen the local Bagchi criterion `ζ(z₀) ≠ 0 ⟺ ∃ r, ZetaDiscStronglyRecurrentOn (closedBall z₀ r)`
into a quantitative law on every disc of the strip:

1. **Threshold law.** For a closed disc `D = closedBall z₀ r` with doubled closure in the strip,
   let `d(z₀, r)` be the uniform distance on `D` from `ζ` to the functions analytic and nonvanishing
   on a neighbourhood of `D`. Then `ε`-self-returns have positive lower density for `ε > d`, and
   for `ε < d` every `ε`-self-return height carries a zero of `ζ` in the shifted disc, so the
   return measure in `[0, T]` is `≤ C (1 + log T)^B T^θ` with `θ < 1` (Ingham–Huxley zero density).
   `d = 0 ⟺ ζ` has no zero in the open disc.
2. **Power-saving receiver.** `ζ(z₀) ≠ 0 ⟺` on some disc about `z₀` the self-return measure is not
   `O((1 + log T)^B T^θ)` for any `θ < 1`. So the gap between "positive density" and
   "measure zero" in the old criterion is closed: either linear or power-saving, nothing between.

## Corpus inputs (found with `scripts/formal_tools.py research`)

- `RHTower.zetaReturnSet`, `ZetaDiscStronglyRecurrentOn` (receiver / head-target modules).
- `RHTower.exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd` (universality on small discs).
- `RHTower.zetaZeroShadow`, `exists_volume_zetaZeroShadow_le_inghamHuxley`
  (XiSliceTypicalOrderPowerSaving), `inghamHuxleyExponent`.
- `DeBruijn.exists_zero_of_norm_lt_sphere_on` (minimum modulus), `exists_zetaIsolatingDisc_le`.
- `RHTower.exists_zetaDiscStronglyRecurrentOn_iff_ne_zero`.

## Conjecture log

- C1 (threshold law, 1 above): in progress.
- C2 (power-saving receiver, 2 above): in progress.
- C3 (order of vanishing = threshold exponent as `r → 0`): queued.

## Lean

Module (planned): `formal/GaloisForLFunctions/RHTower/ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets.lean`.
