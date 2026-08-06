# Route R first-wall lane: TERMINUS, criterion re-encoding (2026-08-06, fourth pass)

Closes the arc of `mem:route_r/harmonic_quantum_gap_criterion_2026_08_06`,
`mem:route_r/first_wall_scale_quantification_2026_08_06`,
`mem:route_r/first_wall_two_sided_scale_law_2026_08_06`.
Module `RHTower/RouteRFirstWallScaleQuantification.lean`; axioms
`[propext, Classical.choice, Quot.sound]` throughout.

## RH characterization (unconditional iff)

`riemannHypothesis_iff_frequently_abs_re_profileAverage_lt_one`: for ANY bounded cofinal
prime-harmonic profile `mu`,

  `RiemannHypothesis ↔ ∀ rho : XiDivisorSupport, ∃ r < 1, ∃ᶠ N in atTop,
     |(profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)).re| ≤ r`

Forward uses `profileAverage_criticalWall_zero_eq_zero` (neutral grade kills the field identically)
plus the corpus theorem `xi_divisor_support_re_eq_half_of_rh` (in `CentralReciprocalMoments`, which
imports nothing from Route R — no cycle).

## Premises discharged

- `eventually_deepStage` — `{p : Nat.Primes | (p:ℕ) < Q}` is finite (inject into `Finset.range Q`,
  `Set.Finite.of_finite_image`), so `IsCofinalUnitProfile.escapes` already forces every far-enough
  stage above depth `Q`. The depth floor is FREE; never assume it again.
- `exists_deepStage_of_frequently` — hence the deep-stage and asymptotic criteria coincide.
- `abs_le_of_frequently_norm_profileAverage_le` — one frequent modulus bound gives the explicit
  grade bound at every admissible depth simultaneously.
- `norm_stageAverage_criticalWall_le_scale` — linearized ceiling `‖A‖ ≤ 2 |t| log Q`.

## Why the lane is finished

Four no-freedom facts, all proved:

1. device: every bounded cofinal unit profile computes the same coordinate;
2. depth floor: supplied automatically by escape;
3. bounded depth: every depth-ceilinged stage is evaded by nonzero grades (third-pass no-go);
4. two-sided pinning: `(1 - q^(-2|t|))(1-3/q) ≤ ‖A‖ ≤ min(1 - Q^(-2|t|), 2|t| log Q)`.

Consequence: no bound on `|t_rho|` short of zero is extractable. A bound `|t| ≤ δ` with fixed `δ > 0`
is exactly a bounded-depth certificate, and those are always satisfiable by nonzero grades. So the
open core equals RH per zero with nothing left to trade.

**Do not sharpen this reporter family further.** Route R's remaining hope must come from a different
producer, not a better reader. See `mem:rh/route-r-novelty-classification-2026-08-03` and the
criterion-re-encoding template.
