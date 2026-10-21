# BAG — Pechersky prime-sum lemma at the natural rate; Bagchi's criterion on every half-scale disc

- **ID:** BAG-pechersky-natural-rate-half-scale-bagchi-2026-10-21
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Read-only current frontier, BAG (`docs/reports/rh-current-frontier-map.md`); local Lean corpus (`ExponentialTypeNotSummableOnPrimeLogs`, `WeightedEulerPaleyWienerVanishing`, `PrimeShortIntervalsSevenTwelfths`, the Pechersky/Euler-product/recurrence chain of 2026-10-20).
- **Statement:** (i) For `Φ ≢ 0` entire of exponential type `ρ` and `0 ≤ σ`, the prime sums `Σ_{p<N} p^{−σ}‖Φ(log p)‖` are unbounded whenever `ρ < 1 − σ` and `2ρ < 5/12` (formerly `3ρ < 1 − σ`). (ii) Consequently every closed disc `closedBall c r` with `1/2 < Re c − 2r`, `Re c + 2r < 1` ("half-scale") is a disc of fixed-base strong recurrence of `ζ` as soon as `ζ` has no zero on `ball c (2r)`; and RH ⟺ `ζ` is strongly recurrent on every half-scale disc (equivalently: uniform head-target density on every half-scale disc).

## Goal

The BAG ledger records the Pechersky range `3ρ < 1 − Re z₀` as the reason the chain
"finite Euler product universality → cutoff-uniform Euler-target density → fixed-base recurrence"
reaches only small discs: the recurrent disc about a zero-free point had radius `< (1 − Re z₀)/3`
(times the Carlson margin), so the RH ⟹ recurrence direction was available only in the `∃ r` form
(local Bagchi criterion). The natural Pechersky range is `ρ < 1 − Re z₀` (the Hardy disc lies in
`Re z < 1`). This card closes that gap up to the Hoheisel cap `ρ < 5/24` inherited from the `7/12`
short-interval exponent, which never binds inside the chain because the Euler tail law already
requires the doubled closure in the strip (`r < 1/8`).

Not claimed: recurrence on discs whose doubled closure leaves the strip (that is the margin of the
Euler tail law `eventually_eventually_volume_eulerDiscTailBadSet_le`, a separate limitation), and
nothing about recurrence at a hypothetical off-line zero (the RH-selective obstacle of the ledger).

## Components connected

1. `RHTower/WeightedEulerPaleyWienerVanishing` — the two-ray Paley–Wiener theorem
   `eq_zero_of_two_ray_exponential_decay` (entire, exponential type, decaying on both real rays
   ⟹ zero).
2. `RHTower/ExponentialTypeNotSummableOnPrimeLogs` — the Cauchy derivative estimate
   `norm_deriv_le_of_exponentialType`, the window lemma `window_sum_ge_theta_window`, the prime
   sum `primeLogWeightedSum`.
3. `RHTower/PrimeShortIntervalsSevenTwelfths` — `exists_theta_window_lower_seven_twelfths`
   (Chebyshev mass `≥ (L − (y+L)^α)/2` in `(y, y+L]` for `α > 7/12`).
4. Mathlib: differentiation under the interval integral
   (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), the fundamental theorem
   of calculus, `sum_integral_adjacent_intervals`, the identity theorem.
5. The 2026-10-20 chain `PecherskyDensityPrimeVectorsHardyDisc → PhasedEulerProducts… →
   FiniteEulerProductUniversalityOnDiscs → UniformEulerTargetDensityOnZeroFreeDiscs →
   ZetaDiscRecurrenceOnZeroFreeDiscs` (hypothesis weakened in place).

## Mechanism (the new idea)

The old proof found one point `x` with `‖Φ(x)‖ ≥ e^{−(ρ+δ)x}` (two-ray theorem applied to
`Φ(w)e^{(ρ+δ/2)w}`) and propagated it by the derivative bound `‖Φ'‖ ≤ Ce^{ρx}` to a window of
length `e^{−(2ρ+δ)x}`: three powers of `ρ` are lost (`1 − σ − 3ρ`).

**Window two-ray theorem** (`eq_zero_of_two_ray_window_integral_decay`): if an entire `g` of
exponential type decays exponentially on the negative ray and its *unit-window integrals*
`∫_0^1 ‖g(x+t)‖dt` decay exponentially on the positive ray, then `g ≡ 0`. Proof: the window
average `F(w) = ∫_0^1 g(w+t)dt` is entire (differentiation under the integral) with the same
two-ray decay, so `F ≡ 0` by Paley–Wiener; `F' = g(·+1) − g ≡ 0` makes `g` 1-periodic, and the
decay on the negative ray then kills `g` on `ℝ`, hence everywhere.

Applied to `Φ(w)e^{(ρ+δ/2)w}` this yields `∫_0^1 ‖Φ(x+t)‖dt ≥ e^{−(ρ+δ)}e^{−(ρ+δ)x}` at
arbitrarily large `x`: the *average* of `‖Φ‖` over `[x, x+1]` is large, not just one value. Cutting
`[x, x+1]` into `N = ⌈1/η⌉` windows of length `h ≤ η = c₁y^{−(2ρ+2δ)}` (`y = e^x`), the lower
Riemann sum differs from the integral by at most `hD ≤ m/4` (`D = Ce^{ρ(x+3)}`), each window
`(e^{x+kh}, e^{x+(k+1)h}]` carries Chebyshev mass `≥ yh/4` because `yh ≥ (c₁/2)y^{1−2ρ−2δ}` and
`1 − 2ρ − 2δ > 7/12` (this is where `2ρ < 5/12` enters), and summing the window bounds gives a
prime sum over `(y, ey]` of size `≥ c·y^{1−σ−ρ−δ}/(x+1)`, unbounded iff `ρ < 1 − σ`.

## Lean

- `formal/GaloisForLFunctions/RHTower/ExponentialTypeNotSummableOnPrimeLogsNaturalRate.lean`:
  `unitWindowAverage`, `hasDerivAt_unitWindowAverage`, `eq_zero_of_forall_ofReal_eq_zero`,
  `eq_zero_of_two_ray_window_integral_decay`, `exists_window_integral_ge_of_exponentialType`,
  `norm_sub_le_of_exponentialType`, `integral_le_sum_window_values_add`,
  `sum_range_sum_Ioc_eq_sum_Ioc`, `primeWindow_sum_ge_of_window_value`,
  `exists_primeLogWeightedSum_gt_of_window_data`, **`exists_primeLogWeightedSum_gt_of_lt_one_sub`**.
- Hypothesis `3ρ < 1 − Re z₀` replaced by `ρ < 1 − Re z₀ ∧ 2ρ < 5/12` in
  `PecherskyDensityPrimeVectorsHardyDisc` (`exists_sum_norm_inner_primeTerm_gt`,
  `exists_unimodular_primeTerm_sum_approx`, `exists_unimodular_prime_sum_approx_on_disc`),
  `PhasedEulerProductsApproximateExponentialsOfHardyFunctions`
  (`exists_unimodular_eulerProduct_approx_exp`), `FiniteEulerProductUniversalityOnDiscs`
  (`exists_pos_density_eulerTargetReturnSet_exp`, `_zeta`), `UniformEulerTargetDensityOnZeroFreeDiscs`
  (`exists_uniform_pos_density_eulerTargetReturnSet_zeta`), `ZetaDiscRecurrenceOnZeroFreeDiscs`
  (`zetaDiscStronglyRecurrentOn_of_zeroFree`).
- `formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnHalfScaleDiscs.lean`:
  `IsHalfScaleStripDisc`, `zetaDiscStronglyRecurrentOn_of_zeroFree_halfScale`,
  `zetaDiscStronglyRecurrentOn_of_riemannHypothesis`, `exists_isHalfScaleStripDisc`,
  **`riemannHypothesis_iff_forall_halfScale_zetaDiscStronglyRecurrentOn`**,
  `riemannHypothesis_iff_forall_halfScale_headTargetUniformlyDense`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only (checked from a scratch file).
- Both new modules wired into `GaloisForLFunctions/RHTower.lean`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof (above), no open dependency
- [ ] 2 → 3  formalized: Lean theorems above, per-module `lake env lean` green, axioms PASS
- [ ] 3 → 4  not pursued (user rule: no stage 4)

## What remains open (exact)

- **Hoheisel cap.** The window method needs windows of log-length `≍ y^{−(2ρ+2δ)}` to carry prime
  mass, which with the corpus exponent `7/12` forces `2ρ < 5/12`. Discs of radius `r ∈ [5/24, 1/4)`
  are therefore outside the sharpened Pechersky range. Removing the cap needs either a short-interval
  exponent `≤ 1/2` (beyond current technology) or a Remez/Cartan-type small-value theorem for
  entire functions of exponential type (a positive-proportion lower bound on `[x, x+1]` without the
  derivative loss); the latter is a self-contained analytic project.
- **Doubled-closure margin.** The Euler tail law requires `closedBall c (2r)` in the strip. Relaxing
  it to `closedBall c (r + ε)` would give RH ⟹ recurrence on every closed disc of the strip of
  radius `< 5/24`, and together with the cap removal the full `RH ⟺ ZetaDiscRecurrent`.
- The RH-selective obstacle (recurrence at a possible off-line zero) is untouched.

## Log
- 2026-10-21 — created; window two-ray theorem and natural-rate prime-sum lemma proved in Lean;
  downstream hypotheses weakened in place; half-scale Bagchi criterion module written.
