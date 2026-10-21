# BAG — Pechersky prime-sum lemma at the natural rate; Bagchi's criterion on every half-scale disc

- **ID:** BAG-pechersky-natural-rate-half-scale-bagchi-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Read-only current frontier, BAG (`docs/reports/rh-current-frontier-map.md`); local Lean corpus (`ExponentialTypeNotSummableOnPrimeLogs`, `WeightedEulerPaleyWienerVanishing`, `PrimeShortIntervalsSevenTwelfths`, the Pechersky/Euler-product/recurrence chain of 2026-10-20).
- **Statement:** (i) For `Φ ≢ 0` entire of exponential type `ρ` and `0 ≤ σ`, the prime sums `Σ_{p<N} p^{−σ}‖Φ(log p)‖` are unbounded whenever `ρ < 1 − σ` and `ρ < 5/12` (formerly `3ρ < 1 − σ`; the intermediate first-order version needs `2ρ < 5/12`). In the Pechersky application `ρ < 1/4`, so the admissible range is exactly `ρ < min(Re z₀ − 1/2, 1 − Re z₀)`: the disc lies in the strip. (ii) Consequently every closed disc `closedBall c r` with `1/2 < Re c − 2r`, `Re c + 2r < 1` ("half-scale") is a disc of fixed-base strong recurrence of `ζ` as soon as `ζ` has no zero on `ball c (2r)`; and RH ⟺ `ζ` is strongly recurrent on every half-scale disc (equivalently: uniform head-target density on every half-scale disc).

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

## Second pass (same day): the small-value theorem that removes the cap

Asked for the Remez/Cartan small-value theorem behind the cap `2ρ < 5/12`, the corpus search found
Jensen-type zero counts (`LittlewoodXi.xi_zeroCount_disc_le_logModulus`, `JensenCount`,
`PrimeBlindCarlsonThreshold.sum_log_le_of_jensen`, mathlib `MeromorphicOn.divisor`) and the vendored
Borel–Carathéodory lemma, but no Cartan lemma, no polynomial Remez inequality and no analytic Remez
inequality. The full Remez/Cartan route (Jensen count → factor the zeros → Harnack on the zero-free
factor → Cartan/Remez on the polynomial factor) would give divergence for every `ρ < 1 − σ`, but it
is far larger than what the cap needs. The cap only has to move past `1/4`, and that follows from a
**second-order small-value lemma** that needs no zero counting:

* `eq_zero_of_two_ray_window_average_decay` (signed window two-ray theorem; the modulus form is now
  a corollary) gives `‖∫_0^1 Φ(x+t)e^{(ρ+δ/2)(x+t)}dt‖ ≥ e^{−δx/2}` at arbitrarily large `x`
  (`exists_window_average_ge_of_exponentialType`).
* **Midpoint rule** for entire functions along the real axis (`norm_integral_sub_midpoint_le`,
  error `2‖Φ''‖r³`; `norm_sum_midpoint_sub_integral_le`, total error `‖g''‖h²/4`): with windows of
  length `h ≍ y^{−ρ−δ/2}` the midpoint values of `‖Φ‖` carry the mass `≍ y^{−ρ−δ}`
  (`sum_norm_midpoint_ge_of_window_average`). The signed average is essential: the modulus `‖Φ‖`
  has no second-order Riemann-sum error.
* **One-sided second-order propagation** (`exists_side_norm_ge_of_norm_deriv_deriv_le`): for any
  `c`, on `[c, c+ℓ]` or on `[c−ℓ, c]`, `‖Φ‖ ≥ ‖Φ(c)‖ − ‖Φ''‖ℓ²`, because `‖A + tB‖ ≥ ‖A‖` whenever
  `t·Re(Ā B) ≥ 0` (`norm_le_norm_add_mul_of_nonneg`). With `ℓ = h/2` the loss is
  `≍ y^{ρ}y^{−2ρ−δ} = y^{−ρ−δ}`, a small multiple of the midpoint value, and the half-windows of
  log-length `≍ y^{−ρ−δ/2}` carry prime mass by the `7/12` theorem as soon as `ρ + δ/2 < 5/12`.

Result: `exists_primeLogWeightedSum_gt_of_lt_one_sub_of_lt_five_twelfths` (`ρ < 1 − σ`, `ρ < 5/12`),
module `RHTower/ExponentialTypeNotSummableOnPrimeLogsMidpointWindows.lean`. The chain now carries
only `1/2 ≤ Re z₀`, `2ρ − 2Re z₀ < −1`, `ρ < 1 − Re z₀` (the cap `ρ < 5/12` is derived from them),
and the half-scale Bagchi module needs no cap argument. What a genuine Remez/Cartan theorem would
add is divergence for `ρ ∈ [5/12, 1 − σ)`, which no disc of the strip uses.

## Lean

- `formal/GaloisForLFunctions/RHTower/ExponentialTypeNotSummableOnPrimeLogsNaturalRate.lean`:
  `unitWindowAverage`, `hasDerivAt_unitWindowAverage`, `eq_zero_of_forall_ofReal_eq_zero`,
  `eq_zero_of_two_ray_window_integral_decay`, `exists_window_integral_ge_of_exponentialType`,
  `norm_sub_le_of_exponentialType`, `integral_le_sum_window_values_add`,
  `sum_range_sum_Ioc_eq_sum_Ioc`, `primeWindow_sum_ge_of_window_value`,
  `exists_primeLogWeightedSum_gt_of_window_data`, **`exists_primeLogWeightedSum_gt_of_lt_one_sub`**.
- `formal/GaloisForLFunctions/RHTower/ExponentialTypeNotSummableOnPrimeLogsMidpointWindows.lean`:
  `norm_deriv_le_of_exponentialType_at`, `norm_deriv_deriv_le_of_exponentialType`,
  `norm_sub_sub_mul_deriv_le_of_norm_deriv_deriv_le`, `norm_integral_sub_midpoint_le`,
  `norm_sum_midpoint_sub_integral_le`, `norm_le_norm_add_mul_of_nonneg`,
  `exists_side_norm_ge_of_norm_deriv_deriv_le`, `exists_window_average_ge_of_exponentialType`,
  `sum_norm_midpoint_ge_of_window_average`, `primeWindow_sum_ge_of_lower_bound`,
  `exists_primeLogWeightedSum_gt_of_midpoint_data`, the constant lemmas
  (`exists_window_count`, `mul_sq_exp_div_le`, `midpoint_error_le`, `second_order_loss_le`,
  `window_size_condition`, `final_power_bound`), and
  **`exists_primeLogWeightedSum_gt_of_lt_one_sub_of_lt_five_twelfths`**.
- Hypothesis `3ρ < 1 − Re z₀` replaced by `ρ < 1 − Re z₀` (the first pass carried `2ρ < 5/12` as an
  extra hypothesis; the second pass removed it) in
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
- [x] 2 → 3  formalized: Lean theorems above, per-module `lake env lean` green, axioms PASS
- [ ] 3 → 4  not pursued (user rule: no stage 4)

## What remains open (exact)

- **Hoheisel cap: closed for the strip.** The first-order window method needed `2ρ < 5/12`; the
  second-order method needs `ρ < 5/12`, which every disc of the strip satisfies (`ρ < 1/4`). A
  Remez/Cartan small-value theorem (not in the corpus; only Jensen counts and Borel–Carathéodory are)
  would push the prime-sum divergence to all `ρ < 1 − σ`, but no disc of the strip uses that range.
- **Doubled-closure margin.** The Euler tail law requires `closedBall c (2r)` in the strip. Relaxing
  it to `closedBall c (r + ε)` would give RH ⟹ recurrence on every closed disc of the strip of
  radius `< 5/24`, and together with the cap removal the full `RH ⟺ ZetaDiscRecurrent`.
- The RH-selective obstacle (recurrence at a possible off-line zero) is untouched.

## Log
- 2026-10-21 — created; window two-ray theorem and natural-rate prime-sum lemma proved in Lean;
  downstream hypotheses weakened in place; half-scale Bagchi criterion module written.
- 2026-10-21 (second pass) — corpus search for Remez/Cartan building blocks (Jensen counts only);
  second-order window module written and compiled; cap hypothesis removed from the chain.
- 2026-10-21 — all seven modules compiled (`lake --old env lean -j 1 -o`, one at a time), axioms
  standard, both new modules wired into `RHTower.lean`, lint clean on these modules; moved to
  3-formalized.
