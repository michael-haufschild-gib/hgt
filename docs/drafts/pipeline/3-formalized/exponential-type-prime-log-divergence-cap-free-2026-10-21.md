# Prime-log divergence of entire functions of exponential type, without the cap

- **ID:** prime-log-divergence-cap-free
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md §BAG (source input `R:ExponentialTypeNotSummableOnPrimeLogs`: Pechersky divergence of the prime vectors); the cap `2ρ < 5/12` of the natural-rate module
- **Statement:** For `Φ ≢ 0` entire with `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}`, `0 ≤ σ` and `ρ < 1 − σ`, the sums `Σ_{p<N} p^{−σ}‖Φ(log p)‖` are unbounded (`exists_primeLogWeightedSum_gt_of_lt_one_sub_capFree`). No cap on `ρ`.

## Goal
The natural-rate theorem of the other agent measures the variation of `Φ` on real windows by the global type (`‖Φ'‖ ≲ e^{ρx}`) while its size on the ray is only known at the worst rate `e^{−(ρ+δ)x}`; the windows then have log-length `e^{−(2ρ+δ)x}` and the `7/12` short-interval theorem caps `2ρ`. The almost-all-short-intervals theorem (`PrimeAlmostAllShortIntervals`, `x^{1/6+ε}`, already in the corpus) does not remove the cap: its exceptional set has only logarithmic savings, and `Φ` may be large on an exponentially thin set, so the loss on bad windows is weighted by `sup|Φ| ≍ e^{ρx}`.

What removes the cap is to measure size and variation of `Φ` at the same rate, the ray exponent `a = h(0) = inf{a : ‖Φ(t)‖ ≤ e^{at} eventually}`:
- `neg_le_rayExponent`: `a ≥ −ρ` by the corpus two-ray theorem (`eq_zero_of_two_ray_exponential_decay`, found by search);
- `exists_exp_rayExponent_sub_lt`: `‖Φ(t)‖ > e^{(a−δ)t}` at arbitrarily large `t` (definition of the infimum);
- `exists_thinStrip_bound`: `‖Φ(t+iy)‖ ≤ M₁e^{(a+δ)t}` for `t ≥ 0`, `|y| ≤ 1`, by Mathlib's quadrant Phragmén–Lindelöf (`PhragmenLindelof.quadrant_I/IV`) applied to `Φ(w)e^{−(a+δ ∓ iρ)w}`, bounded on the real axis by the admissible exponent and on the imaginary axes by the type;
- `norm_sub_le_of_thinStrip`: Cauchy on unit discs gives the Lipschitz constant `M₁e^{3|a+δ|}e^{(a+δ)x}` on `[x, x+2]`;
- generic-Lipschitz copies of the window assembly (`primeWindow_sum_ge_of_window_value_lip`, `exists_primeLogWeightedSum_gt_of_window_data_lip`) reuse `window_sum_ge_theta_window`, `integral_le_sum_window_values_add`, `sum_range_sum_Ioc_eq_sum_Ioc`, `window_sum_le_primeLogWeightedSum` and the `7/12` theorem `exists_theta_window_lower_seven_twelfths` at exponent `α = 1 − 7δ`.
Then `Φ ≥ ½e^{(a−δ)x}` on a window of log-length `e^{−3δx}`, the prime windows have log-length `≍ e^{−6δx}`, and the window contributes `≥ e^{−σ}e^{(1−σ+a−4δ)x}/(16(x+1)) ≥ e^{−σ}e^{(1−σ−ρ−4δ)x}/(16(x+1))`, unbounded iff `ρ < 1 − σ`.

Status relative to the chain: in parallel the other agent proved the cap `ρ < 5/12` by second-order midpoint windows (`ExponentialTypeNotSummableOnPrimeLogsMidpointWindows`) and, since `ρ < 1/4` in the Pechersky application, dropped the cap hypothesis from the whole chain at 18:00; the universality and recurrence modules of the BAG lane now carry only `ρ < Re z₀ − 1/2`, `ρ < 1 − Re z₀`, and I adapted my two modules accordingly (universal radius `min((Re z₀−1/2)/6, (1−Re z₀)/6)`, no cap). The cap-free theorem is the stronger general statement; the chain does not need to be re-pointed at it.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proof as above
- [x] 2 → 3  Lean: `formal/GaloisForLFunctions/RHTower/ExponentialTypeNotSummableOnPrimeLogsCapFree.lean`; `lake env lean` green, no warnings; `#print axioms` standard on all declarations; wired into `GaloisForLFunctions/RHTower.lean` after the natural-rate module; lint clean for the module
- [ ] 3 → 4  not pursued

## Log
- 2026-10-21 — created directly in 3-formalized; built, wired, axioms standard; my two BAG consumer modules re-adapted to the chain's cap-free signatures.
