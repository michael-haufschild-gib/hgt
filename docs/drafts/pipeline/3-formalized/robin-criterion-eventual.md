# Robin's criterion (eventual form)

- **ID:** robin-eventual
- **Stage:** 3-formalized (2026-10-04)
- **Type:** THEOREM (Lean, unconditional iff)
- **Source:** RH goal loop cycle 249
- **Statement:** RH ⟺ `σ(n) < e^γ n log log n` for all large `n`.

## Converse
Free from MUST-748: Robin for all large `n` contains Robin at `lcm(1,…,n)`.

## Forward (paper)
1. Extremal numbers. For `ε > 0`, `Q_p(ε) = 1 + (1 − 1/p)/(p^ε − 1)`, `a_p(ε) = max{k : p^k ≤ Q_p}`.
   `F_p(a) = (Σ_{j≤a} p^{−j}) p^{−εa}` has `F_p(a+1) ≥ F_p(a) ⟺ p^{a+1} ≤ Q_p`, so `a_p` maximizes.
   `N_ε = ∏ p^{a_p}` maximizes `σ(m)/m^{1+ε}` (Lagrangian inequality
   `log(σ(n)/n) − ε log n ≤ log(σ(N)/N) − ε log N`).
2. Choice `ε = 1/(ℓ log ℓ)`, `ℓ = log n`. Concavity of `log log`: the mismatch
   `ε(ℓ − log N) − (log log ℓ − log log log N) ≤ 0` in both cases `log N ≤ ℓ`, `log N ≥ ℓ`.
   So Robin at `n` ⟸ Robin defect at `N_ε` negative.
3. Parametrize `ε = ε(x) = log(1 + 1/x)/log x`: `a_p ≥ 1 ⟺ p ≤ x`; for `p ≤ (5/4)√x`, `a_p ≥ 2`;
   for `(3/2)√x < p ≤ x`, `a_p = 1`. IVT gives `x` with `ε(x) = 1/(ℓ log ℓ)`, `x → ∞`.
4. Under RH: `D_R(N_x)√x log x ≤ Φ + 1 + 1 − 5/4 − 4/3 + o(1) ≤ a₁ − 0.58 + o(1) < 0`, from
   `Δ√xL → 1`, `G√xL − Φ → 0`, `(ψ − θ)/√x → 1`, `log N − θ(x) ≥ θ((5/4)√x)`,
   `E_N ≥ Σ_{(3/2)√x<p≤x} p^{−2} ~ (4/3)/(√x log x)`, second-order `O(log⁴x/x)`.

## Lean plan
- [x] L1 extremal exponents, per-prime maximality, Lagrangian inequality.
- [x] L2 thresholds at `ε(x)`.
- [x] L3 RH asymptotic: Robin defect at `N_x` negative eventually.
- [x] L4 mismatch lemma + IVT + assembly; iff.

## Lean status (complete)
- `RHTower.riemannHypothesis_iff_eventually_robin` (RobinCriterionRiemann.lean).
- Extremal numbers and Lagrangian inequality: `log_sigma_div_sub_le_robinExtremal` (RobinExtremalNumbers.lean).
- Thresholds: `one_le_robinExponent_iff_le`, `eventually_two_le_robinExponent`,
  `robinExponent_le_one_of_gt`, `eventually_sum_prime_inv_sq_scaled_ge` (RobinExtremalThresholds.lean).
- RH at `N_x`: `eventually_robin_robinExtremalAt`; mismatch `log_log_sub_log_log_le`.
