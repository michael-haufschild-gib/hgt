# Robin's inequality at lcm(1,…,n)

- **ID:** robin-lcm
- **Stage:** 3-formalized (2026-10-04)
- **Type:** THEOREM (Lean, unconditional iff)
- **Source:** RH goal loop cycle 247 (after Nicolas cycles 242–246)
- **Statement:** RH ⟺ `σ(L_n) < e^γ L_n log log L_n` for all large `n`, `L_n = lcm(1,…,n)`.

## Why it should work (paper)
`σ(L_n)/L_n = ∏_{p≤n} (1 − p^{−K_p−1})/(1 − 1/p)`, `K_p = ⌊log_p n⌋`, `log L_n = ψ(n)`. With
`P = −log ∏(1 − 1/p)`, `G` the Mertens remainder, `Δ = P − A` the prime tails and
`λ_ψ = log log ψ − log log x`:

`log(σ/L) − γ − log log ψ = G + Δ + [E/(x log x) − λ_ψ] + Σ_p log(1 − p^{−K_p−1})`.

* bracket `≥ 0` always (`log y ≤ y − 1` twice); `= O(ε_ψ²/log x)`.
* `Δ √x log x → 1` and `Σ_p −log(1 − p^{−K_p−1}) √x log x → 2` (both from `Σ_{√x<p≤x} p^{−2} ~ 2/(√x log x)`,
  PNT suffices).
* `G √x log x − Φ(log x) → 0` under RH.

Forward: under RH the scaled defect → `Φ − 1 ≤ a₁ − 1 < 0`. Converse (no Θ issue — the bracket has the
favourable sign): Robin eventually ⇒ `G √x log x ≤ 1 + o(1)` ⇒ (inversion `v = Gr + ∫ Gq + tail`) `Φ` bounded
above ⇒ RH (`riemannHypothesis_iff_weilLagFunctionReal_bddAbove`).

Contrast: Nicolas = lower lag bound at −2 with unfavourable second-order sign (Θ = 1 gap); Robin-lcm =
upper lag bound at +1 with favourable sign.

## Lean plan
- [x] S1 σ(L_n)/L_n product formula.
- [x] S2 PNT prime-square asymptotic (unconditional).
- [x] S3 Δ√x log x → 1 (unconditional).
- [x] S4 Σ −log(1 − p^{−K−1}) √x log x → 2.
- [x] S5 ψ-bracket bounds.
- [x] S6 forward (RH ⇒ Robin at L_n eventually).
- [x] S7 converse.

## Lean status (complete)
- `RHTower.riemannHypothesis_iff_eventually_robin_lcmUpto` (RobinLcmRiemannCriterion.lean) — the iff.
- `RHTower.tendsto_robinLcmDefect_scaled_sub_lag` — under RH `D(n)√n log n − Φ(log n) → −1`.
- `RHTower.robinLcmDefect_scaled_bounds_of_riemannHypothesis` — constants `−1 ± a₁`, limsup along primes.
- `RHTower.tendsto_robinExponentDeficit_scaled` — `E(n)√n log n → 2`, unconditional.
- `RHTower.riemannHypothesis_iff_mertensErrorRemainder_le` — one-sided remainder criterion (MUST-749).
- S3 was not needed separately: Δ√x log x → 1 used only under RH (forward); the converse uses Δ ≥ 0.
- STATUS: MUST-748, MUST-749.
