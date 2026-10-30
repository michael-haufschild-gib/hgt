# Reboot-final checks (2026-10-30)

Two small checks backing `docs/reports/review-3010/reboot-final.md` (fact log section G13). Both ran
in seconds; no runpod job was needed.

## `census.py`
- `HD(1) = 3/2 − 2^{−1/2}cot 2^{−1/2} = 0.6725007037` (the Montgomery–Taylor constant used by the Zeta23
  census); `2HD/(1+HD) = 0.8041858`; `1 − (1−HD)/(3/2+√2) = 0.8876200`.
- TTPC's Frobenius-norm formula `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F(α)dα` with the GUE form factor gives the
  rank–trace certificate `2 − κ = 1 − 1/(3λ²)` for `λ ≥ 1` (13/16 at λ = 4/3, 8/9 at √3).
- Consequence: even with full pair-correlation knowledge at every bandwidth, the rank–trace census
  approaches 100% and never reaches it, so it cannot prove RH.

## `mertens.py`
- Prime part of the pole-vector residual of the complete Weil matrix:
  `‖P_N x − (log N − γ)x‖²`, `x_n = n^{−1/2}`, `P_N(m,n) = Λ(n/m)(n/m)^{−1/2}` on `[1, N]`.
  Row `n` is `n^{−1/2}(A(⌊N/n⌋) + log n − log N + γ)` with `A(y) = Σ_{t≤y} Λ(t)/t`.
- Result: `0.0832` for `N = 10⁴, 10⁵, 10⁶, 2·10⁶` (independent of `N`). Share from rows with
  `⌊N/n⌋ < 2, 4, 16, 256`: `0.777, 0.879, 0.965, 0.998`.
- Interpretation: the `(log N)^{−1/2}` relative quasimode error in the fixed-overlap positivity proof
  (`exists_completeWeil_completedConductor_residual_horizon_bound`) is a fixed boundary layer at the horizon,
  with the `N`-independent profile `R(y) = A(⌊y⌋) − log y + γ`. It is not a decaying prime-sum error.

## Not computed (outcome predictable)
The bottom eigenvalue of `log N·I − P_N`: the pole-vector Rayleigh quotient is
`γ − (Σ_n R(N/n)/n)/H_N ≈ γ − (∫_1^∞ R(y)dy/y)/log N`, and second-order perturbation lowers it by about
`0.0832/((E_2 − γ) log N)` (`E_2 − γ = 2 log 2`). The `[1,2)` part of `∫R dy/y` is
`γ log 2 − (log 2)²/2 = 0.160`, and `R` stays positive up to `y ≈ 10` (values above), so the bottom should
approach `γ` from below at rate `1/log N`. This is a prediction, not a computed result.
