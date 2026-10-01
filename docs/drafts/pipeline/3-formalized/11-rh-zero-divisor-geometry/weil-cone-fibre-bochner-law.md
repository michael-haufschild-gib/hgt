# The fibre Bochner law of the Weil cone, and the end of the Cramér-restored producers

- **ID:** weil-cone-fibre-bochner-law
- **Stage:** 3-formalized (MC loop cycle 179)
- **Type:** THEOREM (Lean)
- **Source:** cycle 178 limit (notch blind to rough deficits); HF krein-producer-loops L201 (pinned continuous producer `Λ − (1/4π)1_ℙ + (1/4π)/log n`), L206.
- **Statement:**
  - **(i) Fibre Bochner law.** Let `lam` be full-cone Weil-positive with notch-small `d = lam − Λ`. For every finite prime set `P`, every finite `A ⊂ ℤ^P` and every real `c`, the partial sums of `d(n) n^{−½} W_q(n)` cannot stay above a positive level. Here `q(t) = |Σ_{a∈A} c_a e^{itλ(a)}|²` and `W_q(n) = Σ_{a,a'} c_a c_{a'} (h k)^{−½}` over the reduced twists `h/k = n Π_p p^{−(a−a')_p}`.
  - **(ii)** For every `κ > 0`, `Λ − κ 1_ℙ + κ/log n` is not Weil-positive. This includes HF's pinned `κ = 1/(4π)`.
  - **(iii)** With MUST-601: no Cramér-restored profile `Λ + κ(1_ℙ − 1/log n)`, `κ ≠ 0`, is Weil-positive.

## Goal
- Cycle 178 found that the Euler-weighted notch only sees `P`-rough sums. Rough deficits (prime deficit balanced by composite excess) are therefore invisible to it.
- The Euler factors `|1 − p^{−½+it}|²` were built to cancel the Bohr lift off the rough fibre. Dropping them gives a general twist polynomial `q`, whose main functional keeps every `P`-fibre with the Poisson weights `Π_p p^{−|v_p(n) − g_p|/2}`.
- A Cramér density `κ/log n` has no Euler structure, so the `2`-adic fibres see it.

## Proof
1. **General refined notch** (`exists_norm_weightedMoment_sub_logMain_le_twist`).
   - The coordinate bounds for an arbitrary twist vector with `|g_p| ≤ B_p` give, with `K = Π p^{B_p}`: `hk ≤ Kn`, `n ≤ K hk`, `|log hk − log n| ≤ log K`, `k ≤ K` and `√(2k/h) ≤ 2K²n^{−½}`.
   - The twisted moment expands as `M^q = Σ_{a,a'} c_a c_{a'} M(log n − λ(a − a'))`.
   - The R2 bookkeeping then gives `‖M^q_L(log n) − 1_{K₀n≤L/4} W_q(n) T(n)‖ ≤ D · refWeight`.
2. **Abstract scale bound** (`exists_ramp_scale_bound_of`). Any nonnegative `q` with a bounded entire extension, plus a per-scale ramp inequality, gives `κ log(L−1) ≤ C_η + η K log(L−1)` (refactored from MUST-599). `false_of_log_scale_bound` closes it.
3. **The test `q = |1 + 2^{it}|²`** (`P = {2}`, `A = {0, e}`, `c = 1`). `W_q(n) = (2 + √2) n^{−½}` for odd `n` and `(2 + √2 + 1/√2) n^{−½}` for even `n` (`twistMainWeight_twoSet`).
4. **Asymptotics.**
   - The fibre sum is `κ[(2+√2)(O − P_odd) + (2+√2+1/√2)(E − ½)]`, where:
     - `O`, `E` are the odd and even sums of `1/(n log n)`;
     - `P_odd = Σ_{odd p} 1/p ≤ log log k + C` (`mertensSecond_upper`).
   - Pairing with the decreasing `g(n) = 1/(n log n)` gives `2O ≥ A − g(2)` and `2E ≥ A`, with `A ≥ log log(k+1) − log log 2` by telescoping.
   - Hence the sum is `≥ κ((1/(2√2)) log log k − C) → +∞`, which contradicts (i).

## Kill attempt and audit
- **FALSE?** No; the proof is complete and formal.
- **CIRCULAR?** No.
- **REDISCOVERED?** No. HF killed L201 only heuristically, and conditionally (local `log|ζ|` sign at the zeros, RH-conditional). This kill is unconditional and arithmetic, at `s = 1`.
- **INSIGNIFICANT?** Moderate–high for the HF lane.
  - It removes the natural realization of the uniform-evaporation survivor (L201) rigorously and unconditionally.
  - It shows that every Cramér-type restoration of `Λ` dies.
  - The general Bochner law is a structural necessary condition on all notch-small second points.
- **Verdict:** SURVIVES → [L].

## New insight and limits
- **Insight.** Weil positivity forces the `P`-fibre functional `g ↦ Φ(g) = Σ d(n) n^{−½}(h_g k_g)^{−½}` to be asymptotically non-positive against every positive-definite pattern `c ⊗ c`. A notch-small decoration must be "Euler-compatible at s = 1": prime and composite parts must balance fibre by fibre, not only in the window aggregate. The Cramér density fails because `Σ n^{−s}/log n` has no Euler product.
- **Still open:**
  - decorations whose fibre functionals are negative semidefinite but non-zero, e.g. Euler-multiplicative deficits such as `−κΛ/log n`. Those fail pinning by MUST-586 only when they are one-signed;
  - `d ≍ Λ`, the `α ≥ 1` wall.
- The next test question is whether Bochner negativity on all `ℤ^P` fibres, combined with pinning, forces `d = 0` for notch-small `d` (a "fibre Wiener" theorem).

## Log
- 2026-10-01 — cycle 179: modules `ZetaNotchTwistPolynomialEnvelope` and `WeilFibreBochnerLaw`; refactor of the mixture, pairing and scale-bound lemmas to arbitrary `q` in `ZetaNotchRampMainTerm` and `WeilLittleOVonMangoldtRigidity`.
