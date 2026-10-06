# Prime-blind extremal certificates: universality test and spectral zero structure (2026-10-06)

## Question
- The corpus observed (2026-10-03) that one extremal prime-blind certificate is optimal for both the even and the
  odd archimedean datum, and used this to explain why thresholds multiply.
- The arch kernels `ω_μ(x) = Σ_k e^{−(μ+½+2k)x}` are completely monotone.
- Conjecture tested: a Cohn–Kumar-type universal optimality. A single prime-blind PD certificate (`g(0)=1`,
  `g(log n)=0` for all n ≥ 2) would then be optimal for every completely monotone objective.

## Setup
- Cubic B-spline span on `[−L/2, L/2]`, `X ⪰ 0`, `tr(GX)=1`, and `tr(S_n X)=0` for `n ≤ e^L` (CLARABEL).
- Scripts: `univ.py`, `univ2.py`; `weilform.py` and `threshold2.py` are copied from `2026-10-03-positivity-conductor-threshold`.
- Objectives:
  - `arch_μ` for `μ ∈ {0, ½, 1, 2, 4}`;
  - Lorentz/Laplace objectives `max ∫e^{−α|x|}g` for `α ∈ {½, 2, 8}`;
  - a joint SDP minimizing the largest excess over all objectives.

## Results
- **Universality fails.** The cross-gaps `tr(Q_ν X*_μ) − V_ν` are stable in L (2.5, 3.0) and in the basis (hk 0.05, 0.035):

  | gap | value |
  |---|---|
  | μ=0 → 1 | 2.5e-6 |
  | μ=0 → 4 | 1.42e-4 |
  | μ=4 → 0 | 3.6e-4 |
  | Lorentz α=½ → arch | 0.007–0.011 |

  - Joint excess: 5.3e-5 over the arch family, 1.9e-4 over all objectives.
- **Consequence.** Thresholds are only approximately multiplicative:
  - `log q*(Γ_ℂ) ≥ log q*_even + log q*_odd − 2.5e-6`.
  - The even/odd near-coincidence is a small-defect accident, not a law.
- Controls:
  - Turán value `max ∫g = log 2` reproduced to 8 digits;
  - `q*_even = 4.036275`, `q*_odd = 2.860550` (L = 3).
- **Spectral zeros of the certificates** (minima of `h*(t)=|ĝ*|²` on `t ≤ 120`):
  - **No-pole even certificate.** Zeros sit at `2πk/log 2` and at *displaced* ζ-zeros: 14.102 (vs 14.135), 21.11 (21.02), 24.90 (25.01), 30.47 (30.42). Higher up the minima are spaced 2–3 and unrelated to ζ. So the certificate is not ζ-null; the critical object is a deformation of ζ.
  - **No-pole odd certificate.** Same pattern as the even one.
  - **ζ-datum certificate** (pole, L = 3):
    - minima exactly at ζ zeros (distance ≤ 0.001) up to t ≈ 50, and no other deep minima below 50;
    - above about 50, minima unrelated to ζ (resolution height of support 3);
    - `X*` has high rank: the optimal face is large.
  - L = 3.5: the solver loses PSD accuracy (h* < 0 at some points); discard.

## Interpretation
- The prime-blind LP has no hidden exact universal structure: no Cohn–Kumar universal optimality.
- So the thresholds 4.0363 and 2.8606 are unlikely to have closed forms. An exact analytic solution of the prime-blind LP, which would have been a route to PBAP, is not available.
- The ζ-datum certificate's real zero set below the resolution height is exactly ζ's zeros. This is consistent with (N1), but already implied by the corpus pinning results.
