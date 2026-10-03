# Certified pinning of producers (2026-10-03)

## Computed
- **Certificates.** For ζ's datum (Γ_ℝ, pole, conductor 1):
  - double-precision SDP duals, rounded to rational PSD matrices `X = Σ w v vᵀ`;
  - near-null eigenvectors of `Q_Λ`.
- **Rigorous evaluation (Arb, 256 bits).**
  - `q(X) = tr(Q_Λ X)` and `m_n(X) = tr((2/√n) S_n X)`.
  - Spline Gram and sampling matrices from exact B8 piece polynomials.
  - Pole term from closed forms.
  - Archimedean term via `−γ g(0) + 2∫_0^∞ [g(0)e^{−2x} − e^{−x/2}g(x)]/(1−e^{−2x}) dx`, using `acb.integral` piecewise, a bounded head on `[0, 1e-30·hk]` and a closed-form tail.
- **Elimination.** Each producer inequality reads `Σ δ_n m_n ≤ q`. Rational LP multipliers combine them, then a rigorous bootstrap (`M ≤ max|Q|/(|C| − E)`) and per-coordinate refinement bound each `δ_n`.

## Results (certified boxes for δ_n = λ(n) − Λ(n))

| support `[−L/2, L/2]` | n = 2 | n = 3 | n = 4 | n = 5 | n = 6 |
|---|---|---|---|---|---|
| `L = 13/10` | [−5.08e-6, 7.52e-8] | [−5.52e-4, 5.95e-3] | | | |
| `L = 8/5` | [−6.20e-9, 3.13e-9] | [−5.57e-7, 3.75e-7] | [−1.58e-4, 2.96e-4] | | |
| `L = 9/5` | [−1.06e-8, 8.6e-10] | [−5.8e-8, 3.5e-7] | [−2.9e-5, 1.0e-5] | [−0.011, 0.016] | |
| `L = 2` | [−2.43e-9, 4.20e-10] | [−1.28e-8, 3.79e-8] | [−8.6e-7, 3.4e-7] | [−1.16e-5, 3.08e-5] | [−4.21e-3, 1.27e-3] |

## Interpretation
- These are the first rigorous non-perturbative pinning results: any Weil-positive integer weight system equals the von Mangoldt function at 2, 3, 4, 5 to high precision, and vanishes at the composite 6 to 4e-3.
- The theorem's hypothesis implies the corpus's `WeilPositiveFull` inequalities on these tests (conventions audited).
- Consequence: any real-rooted twin `F ∈ V_k` has `Λ_F(n)/k` pinned the same way. Deviations from ζᵏ must hide at large n with infinite mass.
