# Local real-rooted twins at conductor N: degree 3 (S42) and degree 2 (S43), 2026-10-03

## What was computed
- AFE null space for `W_d(N)` (entire part, `Γ_ℝ(s)^d`, conductor N), certified visible directions as in `2026-10-03-twin-gram-lp`.
- Base point `F₀ = ζ^d·B_N`, with `B_N = 1 + N^{½−s}` (root number +1). Its Z-function is `2cos(t log N/2)·Z_ζ^d`. It is an exact rational ℤ/d lock at conductor N.
- **S42 (d = 3, `s42.py`).** Gram-law L1-LP for `F₀ + E`, `E ∈ W₃(N)`, N = 1…300, T = 50.
- **S43 (d = 2, `s43.py`).** Sign-pattern margin LP. Require every double zero of `F₀` at a ζ-zero to split into two real zeros: `sign Z_F(γ) = −sign cos(γ log N/2)`, and keep the base sign elsewhere. Then count sign changes and per-zero splits.

## Results
- **S42 (degree 3, Gram objective).** The LP never increases real zeros beyond the base, for N = 1, 10, 30, 100, 300 (even where the visible freedom of 31 directions exceeds the ~20-zero deficit). Gram's law is the wrong objective for split triple zeros, so this is weak evidence.
- **S43 (degree 2), split ζ-zeros / total:**

| N | T = 40 | 60 | 80 | 120 | kvis (T = 40 → 120) |
|---|---|---|---|---|---|
| 1 | fails | – | fails | – | 4–5 |
| 8 | 6/6 | 10/13 | 10/21 | 17/38 | 5 → 12 |
| 12 | 6/6 | 12/13 | 5/21 | 15/38 | 7 → 17 |
| 20 | 6/6 | 11/13 | 10/21 | 11/38 | 7 → 23 |
| 50 | 5/6 | 11/13 | 17/21 | 24/38 | 10 → 33 |

  At N = 20, T = 40 the result is fully real-rooted: 31 sign changes = needed, positive margin, |g_n| ≤ 10·d(n). At N = 50 some failures come from lattice zeros of B_N near ζ-zeros (an ill-posed local target).

## Interpretation
- **Horizon law.** Local real-rooted degree-2 Dirichlet series of conductor N > 4 with no arithmetic origin exist up to a height T*(N), where the ζ-zeros to split outnumber the visible freedom of W₂(N) (~1–1.4 zeros per direction). T*(N) grows with N (~40–60 for N = 8–20, ≳80 for N = 50). N = 1: T* = 0 (Kaczorowski–Perelli).
- At fixed N the freedom grows like T·log(N/4) against zeros like T log T, so the horizon is finite and no global twin arises perturbatively. Consistent with "real zeros ⇒ arithmetic".
- **Degree 3, conductor 1 (C329).** The freedom is exactly one direction per ζ-zero (window count = zero count). Splitting a triple zero needs a near-equality (`E(γ) ≈ 0`) plus a sign condition per zero. The freedom deficit is structural at every height, so perturbative twins die (the rosette, now as a count). Twins must be non-perturbative.

## S44: non-perturbative zero-completion search (`s44.py`), inconclusive by method
From random far starts in `a·ζ²B_N + W₂(N)` (N = 1, 20, 50; T = 120), iterated LPs flip the deepest missing-zero dips while freezing the other sampled signs. The search stalls after 1–5 steps with real-rootedness heights T_RR ≈ 9–23, far below the perturbative horizon (~60 at N = 20). The rigid LP step is too weak, so nothing is learned about non-arithmetic real-rootedness beyond the count horizon.

## S46: local trigonal handles (degree 3, `s46.py`)
Split each triple zero of `ζ³B_N` at a ζ-zero into three real zeros: signs (s, −s, s, −s) at γ ± {0.5, 1.5}η, base sign elsewhere, |e_n| ≤ 1000·d₃(n).

| N | T = 30 | 50 | 80 | 120 | (η = 0.2; split/zeros) |
|---|---|---|---|---|---|
| 1 | 0/3 | 0/9 | 0/21 | | |
| 3 | 0/2 | 0/8 | 0/19 | | |
| 6 | 0/3 | 1/8 | 2/17 | | |
| 12 | 2/2 (margin −0.005) | 1/8 | 0/14 | 0/26 | |
| 25 | 3/3 (margin +0.06) | 0/7 | 2/12 | 0/20 | |

- Wider windows (η = 0.4, 0.6) do not help, so the obstruction is not resolution.
- **Cost law.** A trigonal handle costs ≈ 2.5–3 visible W₃(N) directions (value plus derivative conditions plus staying small in the cubically flat neighbourhood). A hyperelliptic handle (degree 2, S43) costs ≈ 1.
- Visible directions per ζ-zero at T = 80: 0.38 (N = 1), 1.2 (6), 1.7 (12), 2.5 (25), i.e. ≈ 1 + log N/log(t/2π) after onset.
- **Trigonal horizon** `T*₃(N) ≈ 2πN^{1/2…2/3}` (≈ 30–50 at N = 25), not the predicted 2πN.
- Conductor 1: no local trigonal handle at any height. This is the count form of the rosette exclusion.
