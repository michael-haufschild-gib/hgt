# Fully prime-blind exact-null tests (C-PIN) at finite level: resolution, not Kronecker (2026-10-06)

## Question
- C-PIN means a positive `ĥ` with `ν = Ξ²ĥ` prime-blind, i.e. `ν̂(log m) = 0` for all `m ≥ 2`.
  - If it exists, every Weil-positive weight has its boundary measure carried by the critical zeros. Then it equals `Λ` (corpus `eq_vonMangoldt_of_boundaryMeasure_criticalZeros`), so U holds and RH ⟺ PBAP.
- Corpus S41 (2026-10-03) found the finite truncation infeasible at M = 150 (t ≤ 100, Gaussian bumps σ = 1). It attributed the failure to a wall: Kronecker recurrence heights exponential in M.
- Test: is the failure a wall or a resolution artifact?

## Setup (`cpin.py`, `cpin2.py`, `cpin3.py`; HiGHS LP)
- `ν = Z(t)²·ĥ(t)` on `[0, T]` (the positive Gamma factor is absorbed into `ĥ`).
- `ĥ = Σ ν_j φ_j`: Gaussian bumps of width σ (spacing σ/2), or cells of width 0.1 (σ = 0).
- Constraints: `ν_j ≥ τ`, `Σν_j = 1`, and `∫ν cos(t log m) = 0` for `2 ≤ m ≤ M` (rows normalized).
- Report `τ·n`: 1/n is uniform, a value `< 0` means no nonnegative solution exists.
- Tail pollution: `max_{M<m≤4M} |ν̂(log m)|/ν̂(0)`.

## Results
- **Positivity length.** Mean-zero cosine sums `Σ_{m=2}^M c_m cos(t log m)` with `C(0) = 1` and `|c_m| ≤ 10⁴` stay ≥ 0 on `[0, T]` only for `T ≤ T_max`:

  | M | 8 | 16 | 32 | 64 | 128 |
  |---|---|---|---|---|---|
  | T_max | 7.3 | 9.7 | 10.7 | 11.3 | 11.8 |

  Finite Gordan separators live on short windows (a rigorous Montgomery–Vaughan bound gives `T_max = O(M)`).
- **Smooth bumps, σ = 1** (the corpus resolution):
  - M = 30 is barely feasible (`τn ≈ 1e-3`).
  - M ≥ 60 is infeasible for every `T ≤ 4·2πM` (T up to 3016). M = 60 is marginally feasible at T = 1508 (2e-4).
- **Zero-resolving bumps** (σ ≤ 0.5, or cells): feasible with healthy margins.

  | M | T | σ | τn |
  |---|---|---|---|
  | 30 | 100 | cells | 0.146 |
  | 150 | 400 | 0.5 | 0.029 |
  | 150 | 400 | cells | 0.079 |
  | 300 | 400 | 0.5 | 0.0048 |
  | 120 | 754 | 0.5 | 0.025 |
  | 120 | 1508 | 0.5 | 0.029 |
  | 240 | 1508 | 0.5 | 0.019 |
  | 240 | 3016 | 0.5 | 0.019 |

  Margins decay slowly in M (no exponential collapse), and the head residual is below 1e-8.
- **Tails** stay unconstrained: `|ν̂(log m)|/ν̂(0)` for `M < m ≤ 4M` is about 0.006–0.16 at σ = 0.5, and 1e-4–1e-3 at σ = 1 (infeasible).

## Interpretation
- The S41 failure is a resolution artifact. Smooth ĥ cannot work: the twisted second moment `∫|ζ|²w m^{it}` has a main term `m^{−1/2}∫w(log(t/2πm)+2γ)` that cannot vanish for two values of m. A solution must adapt to `|ζ|²` at the zero-spacing scale (mollifier-like structure).
- At that resolution, finite-level C-PIN tests exist with margins that decay slowly in M. There is no Kronecker-height wall up to M = 240.
- Open core: the infinite problem, with all m and controlled tails. By duality it is equivalent to the absence of "positive-off-Z crystalline separators", i.e. Dirichlet series with spectrum in log ℕ_{≥2}, holomorphic on σ > ½, `Re ≥ 0` on the line off Z. These are a superset of the U-violators.
