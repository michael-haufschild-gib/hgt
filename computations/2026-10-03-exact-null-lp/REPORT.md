# Exact-null selective LP (2026-10-03)

## What was computed
- Tests `g` with `ĝ = Ξ(t)²·ĥ(t)`, where `ĥ = Σ ν_j φ_j ≥ 0` (Gaussian bumps, width σ, centres on a grid in [0, TMAX]).
- `Q_Λ(g) = 0` **unconditionally**, since `ĝ` vanishes at every ζ-zero. So for every full-cone Weil-positive `lam`: `Σ_m δ(m) m^{−½} I(m) ≥ 0`, with `I(m) = ∫ĝ cos(t log m)` and `δ = Λ − lam`.
- **LP (`enlp2.py`, HiGHS).** For `n0 = 2, 3` and sign ±: minimize `Σ_{m≠n0, m≤3000} m^{β−½}|I(m)|` subject to `I(n0) = ±1`, `ν ≥ 0`.
  - This yields `∓δ(n0) ≤ √n0·OPT·sup_m |δ(m)|/m^β`, given an a priori bound `|δ(m)| ≤ m^β`.

## Results (n0 = 2, TMAX = 100, Δ = 0.5, σ = 1)
| β | bound from I(2) = +1 (δ(2) ≥ −…) | bound from I(2) = −1 (δ(2) ≤ …) |
|---|---|---|
| 0.5 | 5.4e-5 | 0.72 |
| 0.75 | 2.1e-4 | 1.19 |
| 1.0 | 7.8e-4 (TMAX 60: 2.0e-3) | 2.07 |
| 1.25 | 2.8e-3 | 3.9 |

n0 = 3, β = 1: 0.10 / 6.1.

## Interpretation
- **One-sided.** The `+1` side shrinks with resources. The `−1` side is stuck at a level set by the a priori tail bound.
- **The blind direction.**
  - Exact-null tests see only `Ξ²μ_lam ≥ 0`, i.e. the spectral measure **off** the zeros.
  - Deficits placed **at** ζ-zeros (evaporation, `δ(n) > 0` directions) are invisible.
  - So exact-null certificates give `lam(n) ≤ Λ(n) + ε` (majorant side). The minorant/evaporation side needs tests with `Q_Λ > 0`, i.e. MUST-718-type first-order mixing.
- **Twins.** A ℤ/3 twin is total evaporation of ζ's spectrum plus redeposition at F's zeros (mass 1/3). The exact-null cone sees only the (positive) redeposition, so it cannot exclude twins by itself.

## Stiemke test (S41): fully supported prime-blind exact-null tests (`stiemke.py`)
LP: `ν ≥ τ`, `Σν = 1`, `I(m) = 0` for 2 ≤ m ≤ MMAX; maximize τ. Bumps cover t ≤ 100.
- MMAX = 30: τ·n_v = 0.0045 (interior exists, residual 2e-14).
- MMAX = 60: τ·n_v = 3e-5.
- MMAX = 150: **infeasible**.

**Reading: a truncation artifact.** On a finite t-window, a cosine polynomial with frequencies log m (m ≤ M) can be positive on all of [0, TMAX] despite zero mean (it is negative only beyond TMAX), giving a Gordan separator. A faithful test needs TMAX ≳ the Kronecker recurrence time of {log p}, i.e. exponential in M. This is the corpus wall L319 ("recurrence needs Kronecker heights ≫ e^{2U}"). The S41 route is computationally inaccessible and reduces to L318/L319.

## S45: majorant certificates (I(n0) = +1 only), a priori |δ(m)| ≤ m^{1.5}
Bound on `lam(n0) − Λ(n0)` for every producer (TMAX 60 / 100 / 160 / 200):

| n0 | bound |
|---|---|
| 2 | 0.032, 0.0103, 0.0093, 0.0089 (plateau) |
| 3 | 1.27, 1.05, 1.50 |
| 4 | ~10 |
| 5 | ~7 |
| 7 | 15–19 |

**Verdict: plateau, as predicted.** Exact-null tests cannot certify `lam ≤ Λ` without strong a priori tail control. Majorant-violating Ξ²-positive pseudo-producers exist in the truncated problem: they exploit tail coordinates, consistent with W₃ rosette directions (`Ξ²δ''_γ = 2Ξ'(γ)²δ_γ`). The reduction "majorant certificates + Lean minorant rigidity ⇒ C-PIN" is therefore blocked at the majorant step.
