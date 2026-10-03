# Prime-blind positivity thresholds of archimedean data (2026-10-03)

## What was computed
- Datum: `q^{s/2} Π_j Γ_ℝ(s+μ_j) L(s)` with pole order `m`.
- `κ*_L = max_λ min eig(Q_λ)`, G-normalized, at `q = 1`, with all integer weights `λ(n)`, `n ≤ e^L`, free.
- The conductor shifts `Q` by `log q·I`, so the threshold is `q*_L = exp(−κ*_L)`.
- Dual SDP: the extremal prime-blind certificate (PSD `X`, `tr(GX) = 1`, `g(log n) = 0`).
- Discrete Turán problem: `max ∫g` over the same cone.

## Results

| Datum | L = 0.5 | L = 1.0 | L = 1.5 | L = 2.0 | L ≥ 2.5 | smallest real conductor |
|---|---|---|---|---|---|---|
| Γ_ℝ(s), even, no pole | 1.97 | 3.78 | 4.011 | 4.035 | **4.03628** | 5 |
| Γ_ℝ(s+1), odd, no pole | 1.62 | 2.70 | 2.844 | 2.860 | **2.86055** | 3 |

- The plateau holds for `L = 2.5, …, 5` (up to `L = 4.5` for the odd datum).
- **ζ datum (Γ_ℝ, pole):** `κ*_L` falls 0.089 → 1.1e-4 → 0 (`L = 0.5, 1.0, ≥ 1.5`). The datum is critical: threshold = conductor 1.
  - The maximizing weights reproduce `Λ`: (0.6931, 1.0986, 0.6931, 1.6094, 0.0000, 1.9459).
- **Degree 2:**

  | Datum | q* | factorization |
  |---|---|---|
  | Γ_ℂ, pole | 2.86054 | = odd |
  | Γ_ℝ², simple pole | 4.03627 | = even |
  | Γ_ℝ², double pole | 1 | |
  | Γ_ℂ, no pole | 11.54595 | = even × odd |
  | Γ_ℝ², no pole | 16.29152 | = even² |

  Thresholds multiply over Γ_ℝ factors; pole factors are critical (contribute 1).
- **Real L-functions:** `L(s,χ₅)`, `L(s,χ₈)`, `L(s,χ₋₃)`, `L(s,χ₋₄)`, `ζ_{ℚ(√5)}` and `ζ_{ℚ(√−3)}` all have `min eig(Q) → 0⁺` (no slack) at their own weights. But at q = 5 other weights reach `min eig = 0.214`, so W is fat for non-critical data.
- **Extremal certificate g\*:**
  - The same function for even and odd data: g-samples agree to 3–4 digits, X-overlap 0.977. This explains the multiplicativity.
  - `∫g* = 0.693143` ≈ log 2.
  - Its spectrum vanishes at `r = 2πj/log 2`.
- **Discrete Turán:** `max ∫g` over PD `g` with `g(0) = 1`, `g(log n) = 0` equals `log 2` (7 digits). Proof: Poisson summation on the sublattice `log 2·ℤ ⊂ log ℕ`.

## Interpretation
- Prime-blind positivity does not detect arithmetic conductors. The thresholds 4.036 and 2.861 are set by the prime 2 (the `log 2·ℤ` lattice), and fake producers exist on `[4.036, 5)` and `[2.861, 3)`.
- The ζ datum is the only critical one among those tested: W is a point (`Λ`) and κ* → 0. RH ⟺ the pole datum's threshold is ≤ 1.
