# The finite Weil-positivity margin: least eigenvalue of the arithmetic Gram matrices

Script `gram_margin.py` (runpod, ~40 s). Builds `G_N[n,m] = Φ(log(n/m))`, `1 ≤ n,m ≤ N`, from the prime side of the lag
function at the rational point `X = n/m` (Lean `weilLagFunctionReal_eq_prime_side`, `lagGramKernel`), with the trivial-zero
series in closed form `S(X) = 1 − ½log(1 − X⁻²) − X·artanh(1/X)` (a 40-term truncation of `S` is wrong near `X = 1` and
produced spurious negative eigenvalues in a first run — do not truncate `S`). Also the Toeplitz forms of the two-prime lattice
`Φ(k log 2 + l log 3)`, `|k|,|l| ≤ K`. Output `gram_margin.json`. RH ⟺ all `G_N ⪰ 0` (Lean
`riemannHypothesis_iff_arithmeticGramForm_nonneg`); numerically all are PSD.

| N | λ_min | λ_min·N | λ_2 | λ_max | λ_max/N |
|---|---|---|---|---|---|
| 50 | 1.674e-3 | 0.0837 | 4.27e-3 | 0.301 | 0.0060 |
| 100 | 8.51e-4 | 0.0851 | 2.19e-3 | 0.541 | 0.0054 |
| 200 | 4.32e-4 | 0.0863 | 1.12e-3 | 1.048 | 0.0052 |
| 400 | 2.18e-4 | 0.0872 | 5.66e-4 | 2.123 | 0.0053 |
| 800 | 1.10e-4 | 0.0879 | 2.86e-4 | 4.261 | 0.0053 |
| 1600 | 5.53e-5 | 0.0884 | 1.44e-4 | 8.515 | 0.0053 |
| 3200 | 2.78e-5 | 0.0889 | 7.26e-5 | 17.008 | 0.0053 |

Two-prime lattice: `K = 2,3,4,5` (dim 25, 49, 81, 121): `λ_min = 2.84e-3, 1.67e-3, 9.75e-4, 6.52e-4` (≈ `0.07/dim`), all PSD.

**Laws read off.** (1) `λ_min(G_N) ≍ 1/N`: `λ_min·N` increases slowly from 0.084 to 0.089 (limit ≈ 0.09–0.10). This is the
finite-scale margin of Weil positivity on the divisor group: relative to the trace `N·a_1` it is `≈ 1.9/N²`. (2) The top
eigenvalues are `w_ρ·N` for the leading zeros: `λ_max/N → 0.0053 ≈ 1/(¼ + γ₁²) = 1/199.9` (first zero, the pair `±γ₁` gives
two such eigenvalues since the vectors `n^{±iγ₁}` are nearly orthogonal). (3) An elementary Rayleigh quotient with
`c = (e_N − e_{N−1})/√2` gives `λ_min ≤ a_1 − Φ(log(N/(N−1))) ≈ (log N)/(2πN)` from the cusp `Φ(L) ≈ a_1 − (L/2π)log(1/L)`;
the true margin is smaller by the factor `log N/(2π·0.09)`, so several nearby rows combine to remove the logarithm.

**Consequences.** A geometric producer of positivity must deliver, on the span of the Frobenius vectors `v_1,…,v_N`, a form
with least eigenvalue of order `0.09/N` — not merely nonnegativity. An off-line zero of height `T` perturbs `G_N` by at most
`N²·Σ_{|γ|>T} |w_ρ| ≈ N²·log T/(πT)`, so it is invisible to `G_N` until `N ≳ (0.09 T/log T)^{1/2}`; the numerical PSD-ness
up to `N = 3200` is consistent with, and no stronger than, the verified zero-free height. Conjecture (open, exact,
falsifiable): `λ_min(G_N)·N → c* ∈ (0.09, 0.11)`. No proof uses any of these numbers.
