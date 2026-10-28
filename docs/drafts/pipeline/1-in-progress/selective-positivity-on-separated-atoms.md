# Selective positivity of Weil's form on separated atomic families

- **ID:** selective-positivity-on-separated-atoms
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (numerical evidence; partial Lean)
- **Source:** Q1(ii)–(iii), B3.16, B3.26; SSHA topic 1; RAPT `ThePoleIsTheTopOfThePrimeForm`,
  `TheValuationTowerIsExactlySolvable`.
- **Statement:** For a fixed real C² bump `g` supported in `[0, w]`, `w = c δ_N`, Weil's form of `ζ` is
  positive on every atomic test `f_x = Σ_{n ≤ N} x_n g(· − log n)` for all `c < c_ζ(g)` with `c_ζ(g)`
  close to `1` (the whole separated regime), uniformly in `N`; the Liouville twin fails for
  `c > c_univ(g) ≈ e^{κ₀(g) + γ}`, `c_univ < c_ζ`.

## Mechanism

On separated atoms `Re W(f_x)/‖g‖² = (log(1/(wN)) + κ₀(g))|x|² − cross(x) − P_N(x) + 2f̂(0)f̂(1)/‖g‖²`,
`κ₀(g) = 2θ′(0) + 2c₁ + ∫_0^1 (1 − Ĝ₁(y)) dy/y`, `c₁ = ∫_0^1(ω − 1/(2x)) + ∫_1^∞ ω`.
The prime form has top `log N − γ` on the pole `n^{−1/2}` (Lean) and, numerically, next eigenvalue
`log N − γ − 2log 2` (the first 2-adic valuation step; Lean on class spans). The pole term
`2f̂(0)f̂(1)` contains `ℓ(x) = Σ x_n n^{−1/2}` and pays exactly the pole direction — only in the Euler
gauge: a twin's top eigenvector is `D_ω n^{−1/2}`, with `ℓ ≈ Σ ω(n)/n` small for Liouville.

## Numerics (scratch, point-mass cross kernel, `g₁ = sin²(πu)`, `κ₀ ≈ −1.16`)

| c | ζ min eig | Liouville min eig |
|---|---|---|
| 0.3 | 0.80 | 0.59 |
| 0.5 | 0.43 | 0.08 |
| 0.6 | 0.32 | −0.10 |
| 0.8 | 0.17 | −0.39 |
| 0.99 | 0.09 | −0.60 |

Same to 3 digits at N = 600 and 1500. The Markov form alone turns negative at `c ≈ 0.4`; on the
pole-orthogonal complement it stays ≥ 0.79 at `c = 0.9`.

## Gates

- [x] Top of the prime form sharp, all vectors (Lean, RAPT).
- [x] Hodge index with sharp gap on single-prime class spans (Lean, RAPT).
- [x] Global gap (C4), sharp: `P_N ≤ (log N − γ − 2 log 2 + ε)|x|²` on the pole complement,
      attained by the 2-adic step (Lean, RAPT RP37).
- [ ] Exact archimedean self-energy constant and cross kernel with tilted weights.
- [ ] Twin failure: needs cancellation in `Σ_m λ(m)λ(m+j)` (two-point Chowla type) for the Liouville
      pole; open.

## Findings on the global gap (C4)

- Top eigenvectors of `P_N` (N = 20000): overlap 0.997 of the 2nd with the 2-adic valuation step
  `n^{−1/2}(1_{2|n} − 1_{2∤n})`, 0.996 of the 3rd with the 3-adic step: the spectrum near the top is
  `log N − γ − (log m + τ(m))`, `τ` the tame different (matches the exact class-span theory).
- Peeling `p = 2` (odd-part Collatz–Wielandt + exact 2-ladder spectrum) gives
  `(log N − γ + ε) − P_N ⪰ ⊕_{2-ladders}(H_2 − γ)` globally, but the coupling between the 2-pole-like
  subspace and its complement has norm ≈ 2 (boundary residual of the pole), so the recursion over
  primes does not close by block estimates.
- Efron–Stein constant for `μ = 1/m` on `[1, N]`: 1.31, 1.29, 1.27, 1.26 (N = 60…1500); tilting the
  measure by `(1 + ηn/N)²` makes it worse (1.53 at η = 1).
- Schur complement across `[1, N/2] ⊕ (N/2, N]`: `M_N ⪰ (M_{N/2} + log 2 − BBᵀ/λ_N) ⊕ (paid)`,
  `BBᵀu ≈ log 2 · log N · u`; per-doubling errors are Mertens fluctuations at fixed `y = N/m`, not summable.
- Twin side: the Liouville pole's archimedean cross term is a `1/h`-weighted two-point correlation of
  `λ`; its smallness is averaged Chowla (Matomäki–Radziwiłł–Tao). Finite-flip twins: explicit.

## Status

No proof claimed.
