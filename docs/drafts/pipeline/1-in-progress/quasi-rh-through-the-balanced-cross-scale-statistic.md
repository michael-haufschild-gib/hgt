# Quasi-RH through the balanced cross-scale statistic (opening A, continued)

- **ID:** fable-2410-A-quasiRH
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (target `Θ < 1`)
- **Source:** docs/reports/review-2410/fable.md §2.3 A, §2.5 · BVI README §3.13, §7.4 · card
  `3-formalized/kloosterman-reciprocity-balanced-cross-scale-gram-2026-10-24.md`
- **Statement:** a power saving for `Λ_d(μ𝟙_{(Q,2Q]})` on the diagonal band `Q ≍ d`, hence `Θ < 1`.

## Goal
Deliver quasi-RH from opening A. Below the diagonal the power saving is proved at every modulus
(six BVI modules). On the band the statistic is a functional of long-window Möbius sums.

## Notation
`Φ_d(m) = (d²/2)B₂({m/d}) − 1/12`, `𝔅(d,n) = Σ_j Φ_d(jn)/j²`, `Ψ_d` cubic potential,
`𝔅₃(d,n) = Σ_j (2Ψ_d − Φ_d)(jn)/j³`, `ℓ_d(n) = (𝔅(d,n) − m_d)/n² + 𝔅₃(d,n)/n³`,
`Λ_d(c') = Σ_n c'(n) ℓ_d(n)`, `f(x) = Σ_j B₂({jx})/j²` (1-periodic).

## Conjecture ledger
| # | Conjecture | Status | Lesson |
|---|---|---|---|
| C1 | `Σ_n μ(n) ℓ_d(n) = 2Ψ_d(1) − (6/π²) m_d` at every `d` | PROVED, Lean `hasSum_moebius_mul_kernelTerm` | both kernels are sums over multiples; `μ ⋆ 1 = δ`; window statistics telescope to an explicit value |
| C2 | `f(x) = ζ(2)/6 − x log(1/x) + b x + O(x²)`, uniformly in the arithmetic of `x` | numerically true (`b ≈ 0.2606`) | the fractal part of `f` is `O(x²)` near `0`; superseded by the cruder C3a |
| C3a | `|n² ℓ_d(n) − (ζ(2)/4) d²| ≤ C d n log 2d` for `n ≤ d` | paper proof (split `j < d/n`) | elementary; enough for C3 |
| C3 | band power saving (`Q^{1−ε} ≤ d ≤ Q^{1+ε}`) ⟺ `Θ < 1` | paper proof | `⇒`: C1 + C3a give `Σ_{n>X} μ(n) ℓ_d(n) = (ζ(2)/4) d² T₂(X) + O(d log² d)` for `d ≥ X`; band + below-diagonal theorem bound it; `d = X^{1+κ}` gives `T₂(X) ≪ X^{−1−κ}`, Abel gives `M ≪ X^{1−κ}`. `⇐`: archimedean law + Littlewood |
| C4 | multiplicative bootstrap `S(Q) ≤ C S(√Q)² + Q^{−δ}` via Type II factorization of the archimedean kernel | FAILED | Type I terms and the hyperbola bring back `Σ_{c ≤ Q/b} μ(c)/c` at full scale `Q`; `1/ζ` has no factorization through `1/ζ` at smaller scales without `ζ` |
| C5 | Gram positivity bounds the band: `|Λ_d|/d ≤ √(G(d,d) E(u_Q))` | FAILED | `E(u_Q) ≥ (M(2Q) − M(Q))²/Q`: positivity gives floors, the bound is trivial |
| C6 | reciprocity `f(x) ↔ f(1/x)` moves the band to a smaller scale | FAILED | at `x ≍ 1`, `{1/x}` is not small: reciprocity maps the band to itself |
| C7 | smoothed rows give sieve weights: `Λ_d(μφ_Q) = Σ_N Φ_d(N) λ_Q(N)/N²`, `λ_Q(N) = Σ_{n∣N} μ(n) φ(n/Q)` | identity (true) | the band is the distribution of truncated Möbius divisor sums mod `d ≍ Q`: level of distribution 1, single modulus |
| C8 | Liouville row: `Σ λ(n) 𝔅(d,n)/n² = Σ_m Φ_d(m²)/m⁴` (quadratic residues mod `d`) | identity (true) | explicit with Gauss-sum structure; band ⟺ `ζ(2s)/ζ(s)`, same wall |

## Log
- 2026-10-24 — created; loop started.
