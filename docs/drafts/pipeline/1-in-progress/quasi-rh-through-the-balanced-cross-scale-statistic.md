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
| C3 | band power saving (`Q^{1−ε} ≤ d ≤ Q^{1+ε}`) ⟺ `Θ < 1` | PROVED, Lean `balancedStatisticPowerSaving_iff` | `⇒`: C1 + C3a give `Σ_{n>X} μ(n) ℓ_d(n) = (π²/24) d² T₂(X) + O(d log² d)` for every `d`; band + below-diagonal law bound it at `d = ⌊X^{1+e}⌋`; `T₂(X) ≪ X^{−1−κ}`, Abel `M ≪ X^{1−κ}`, absolute-moment law. `⇐`: archimedean law + Littlewood. Opening A has no rung below quasi-RH |
| C3′ | centred prime row: band power saving ⟺ `Θ < 1` | PROVED, Lean `centredPrimeBandPowerSaving_iff` | no inversion law (`Λ ⋆ 1 = log`); a chain of blocks `(X, 2^{⌊log₂ X^e⌋} X]` inside the band pins `Σ_{n>X} (Λ(n)−1)/n² ≪ X^{−1−κ}`; Abel, square-sample law. Both actual rows: the balanced first rung is exactly the strip |
| A1 | below-diagonal statistics (power-small, unconditional) combine to the band: `Σ_{d ≤ Q^{1−δ}} α_d ℓ_d ≈ 1/n²` on `(Q,2Q]` | FAILED | for `d ≪ n`, `ℓ_d(n)` is periodic mod `d` with zero residue mean; sums of such functions average to `0` on long intervals and cannot reproduce the window mean. The selective (minor-arc) input is blind to the long-window sum |
| A2 | above-diagonal moduli `d ≫ Q` bound the window | FAILED | there `Λ_d(u_Q) = (π²/24) d² Û_Q(2) + O(dQ log)`: they see the mean exactly but are not smaller than it |
| A3 | Liouville row: `λ ⋆ 1 = 𝟙_□` brings Gauss sums (Weil) into the full-row identity | FAILED | squares wrap mod `d` only for `m > √d`, weight `≤ d²/m⁴`: the Weil part is `O(√d)`, negligible against the band |
| A4 | the C1 family (any `Σ_j g(jn)` kernel) gives a power saving | FAILED | C1 is the `B₂` version of `Σ μ(n)⌊x/n⌋ = 1`; these identities give `|Σ μ(n)/n| ≤ 1`-type bounds, Class I, Beurling-universal |
| B1 | Gram positivity `E(c) ≥ 0` at rows resonating with a zero near `1` | FAILED | Plancherel: `E(c) = ∫|ζ(½+it) C(½+it)|²/(¼+t²) dt`, manifestly a square; holds for Beurling systems |
| B2 | iterate Kloosterman reciprocity along Euclid's algorithm on `(n, d)` | FAILED | for `n ≍ d` the first steps `d mod n = d − kn` are linear in `n`: archimedean; deeper steps decay geometrically |
| B3 | averaged Chowla `Σ_{0<|h|<H}(H−|h|) Σ μ(n)μ(n+h)` at `H = Q^α` with a power saving | ⟺ `Θ < 1` (paper) | the window energy is this weighted correlation sum plus `O(H³)`, and window saving ⟺ `Θ < 1` (`moebiusPowerWindowSaving_iff`); the Class III quantity carries exactly the strip |
| B4 | multiples of `p`: `Σ_{k≥1} M(x/p^k) = −M(x)/p + O(max_a |S(a/p)|)` constrains `M` | FAILED | minor-arc error `x^{1−η}` exceeds the trivial size `x/p` of the class-0 mass for every `p ≥ x^η`; the mean needs `p ≤ x^η`, where only Siegel–Walfisz holds |
| B5 | large sieve over all `a/q, q ≤ √x` | FAILED | sign-blind; the `q = 1` term alone is bounded only trivially |
| B6 | Halász / pretentious distance | FAILED | `D(μ, n^{it}; x)² ≤ 2 log log x`, so at most log-power savings |
| B7 | zero density / large values | FAILED | they bound how many zeros there are; one zero near `1` is not excluded |
| B8 | Vinogradov's mean value theorem (optimal, BDG/Wooley) | FAILED | gives the Vinogradov–Korobov region `1 − c(log t)^{−2/3}`, no strip |
| B9 | Bombieri–Vinogradov amplification | FAILED | `(log x)^{−A}` savings only, limited by Siegel zeros |
| B10 | hyperbolic decomposition `x S₁(x) = 1 + Σ μ(n){x/n}`, Type I/II savings for `μ(n)e(kx/n)` | localization (paper) | the middle range is power-small (selective, ℤ-specific); the end `n > x^{1−δ}` splits into short windows of relative length `1/k` at scales `x/k`: again `Θ < 1` |
| B11 | Beurling selectivity: `N(x) = cx + O(x^θ)` with `θ < 1/2` forces a strip | OPEN, at least as hard | zeros of `ζ_B` leave `N` unaffected (only poles of `ζ_B` drive `N`); ℤ has `θ = 0`, so this would imply quasi-RH; DMV constructions cover `θ > 1/2` only |
| B12 | successor `μ(n(n+1)) = μ(n)μ(n+1)` | FAILED | Chowla for `n(n+1)`, open; log-averaged versions are subpower |
| B13 | Deuring–Heilbronn repulsion | FAILED | a zero near `1` repels other zeros; it does not exclude itself |
| D1 | average the band over moduli `d ∈ [D, 2D]` (as a tool) | FAILED | averaging `f(n/d)` over `d` smooths the fractal part away and keeps exactly the window mean |
| D2 | sign structure: `f` has cusps `ζ(2)/6 − |t| log(1/|t|)` at integers, so `Λ_d` has a sign near `n ≈ kd` | FAILED | the weight is not sign-definite over the window; `μ` signs decide |
| D3 | quadratic dual norm `Σ_d Λ_d²/d` over the band | FAILED | bounded below by the squared window mean (attained dual norm); it is a floor |
| D4 | Hurwitz form `f(a/q) = q^{−2} Σ_r B₂({ra/q}) ζ(2, r/q)` exposes arithmetic of `d` | FAILED | reorders to the spectral law; same archimedean main part |

**Where the loop stands.** Every mechanism tested reduces to `Θ < 1` or fails one of the tests:
selective inputs (minor arcs, exponential sums at hyperbolic phases, Weil) act only on residue
fluctuations, which carry no information about the window mean; mean-reading inputs (C1-type
identities, positivity, Halász, density) are Beurling-universal or sign-blind. The one open
statement that would imply quasi-RH by a new route is B11 (regular Beurling counting below `√x`).
| C4 | multiplicative bootstrap `S(Q) ≤ C S(√Q)² + Q^{−δ}` via Type II factorization of the archimedean kernel | FAILED | Type I terms and the hyperbola bring back `Σ_{c ≤ Q/b} μ(c)/c` at full scale `Q`; `1/ζ` has no factorization through `1/ζ` at smaller scales without `ζ` |
| C5 | Gram positivity bounds the band: `|Λ_d|/d ≤ √(G(d,d) E(u_Q))` | FAILED | `E(u_Q) ≥ (M(2Q) − M(Q))²/Q`: positivity gives floors, the bound is trivial |
| C6 | reciprocity `f(x) ↔ f(1/x)` moves the band to a smaller scale | FAILED | at `x ≍ 1`, `{1/x}` is not small: reciprocity maps the band to itself |
| C7 | smoothed rows give sieve weights: `Λ_d(μφ_Q) = Σ_N Φ_d(N) λ_Q(N)/N²`, `λ_Q(N) = Σ_{n∣N} μ(n) φ(n/Q)` | identity (true) | the band is the distribution of truncated Möbius divisor sums mod `d ≍ Q`: level of distribution 1, single modulus |
| C8 | Liouville row: `Σ λ(n) 𝔅(d,n)/n² = Σ_m Φ_d(m²)/m⁴` (quadratic residues mod `d`) | identity (true) | explicit with Gauss-sum structure; band ⟺ `ζ(2s)/ζ(s)`, same wall |

## Log
- 2026-10-24 — created; loop started.
