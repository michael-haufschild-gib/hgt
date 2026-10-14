# JAS producer conjectures: sweep and kills

Target producer: level-one constant-vector positivity on the full dyadic intervals `(2^m, 2^{m+1}]`,
together with chain exclusion. On the prime side the dyadic test is `E[K(S)]`, where:

- `S = Σ_p ε_p log p` is a symmetric random walk on the logs of the primes in the dyadic range, with
  `P(ε_p = ±1) ≈ r/p`;
- `K` is the lag function `≈ −(ψ_smoothed(e^L) − e^L)/e^{L/2}`.

At first order positivity reads `|Σ_{y<p≤2y} K(log p)/p| ≲ W/(2r)`: a smoothed `√x`-precision prime
count averaged over a dyadic range. The `k`-th order terms test `K(k log y)` with tolerance
`(log y)^k/k!`.

Kill standard: a wall from the corpus catalogue, or one of the named countermodels:

- `ζ(s−a)ζ(s+a)`: Euler product, functional equation, `Λ_a ≥ 0`, non-tempered;
- Davenport–Heilbronn: functional equation, no Euler product;
- Beurling systems: Euler product, no functional equation.

| # | Conjecture | Verdict | Lesson |
|---|---|---|---|
| S1 | A prime-side sum-of-squares identity from `Λ ≥ 0`, Euler product and functional equation | FALSE (`ζ(s−a)ζ(s+a)`) | The producer must use coefficient size (temperedness). |
| S2 | Bounded coefficients `0 ≤ a_n ≤ 1`, Euler product and FE suffice | CIRCULAR | By the degree-one classification this class is ζ and Dirichlet L, so the claim is GRH for them. |
| S3 | Positivity of the Riemann–Pólya kernel `Φ > 0` symmetrized under `s ↔ 1−s` | FALSE | Positive kernels have transforms with complex zeros. What is needed is the Laguerre–Pólya class: all Jensen polynomials hyperbolic, known only asymptotically. |
| S4 | Level descent `σ → σ − ε` through products of tests on disjoint prime sets | FALSE | For `ζ(s−a)ζ(s+a)` its own tests stop at level `1 + a`; descent cannot self-improve a zero-free region. |
| S5 | Constant vectors from typical-phase positivity by concentration on the prime torus | REDISCOVERED/FALSE | The exceptional set sits exactly at the constant vectors (resonance with the pole). |
| S6 | Heat flow `t ↓ 0`: finitely many non-real zeros of `H_t` plus continuity | CIRCULAR | `H_t` has no Euler product; `Λ ≤ 0` is RH. |
| S7 | Pole repulsion amplified by large prime products is height-uniform | FALSE | The coupling of dyadic sums to height `γ` decays like `1/γ`; the budget law gives `(log y)^{3/2}`, i.e. VK. |
| S8 | Each prime sees itself (self term `Λ(p)k(0)`) and this dominates | INSIGNIFICANT | Self terms are `O(Σ log p/p^{3/2})`. |
| S9 | One off-line zero forces many (local propagation by FE and Jensen) | FALSE | Davenport–Heilbronn has isolated off-line zeros. |
| S10 | Mix: GORZ asymptotic Jensen hyperbolicity (archimedean) with JAS (large primes) | BRIDGE | GORZ comes from the `n = 1` theta term; the arithmetic sits in the small shifts and the middle supports, where neither side dominates. |
| S11 | Zero-density estimates exclude thin-excursion chains for ζ | FALSE (cost unchanged) | See below. |

**S11 in detail.** `N(½+δ, T) ≪ T^{A(1−σ)} log^B T` forces a Fejér block of `e^F` off-line zeros in
arithmetic progression to have spacing `ω ≥ e^{cF}`, with `c = 1/(A(1−σ)) − 1 > 0`. The handover cost
stays of order `f` per geometric step. Density-zero chains with slowly growing `F` therefore remain
consistent with zero-density. So zero-density cannot remove the no-chain hypothesis from the
density-zero law.

**Reading.** Every producer mechanism that uses only the Euler product, the functional equation and
positivity dies at one of the three countermodels. What is left must use all three structures together:

- temperedness (`|a_n| ≤ d(n)`);
- the functional equation globally, not only through convexity;
- the Euler product.

The JAS producer is exactly the zero-free region problem: budget `B ⟺` width (budget law). No JAS-internal
slack exists.

NO POSITIVE SALVAGE FOUND beyond the dictionary in the first paragraph, which is in the corpus as the
budget law and the explicit-formula form of the dyadic test.
