# The Li ladder as comb forms of the Laguerre tails themselves

- **ID:** agz-raw-laguerre-tails (task A82 of `docs/reports/review-1011/obstacles-summary.md`, question 5 of §2.14)
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** obstacles-summary §2.14 question 5; §2.1 A82
- **Statement:** for every `n`, with `P_n(x) = Σ_{k<n} C(n,k+1)(−x)^k/k!` and the tail
  `c_m = P_n(log(N/m))`, `1 ≤ m ≤ N`: `𝔚_{[1,N]}(c)/N → Re 2λ_n` (`xiLiPaired n`). No damping, no
  smoothing, no second limit. More generally, for the log-power tails `ℓ^k_N(m) = log^k(N/m)`,
  `𝔚_{[1,N]}(ℓ^k, ℓ^l)/N → k! l! Re Σ_ρ ρ^{−k−1}(1−ρ)^{−l−1}`.

## Gates
- [x] T1 scaling recursion (exact) and the Cesàro step
- [x] T2 base case, prime part (hyperbola method, prime number theorem with error)
- [x] T3 base case, archimedean part
- [x] T4 the moments of the row are sums over the zeros (Mellin transform, Hadamard)
- [x] T5 assembly
- [ ] Lean

## Paper proof

Notation: `B_N(c, e)` Weil's bilinear form on the comb `[1, N]` (`formBilin`), `ℓ_N(m) = log(N/m)`,
`b_N(k, l) = B_N(ℓ_N^k, ℓ_N^l)`, `η_N = log(1 + 1/N)`; zeros `ρ` of `ξ` with multiplicity;
`V(k, l) = Σ_ρ ρ^{−k−1}(1−ρ)^{−l−1}` (absolutely convergent: `|ρ|, |1−ρ| ≥ |Im ρ| > 4`).

**T1. Scaling recursion.** `ℓ_{N+1} = ℓ_N + η_N` on `[1, N]` and `ℓ_{N+1}^k(N+1) = 0` for
`k ≥ 1`. A divisor vanishing at `N + 1` has the same form on `[1, N+1]` and `[1, N]`. Hence for
`k, l ≥ 1`, exactly,

`b_{N+1}(k, l) = Σ_{i ≤ k} Σ_{j ≤ l} C(k,i) C(l,j) η_N^{k−i+l−j} b_N(i, j)`.

*Cesàro step.* `N η_N → 1`, `η_N → 0`. If `b_N(i, j)/N → β(i, j)` for all `(i, j) ≠ (k, l)`,
`i ≤ k`, `j ≤ l`, then every term with `k − i + l − j ≥ 2` of
`b_{N+1}(k,l) − b_N(k,l)` tends to `0` and the two terms with `k − i + l − j = 1` tend to
`k β(k−1, l)` and `l β(k, l−1)`. By Cesàro, `b_N(k, l)/N → k β(k−1, l) + l β(k, l−1)`.
So all limits exist once the limits `β(0, j)` exist (`b` is symmetric), and
`β(k, l) = k β(k−1, l) + l β(k, l−1)` for `k, l ≥ 1`.

**Base case.** `b_N(0, j) = Σ_{n ≤ N} log^j(N/n) R_N(n)` with the row of the flat tail
`R_N(n) = (N/n − ψ(N/n)) + (H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π)`
(`formBilin_flatTail`). For `j = 0` the limit is `2 + γ − log 4π = V(0, 0)` (flat tail; corpus).
Let `j ≥ 1`.

**T2. Prime part.** `r(x) = x − ψ(x)`. The prime number theorem with error `x e^{−c√log x}` and
Chebyshev's bound give `C_j` with `|r(x)| log^j x (1 + log x)² ≤ C_j x` for `x ≥ 1`.
Claim: `(1/N) Σ_{n ≤ N} log^j(N/n) r(N/n) → κ_j := ∫_0^1 log^j(1/t)(1/t − ψ(1/t)) dt`.
Fix `K ≥ 2`, `N ≥ 2K`, `m₀ = ⌊N/K⌋`.
- `n ≤ m₀`: the term is at most `C_j /(n (1 + log(N/n))²)`. With `φ(n) = 1/(1 + log(N/n))`,
  `φ(n+1) − φ(n) ≥ log(1 + 1/n)/(1 + log(N/n))² ≥ 1/(2n(1 + log(N/n))²)`; telescoping,
  the part is at most `2 C_j φ(m₀ + 1) ≤ 2 C_j/(1 + log(K/2))`.
- `m₀ < n ≤ N`: `N/n < K`, `ψ(N/n) = Σ_{k ≤ K} Λ(k) 1[n ≤ N/k]`, so the part is
  `Σ_{m₀<n≤N} log^j(N/n)/n − Σ_{k ≤ K} Λ(k) (1/N) Σ_{m₀ < n ≤ ⌊N/k⌋} log^j(N/n)`.
  The functions `t ↦ log^j(1/t)/t` and `t ↦ log^j(1/t)` are antitone on `(0, 1]`; comparing sums
  and integrals on `[m₀/N, ⌊N/k⌋/N]`, whose endpoints are within `1/N` of `1/K`, `1/k`, the part
  tends to `∫_{1/K}^1 log^j(1/t)(1/t − ψ(1/t)) dt`.
- The integrand of `κ_j` is at most `C_j/(t (1 + log(1/t))²)`, integrable; so
  `∫_0^{1/K} → 0` as `K → ∞`.

**T3. Archimedean part.** `log M + γ ≤ H_M ≤ log M + γ + 1/M` (`M ≥ 1`). For `1 ≤ n < N`:
`|H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π − a(n/N)| ≤ 1/(N−n) + 1/n`,
`a(t) = −½ log(1 − t²) − log 2π`. With `log(N/n) ≤ (N−n)/n` the error sums to
`O(log^j N (1 + log N))`, which is `o(N)`. The function `log^j(1/t) log(1 − t²)` is bounded and
continuous on `(0, 1]` (`j ≥ 1`), `log^j(1/t)` is antitone and integrable. Riemann sums:
`(1/N) Σ_{n ≤ N} log^j(N/n)(H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π) → σ_j := ∫_0^1 log^j(1/t) a(t) dt`.

So `β(0, j) = μ_j := κ_j + σ_j = ∫_0^1 log^j(1/t) ϱ(t) dt`, `ϱ(t) = 1/t − ψ(1/t) + a(t)`.

**T4. The moments are sums over the zeros.** For real `s > 1`:
- `∫_0^1 t^{s−1} ψ(1/t) dt = Σ_k Λ(k) ∫_0^{1/k} t^{s−1} dt = −ζ′(s)/(s ζ(s))`;
  `∫_0^1 t^{s−1} t^{−1} dt = 1/(s−1)`;
- `∫_0^1 t^{s−1}(−log(1−t²)) dt = Σ_{k≥1} 1/(k(s+2k)) = (ψ_Γ(s/2+1) + γ)/s` (digamma series);
- so `M(s) := ∫_0^1 t^{s−1} ϱ(t) dt = 1/(s−1) + ζ′/(sζ)(s) + (ψ_Γ(s/2+1) + γ)/(2s) − log 2π/s`.
- `ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ_Γ(s/2) + ζ′/ζ(s)`, `ψ_Γ(z+1) = ψ_Γ(z) + 1/z`,
  `ξ′/ξ(0) = −(1 + γ/2 − ½ log 4π)`: `s M(s) = ξ′/ξ(s) − ξ′/ξ(0)`.
- Hadamard: `ξ′/ξ(s) − ξ′/ξ(0) = Σ_ρ (1/ρ − 1/(ρ − s)) = Σ_ρ s/(ρ(s − ρ))`.
Hence `M(1 + ε) = Z(ε) := Σ_ρ 1/(ρ(1 + ε − ρ))` for `ε > 0`.

*Moments.* Claim `μ_j = j! V(0, j)`, by induction on `j`. With `L = log(1/t)`,
`t^ε = e^{−εL} = Σ_{i<j} (−εL)^i/i! + R_j(εL)`, `|R_j(y) − (−y)^j/j!| ≤ y^{j+1}/(j+1)!`,
`|R_j(y)| ≤ y^j/j!` (`y ≥ 0`). Since `|ϱ| L^j` is integrable, dominated convergence gives
`(M(1+ε) − Σ_{i<j} (−ε)^i μ_i/i!)/ε^j → (−1)^j μ_j/j!` as `ε ↓ 0`. On the other side
`1/(1+ε−ρ) = Σ_{i<j} (−ε)^i/(1−ρ)^{i+1} + (−ε)^j/((1−ρ)^j (1+ε−ρ))`, so
`(Z(ε) − Σ_{i<j} (−ε)^i V(0,i))/ε^j = (−1)^j Σ_ρ 1/(ρ(1−ρ)^j(1+ε−ρ)) → (−1)^j V(0, j)`
(dominated by `1/(Im ρ)²`). The two quotients agree for every `ε > 0` by the induction
hypothesis. (`μ_j` is real, so `V(0, j)` is.)

**T5. Assembly.** `1 = ρ + (1 − ρ)` gives `V(k, l) = V(k−1, l) + V(k, l−1)` (`k, l ≥ 1`); the
zeros are symmetric under `ρ ↦ 1 − ρ`, so `V(k, l) = V(l, k)`. Therefore
`β(k, l) = k! l! Re V(k, l)` satisfies the recursion and the base cases of T1:
`b_N(k, l)/N → k! l! Re V(k, l)`.
With `a_k = C(n, k+1)(−1)^k/k!`: `Σ_{k<n} a_k k! z^{−k−1} = 1 − (1 − 1/z)^n`, and with
`w = 1 − 1/ρ`, `1 − 1/(1−ρ) = w^{−1}`. Hence
`𝔚_{[1,N]}(P_n(ℓ_N))/N = Σ_{k,l<n} a_k a_l b_N(k,l)/N → Re Σ_ρ (1 − w^n)(1 − w^{−n}) = Re Σ_ρ (2 − w^n − w^{−n}) = Re 2λ_n`.

## Lean
Not started.

## Open
- The same limit for `m^ε`-damped tails with `Re ε < 0` is equivalent to a zero-free strip; the
  statement at `ε = 0` is of the strength of the prime number theorem with a error term beating
  every power of the logarithm.

## Log
- 2026-11-11 — paper proof.
