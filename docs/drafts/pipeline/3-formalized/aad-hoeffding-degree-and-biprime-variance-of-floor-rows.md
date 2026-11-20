# Hoeffding degree truncation on smooth cosets and biprime ANOVA variance of floor rows

- **ID:** aad-hoeffding-degree-and-biprime-variance-of-floor-rows
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-1911/todo.md` #18 · `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/Spectrum/TheHoeffdingDegreeAndBiprimeVarianceOfAFloorRow.lean`
- **Statement:** Every letter `1 ≤ k < (Y + 1)^{d+1}` has at most `d` prime divisors `> Y`, making `saw q K` purely additive across primes `> Y` on each `Y`-smooth CRT coset when `K < (Y + 1)^2` and quadratic when `K < (Y + 1)^3`; on `ℤ/(pq)ℤ ≃ ℤ/pℤ × ℤ/qℤ` (`gcd(p,q)=1`), the centered normalized residue decomposes orthogonally into marginals of variance `(p^2-1)/(12 p^2 q^2)` and `(q^2-1)/(12 p^2 q^2)` plus a pure degree-2 interaction of variance `(p^2-1)(q^2-1)/(12 p^2 q^2)`.

## Goal
Isolate the exact combinatorial degree of sawtooth sums on smooth-frozen CRT cosets and prove the exact two-prime Hoeffding variance decomposition explaining why degree-1 marginal tests lose a factor `1/p^2 + 1/q^2` on composite letters `pq`.

## Gates
- [x] 0 → 1  in-progress: exact coset degree and biprime ANOVA formulas isolated
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `Spectrum/TheHoeffdingDegreeAndBiprimeVarianceOfAFloorRow.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Prime-divisor degree bound and exact coset additivity above `√K`.**
   - For `k ≥ 1`, if `(k.primeFactors.filter (Y < ·)).card ≥ d + 1`, choosing a subset `T` of cardinality `d + 1` gives `(Y + 1)^{d+1} ≤ ∏_{p ∈ T} p ≤ ∏_{p ∈ k.primeFactors} p ≤ k`. Contrapositively, `1 ≤ k < (Y + 1)^{d+1}` implies at most `d` prime factors `> Y` (`≤ 1` when `k < (Y+1)^2`, `≤ 2` when `k < (Y+1)^3`).
   - Let `M_{Y,K} = lcm {m ∈ [1, K] : ∀ p ∈ m.primeFactors, p ≤ Y}`. Suppose `K < (Y + 1)^2` and `k ∈ [2, K]`. Either `k` is `Y`-smooth (`k ∣ M_{Y,K}`, so `r % k = z % k` whenever `r ≡ z (mod M_{Y,K})`), or `k` has a unique prime factor `p > Y`. In the latter case `p^2 ≥ (Y+1)^2 > K ≥ k`, so `p^2 ∤ k`; writing `k = u p` gives `1 ≤ u ≤ Y` (`u` is `Y`-smooth, `u ∣ M_{Y,K}`, `gcd(u, p) = 1`). By the Chinese Remainder Theorem on `u p`, `r % (u p)` depends only on `(z % u, r % p)`. Grouping letters by their unique prime factor `p ∈ (Y, K]` expresses `saw q K r` on `{r ≡ z (mod M_{Y,K})}` as `F₀(z) + ∑_{p ∈ (Y, K], p prime} Φ_{z,p}(r % p)`.

2. **Exact Hoeffding ANOVA decomposition of `(t % (pq)) / (pq)` on `ℤ/(pq)ℤ`.**
   - For `M ≥ 1`, `centRes M t = (t % M)/M - (M - 1)/(2M)` satisfies `∑_{t < M} centRes M t = 0` and `(1/M) ∑_{t < M} (centRes M t)^2 = (M^2 - 1) / (12 M^2)` via `∑_{j < M} j = M(M-1)/2` and `∑_{j < M} j^2 = M(M-1)(2M-1)/6`.
   - Let `p, q ≥ 1` with `gcd(p, q) = 1`. Every `t ∈ [0, pq)` is uniquely `a + j p` with `a = t % p < p`, `j = t / p < q`. Since `a + j p < pq`, averaging `X(t) = centRes (pq) t` over `j < q` yields `(1/q) ∑_{j < q} X(a + j p) = (1/q) centRes p a =: M₁(a + j p)`. By coprimality, `j ↦ (a + j p) % q` bijects `range q → range q`, so `∑_{j < q} M₂(a + j p) = 0` where `M₂(t) = (1/p) centRes q t`. Symmetrically `∑_{i < p} X(b + i q) = M₂(b)` and `∑_{i < p} M₁(b + i q) = 0`.
   - Hence `Ψ := X - M₁ - M₂` has zero sum along every `p`-fiber and every `q`-fiber, giving exact orthogonality `⟨M₁, M₂⟩ = ⟨M₁, Ψ⟩ = ⟨M₂, Ψ⟩ = 0` on `range (pq)` and Pythagorean decomposition
     $$\frac{p^2 q^2 - 1}{12 p^2 q^2} = \frac{p^2 - 1}{12 p^2 q^2} + \frac{q^2 - 1}{12 p^2 q^2} + \frac{1}{pq}\sum_{t < pq} \Psi(t)^2,$$
     whence `(1/(pq)) ∑_{t < pq} Ψ(t)^2 = (p^2 - 1)(q^2 - 1) / (12 p^2 q^2)`.

3. **First-order Bernoulli slope nonnegativity at `θ = 0`.**
   - For any `IsFeasible K S q`, `saw q K 0 = 0` and `saw q K r ≥ 0` for all `r : ℕ`, so at `θ = 0` the derivative of `∑_{A ⊆ I} θ^{|A|}(1-θ)^{|I|-|A|} saw q K (r_A)` with `r_∅ = 0` equals `∑_{i ∈ I} saw q K (r_{{i}}) ≥ 0`.

4. **Coset fiber expectations, individual rough-prime positivity above `√K`, and solo-prime rigidity above `K / 2`.**
   - For `1 ≤ k₂` and `a < k₁`, `a + j k₁ < k₁ k₂` for all `j < k₂`, so `∑_{j < k₂} ((a + j k₁) % (k₁ k₂)) = k₂ (a + k₁ (k₂ - 1) / 2)`.
   - When `K < (Y + 1)^2` and `p₀ ∈ (Y, K]` is prime, `p₀` is coprime to every `Y`-smooth `m ≤ K` and every prime `p ∈ (Y, K] \ {p₀}`. Choosing `r ≡ v (mod p₀)` and `r ≡ 0` modulo all smooth moduli and all other rough primes makes `saw q K r = cosetPrimeSaw q Y K 0 p₀ v ≥ 0` for every `v`. Setting `Y = p - 1` (`K < p^2`, `p ≤ K`) and summing over `v ∈ range p` via the bijection `j ↦ (j u) % p` yields `0 ≤ ∑_{1 ≤ u ≤ K/p} u q(u p)`, hence `∑_{1 ≤ u ≤ K/p} c(u p) ≤ 0` for every integer producer `(c, m, B)` on `[1, K]`.
   - For any prime `p` with `K < 2 p` and `p ≤ K`, `p` divides no `k ∈ [2, K] \ {p}`; choosing `r ≡ p - 1 (mod p)` and `r ≡ 0` modulo `[2, K] \ {p}` gives `p · stepWeight c r = -c(p)(p - 1)` in `ℤ`, whence `c(p) = p(c(p) + stepWeight c r)` (`p ∣ c(p)`) and `c(p) ≤ 0`.

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
