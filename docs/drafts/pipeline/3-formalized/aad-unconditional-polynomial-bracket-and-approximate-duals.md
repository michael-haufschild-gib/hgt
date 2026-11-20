# Unconditional polynomial rate bracket, quadratic coefficient mass, and approximate fake prime measures

- **ID:** aad-unconditional-polynomial-bracket-and-approximate-duals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-1911/todo.md` #18 · `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheUnconditionalPolynomialBracketAndApproximateDuals.lean`
- **Statement:** Integer floor producers unconditionally attain `HasRate (fun K => K^{-a})` for all `0 < a < 3001 / 24000` (upgrading `bestRate K` to a two-sided polynomial bracket and `HasParityNeutralRate` to `0 < a < 3001 / 120000`), every producer obeys the alphabet-independent bound `∑ |c(k)| / k^2 ≤ 6 · stencilSlope c`, approximate fake prime measures with `|M_u(k) - log k| ≤ η / k` certify `(1 + 6η) · normSlope c m B ≥ mass(u) / (1 - 1/B)`, and the prime mass-move `τ_p = δ_{p-1} + δ_1 - δ_p` isolates the single moment `p · δ_{k,p}` across all `k ≥ 2`.

## Goal
Upgrade the unconditional rate and parity-neutral rate scales of `ArithmeticAuxiliaryDynamics` from Vinogradov–Korobov sub-polynomial bounds to explicit power-saving polynomial laws, establish the `K`-independent `k^{-2}` coefficient-mass law, remove exact moment constraints from dual rate certificates, and isolate single-prime sawtooth coordinates via elementary mass-move operators.

## Gates
- [x] 0 → 1  in-progress: exact dependencies and statements isolated in `ArithmeticAuxiliaryDynamics`
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `TheUnconditionalPolynomialBracketAndApproximateDuals.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Unconditional polynomial rates, parity-neutral polynomial rates, and polynomial `bestRate` bracket.**
   - By `ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths`, `Θ_ζ ≤ 20999 / 24000`, so `1 - Θ_ζ ≥ 3001 / 24000 > 1 / 8`. Applying `hasRate_of_lt_one_sub_zetaZeroAbscissa` yields `HasRate (fun K => K^{-a})` for every `0 < a < 3001 / 24000` (in particular `a = 1 / 8`).
   - Combining `exists_half_floor` (`bestRate K ≥ c₁ / (√K (1 + log K))`) with `csInf_le` on `rateSet K` yields `c₁ / (√K (1 + log K)) ≤ bestRate K ≤ K^{-a}` eventually for every `0 < a < 3001 / 24000`, with asymptotic log-ratio `Θ_ζ - 1 ≤ -3001 / 24000`.
   - For any `Θ ∈ [1/2, 1)` with `ζ(s) ≠ 0` on `Re s > Θ` and `0 < a < (1 - Θ) / 5`, setting `σ = (5a + 1 - Θ) / 2 ∈ (0, 1 - Θ)` gives `|M(n)| ≤ C n^{1-σ}` by `exists_mertens_power_of_zeroFree`, whence `hasParityNeutralRate_of_power` yields `HasParityNeutralRate (fun K => K^{-a})`. Specializing to `Θ = 20999 / 24000` gives unconditional parity-neutral polynomial rates for all `0 < a < 3001 / 120000` (in particular `a = 1 / 40`).

2. **Alphabet-independent quadratic coefficient mass (`∑ |c(k)| / k^2 ≤ 6 · stencilSlope c`).**
   - Let `(c, m, B)` be any producer and `K = sup(support c)`. Since `∑_{j=1}^M 1 / j^2 ≤ 2 - 1/M ≤ 2` for `M ≥ 1` (by telescoping `1 / (M+1)^2 ≤ 1 / M - 1 / (M+1)`), Möbius inversion `|c(k)| ≤ ∑_{d ∣ k} |h(d)|` gives
     $$\sum_{k \in \operatorname{supp}(c)} \frac{|c(k)|}{k^2} \le \sum_{d=1}^K |h(d)| \sum_{j=1}^{\lfloor K/d \rfloor} \frac{1}{(dj)^2} \le 2 \sum_{d=1}^K \frac{g(d) + g(d-1)}{d^2}.$$
   - Because `g(0) = 0`, `1 / d^2 ≤ 2 / (d(d+1))` for `d ≥ 1`, and `1 / (r+1)^2 ≤ 1 / (r(r+1))` for `r ≥ 1`, reindexing `d = r + 1` bounds `∑_{d=1}^K (g(d) + g(d-1)) / d^2 ≤ 3 ∑_{r=1}^K g(r) / (r(r+1)) ≤ 3 · stencilSlope c` via `(isFakePrimeMeasure_pronic K).hasSum_slope`. Multiplying by `2` gives `quadraticMass c ≤ 6 · stencilSlope c`.

3. **Inexact weak duality for approximate fake prime measures.**
   - Let `u : ℕ → ℝ` satisfy `u_j ≥ 0`, `Summable (fun j => u_j ((j+1) % k))`, and `|∑_j u_j ((j+1) % k) - log k| ≤ η / k` for `2 ≤ k ≤ K` (`η ≥ 0`).
   - For any feasible real weights `q` on `S` (`∀ r ∈ S, 1 ≤ r`), summing `u_{r-1} ≤ u_{r-1} saw q K r` over `r ∈ S` gives `targetMass u S ≤ ∑_j u_j saw q K (j+1) = ∑_{k=2}^K q_k M_u(k) ≤ objective q K + η ∑_{k=2}^K |q_k| / k`.
   - For an integer producer `(c, m, B)` on `[1, K]`, substituting `q_k = -c(k) / (m k)` yields `m ∑_{j < B-1} u_j ≤ stencilSlope c + η · quadraticMass c ≤ (1 + 6η) stencilSlope c`, hence `(∑_{j < B-1} u_j) / (1 - 1/B) ≤ (1 + 6η) normSlope c m B`.

4. **Exact single-letter isolation of the prime mass-move `τ_p`.**
   - Let `p ≥ 3` be prime and `k ≥ 2`. If `k = p`, `(p-1) % p + 1 % p - p % p = (p - 1) + 1 - 0 = p`. If `k ≠ p`, primality gives `k ∤ p`, so `1 ≤ p % k < k`, `(p - 1) % k = p % k - 1`, and `1 % k = 1`, yielding `((p - 1) % k) + (1 % k) - (p % k) = 0`.
   - Consequently `saw q K (p - 1) + saw q K 1 - saw q K p = if p ∈ Icc 2 K then p · q_p else 0`, while on `[1, B)` (`B ≥ 2`) the indicator gain `1_{[1,B)}(p-1) + 1_{[1,B)}(1) - 1_{[1,B)}(p)` equals `2` if `p = B` and `1` if `p ≠ B`.

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
