# The fixed-base insertion cone and the Euler abscissa transition of Arithmetic Bernstein

- **ID:** fixed-base-cone-critical-bernstein
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/README.md` Open Topic 3
- **Statement.**
  1. *Clebsch–Gordan and Dirichlet-dilated Hankel duality.* For all `θ ∈ ℝ` and `a, b ∈ ℕ`,
     `cosSum θ a * cosSum θ b = ∑ r ∈ range (min a b + 1), cosSum θ (a + b - 2 * r)`.
     Consequently, for any trace-summable amplitude `a : (Fin n → ℕ) → ℝ`, `0 ≤ torusSum a θ` for all
     `θ : Fin n → ℝ` if and only if for every `N : ℕ` and `c : (Fin n → ℕ) → ℝ` supported in
     `piBox n N`, the dilated form
     `∑ d ∈ piBox n N, ∑ u ∈ piBox n N, ∑ v ∈ piBox n N, c (d + u) * c (d + v) * a (u + v)`
     is nonnegative. At a fixed base point `x`, torus positivity across all finite prime sets is
     therefore equivalent to positivity of the Dirichlet-dilated Hankel trace rather than the `d = 0`
     undilated Hankel kernel alone.
  2. *Supercritical separation (`α > 1`).* Let `φ(y) = max(0, 1 − |y − 2 log 2| / log(5/4))`. For every
     `α > 1` there exists `ε₀ > 0` such that for every `ε ∈ (0, ε₀]`, the continuous amplitude
     `f(y) = e^{−αy} − ε φ(y)` satisfies `ExpDecayFrom x₀ α f` at every `x₀`, satisfies left growth
     `|f(y)| ≤ C e^{−αy}` on `(−∞, 0]`, has strictly positive torus sums on every finite set of primes
     at every base point `x ∈ ℝ` and every phase `θ`, yet fails `IsExpConvexFrom 0 f`
     (`f(2 log 2) f(2 log 3) < f(log 6)²`).
  3. *Critical Euler-abscissa collapse (`0 < α ≤ 1`).* For every `α ∈ (0, 1]` and every nonnegative
     `ψ : ℝ → ℝ` vanishing on `[log 5, ∞)` with `ψ(2 log 2) > 0` (in particular `ε φ` for every
     `ε > 0`), `e^{−αy} − ψ(y)` takes strictly negative torus sums already at the fixed base point
     `x = 0` on a finite set of primes.

## Goal
Resolves Open Topic 3 of `ArithmeticInnerFunctionTheory`:
- Characterizes what torus positivity at all prime sets forces at a fixed base point `x = 0`: the exact
  Dirichlet-dilated Hankel cone (`∑_d ⟨S_d c, K_f S_d c⟩ ≥ 0`), strictly larger than the exponentially
  convex cone (`d = 0` alone).
- Shows that the left-growth hypothesis in `torusPositive_iff_hankel_nonneg` cannot be dropped above
  the Euler abscissa `κ = 1`, even when positivity holds at all base points `x ∈ ℝ`.
- Locates the exact Euler-product mechanism at `α = 1`: above `1`, convergence of `∑_p p^{−α}` creates
  a uniform interior floor on the torus; on `(0, 1]`, divergence of `∑_p p^{−1}` collapses the `θ_q = π`
  Euler factors `∏(1 + q^{−α})^{−2} → 0` while leaving compactly supported perturbations on `(0, log 5)`
  intact.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `ArithmeticInnerFunctionTheory/TheFixedBaseConeAndCriticalBernstein.lean`

## Paper proof
*1. Clebsch–Gordan and polynomial span `[PROVED HERE]`.* By `cosSum_zero`, `cosSum θ 1 = 2 cos θ`, and
`cosSum_add_two`, strong induction on `b` proves
`cosSum θ a * cosSum θ b = ∑ r ≤ min a b, cosSum θ (a + b − 2r)`: for `b + 2` and `a = k + 1`,
`cosSum θ (k + 1) * (2 cos θ cosSum θ (b + 1) − cosSum θ b) = (cosSum θ (k + 2) + cosSum θ k) *
cosSum θ (b + 1) − cosSum θ (k + 1) * cosSum θ b`, and the `r ≥ 1` slice of `(k + 2, b + 1)` cancels
the `(k + 1, b)` sum identically, leaving `r = 0` plus the `(k, b + 1)` sum shifted by one.

Taking products over `i : Fin n` gives `chiProd θ k * chiProd θ m = ∑_{d ∈ commonBox k m} chiProd θ (k + m − 2d)`.
For trace-summable `a` and `c` supported in `piBox n N = {k | ∀ i, k i < N}`, integrating
`torusSum a θ * (∑_{k ∈ piBox n N} c k * chiProd θ k)²` against `torusMeasure n` via
`integral_torusSum_mul_chiProd` yields
`∑_{k, m ∈ piBox n N} c k * c m * ∑_{d ∈ commonBox k m} a (k + m − 2d)`.
Under the bijection `(u, v) = (k − d, m − d)` — which preserves `piBox n N` without boundary loss since
`d_i + u_i < N ⇒ d_i < N ∧ u_i < N` — this equals
`∑_{d, u, v ∈ piBox n N} c (d + u) * c (d + v) * a (u + v)`.

*2. Duality `[PROVED HERE]`.* (⇒) Nonnegativity of `torusSum a` gives nonnegativity of the integral of
its product with every square. (⇐) By `cosSum_add_two`, `cosSum θ k` depends only on `cos θ`, and
`(cos θ)^m` lies in `span {cosSum θ k | k ≤ m}`. If `torusSum a θ₀ < 0`, setting
`ψ_i = arccos(cos θ₀_i) ∈ [0, π]` preserves `torusSum a` and continuity yields `φ₀ ∈ (0, π)^n`, `η > 0`,
and `r ∈ (0, 1)` such that `torusSum a θ ≤ −η` whenever `∀ i, |cos θ_i − cos φ₀_i| ≤ r`. Let
`P_m(θ) = ∏_i (1 − (cos θ_i − cos φ₀_i)² / 4)^m`, which expands in `{chiProd θ k | k ∈ piBox n (2m + 1)}`.
Outside `{θ | ∀ i, |cos θ_i − cos φ₀_i| ≤ r}`, `0 ≤ P_m(θ) ≤ (1 − r²/4)^m`. On the core
`{θ ∈ (0, π)^n | ∀ i, |cos θ_i − cos φ₀_i| ≤ r / (2(n + 1))}`, each factor exceeds `1 − r²/(16(n + 1))`,
so Bernoulli's inequality gives `P_m(θ) ≥ (1 − r²/16)^m`, while `satoTateDensity > 0` on `(0, π)` gives
the core positive `torusMeasure n` mass `μ₀ > 0`. With `|torusSum a θ| ≤ M` (`abs_torusSum_le`),
`∫ torusSum a · P_m² ≤ −η μ₀ (1 − r²/16)^{2m} + M (1 − r²/4)^{2m} < 0` for large `m`, contradiction.

*3. Exact Euler torus sum and supercritical cushion (`α > 1`) `[PROVED HERE]`.* For `g_α(y) = e^{−αy}`
(`α > 0`) and `ℓ_i > 0`, `ofReal_insertion_eq_tsum_pairs` factors the pair sum for `r = e^{−αℓ}` as
`(∑_a (re^{iθ})^a)(∑_b (re^{−iθ})^b) = ‖1 − re^{iθ}‖^{−2}`. Induction on `n` via `torusSum_cons` gives
`torusSum (ampl g_α ℓ x) θ = e^{−αx} ∏_i ‖1 − e^{−αℓ_i} e^{iθ_i}‖^{−2}`.
For `α > 1` and distinct primes `p_i`, `‖1 − p_i^{−α} e^{iθ_i}‖ ≤ 1 + p_i^{−α} ≤ exp(p_i^{−α})`, so the
product is at least `c_α = exp(−2 ∑'_{m : ℕ} (m : ℝ)^{−α}) > 0` uniformly in `n, p, θ`.

For the tent `φ`, `0 ≤ φ ≤ 1`, `φ(2 log 2) = 1`, and `φ(y) = 0` outside `(log(16/5), log 5) ⊂ (log 3, log 5)`.
Let `η = (α − 1)/2 > 0` and `P_η = ⌈2^{1/η}⌉₊`. For `p_i ≥ P_η` and `k_i ≥ 1`, `k_i + 1 ≤ 2^{k_i} ≤ p_i^{η k_i}`;
for the at most `P_η` primes `< P_η`, `(k_i + 1) 2^{−η k_i} ≤ M_η`. Hence `chiSize k ≤ B_η N(k)^η` for
`N(k) = ∏_i p_i^{k_i}`, with `B_η = M_η^{P_η}` independent of `n, p`. Whenever `φ(x + log N(k)) ≠ 0`,
`x + log N(k) < log 5`, so `1 < 5 e^{−x} / N(k)` and `|φ(x + log N(k))| ≤ 5^α e^{−αx} N(k)^{−α}`.
Since `k ↦ N(k)` is injective by unique prime factorization and `(α + 1)/2 = α − η > 1`,
`|torusSum (ampl φ (log p) x) θ| ≤ 5^α B_η (∑'_{m : ℕ} (m : ℝ)^{−(α+1)/2}) e^{−αx} =: K_α e^{−αx}`
for all `n, p, x, θ`. Choosing `ε ∈ (0, c_α / (2(K_α + 1))]` makes `f = g_α − ε φ` strictly torus-positive
everywhere, while at `t_1 = log 2, t_2 = log 3` with weights `(3^{−α}, −2^{−α})` the Hankel form equals
`−ε · 9^{−α} < 0` since `φ(log 6) = φ(2 log 3) = 0`.

*4. Critical collapse (`0 < α ≤ 1`) `[PROVED HERE]`.* By `Nat.Primes.not_summable_one_div`, for any `B > 0`
there is a finite set `S` of primes `q ≥ 5` with `∑_{q ∈ S} q^{−1} > B`. For `q ≥ 5` and `α ≤ 1`,
`(1 + q^{−α})² ≥ 1 + q^{−1}`, so `∏_{q ∈ S} (1 + q^{−α})² ≥ 1 + ∑_{q ∈ S} q^{−1} > B`.
On the prime tuple `Z = {2} ∪ S` with phases `θ_2 = 0` and `θ_q = π` (`q ∈ S`), at `x = 0`:
`torusSum (ampl g_α (log p) 0) θ = (1 − 2^{−α})^{−2} ∏_{q ∈ S} (1 + q^{−α})^{−2} < (1 − 2^{−α})^{−2} / B`.
Meanwhile every multi-index `k` with `k_q ≥ 1` (`q ∈ S`) or `k_2 ≥ 3` has `∑ k_i log p_i ≥ log 5`, so
`ψ` vanishes there; on the remaining three multi-indices `k_2 ∈ {0, 1, 2}` (`k_q = 0`),
`chiProd θ = cosSum 0 k_2 = k_2 + 1 > 0` and `ψ ≥ 0`, giving
`torusSum (ampl ψ (log p) 0) θ = ψ(0) + 2 ψ(log 2) + 3 ψ(2 log 2) ≥ 3 ψ(2 log 2) > 0`.
Taking `B > (1 − 2^{−α})^{−2} / (3 ψ(2 log 2))` makes `torusSum (ampl (g_α − ψ) (log p) 0) θ < 0`.

## Log
- 2026-11-07 — created in 1-in-progress; paper proof completed and moved to 2-fully-proven.
