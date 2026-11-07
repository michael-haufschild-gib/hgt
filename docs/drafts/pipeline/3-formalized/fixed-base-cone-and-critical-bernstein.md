# The fixed-base insertion cone and the Euler abscissa transition of Arithmetic Bernstein

- **ID:** fixed-base-cone-critical-bernstein
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/README.md` Open Topic 3; `TheArithmeticBernsteinTheorem`.
- **Statement:**
  1. *Clebsch–Gordan and Dirichlet-dilated Hankel duality.* For all `θ ∈ ℝ` and `a, b ∈ ℕ`,
     `cosSum θ a * cosSum θ b = ∑ r ∈ range (min a b + 1), cosSum θ (a + b - 2 * r)`.
     Consequently, for any trace-summable amplitude `a : (Fin n → ℕ) → ℝ`, `0 ≤ torusSum a θ` for all
     `θ : Fin n → ℝ` if and only if for every `N : ℕ` and `c : (Fin n → ℕ) → ℝ` supported in
     `piBox n N`, the Dirichlet-dilated Hankel form
     `dirichletHankelForm a N c = ∑ d ∈ piBox n N, ∑ u ∈ piBox n N, ∑ v ∈ piBox n N, c (d + u) * c (d + v) * a (u + v)`
     is nonnegative. At any fixed base point `x`, torus positivity across all finite prime sets is
     equivalent to nonnegativity of `dirichletHankelForm (ampl f (log p) x) N c` for all finite prime
     tuples `p`.
  2. *Supercritical separation (`α > 1`).* Let `tentBump y = max(0, 1 − |y − 2 log 2| / log(5/4))`.
     For every `α > 1` there exists `ε₀ > 0` such that for every `ε ∈ (0, ε₀]`, the continuous
     amplitude `f(y) = e^{−αy} − ε · tentBump y` satisfies `ExpDecayFrom x₀ α f` at every `x₀`,
     satisfies left growth `|f(y)| ≤ C e^{−αy}` on `(−∞, 0]`, has strictly positive torus sums on every
     finite set of primes at every base point `x ∈ ℝ` and every phase `θ`, yet satisfies
     `f(2 log 2) f(2 log 3) < f(log 2 + log 3)²` and fails `IsExpConvexFrom 0 f`.
  3. *Critical Euler-abscissa collapse (`0 < α ≤ 1`).* For every `α ∈ (0, 1]` and every nonnegative
     `ψ : ℝ → ℝ` vanishing on `[log 5, ∞)` with `ψ(2 log 2) > 0` (in particular `ε · tentBump` for every
     `ε > 0`), `e^{−αy} − ψ(y)` takes strictly negative torus sums already at the fixed base point
     `x = 0` on a finite set of primes.

## Proof

1. *Clebsch–Gordan and fixed-base duality.* Strong induction on `b` via `cosSum_zero`,
   `cosSum θ 1 = 2 cos θ`, and `cosSum_add_two` proves
   `cosSum θ a * cosSum θ b = ∑ r ≤ min a b, cosSum θ (a + b − 2r)`. Taking products over `i : Fin n`
   gives `chiProd θ k * chiProd θ m = ∑_{d ∈ commonBox k m} chiProd θ (k + m − 2d)`. Integrating
   `torusSum a θ * (∑_{k ∈ piBox n N} c k * chiProd θ k)²` against `torusMeasure n` via
   `integral_torusSum_mul_chiProd` and reindexing `(u, v) = (k − d, m − d)` — which preserves
   `piBox n N` without boundary loss when `c` vanishes outside `piBox n N` — yields
   `dirichletHankelForm a N c`.
   Conversely, since `cosSum θ k` depends only on `cos θ` and spans `ℝ[cos θ]`, if `torusSum a θ₀ < 0`
   then continuity gives an interior point `φ₀ ∈ (0, π)^n`, `η > 0`, and `r ∈ (0, 1)` where
   `torusSum a θ ≤ −η` on `{θ | ∀ i, |cos θ_i − cos φ₀_i| ≤ r}`. Expanding the cosine peak
   `P_m(θ) = ∏_i (1 − (cos θ_i − cos φ₀_i)² / 4)^m` in `chiProd` inside `piBox n (2m + 1)`, positivity
   of `satoTateDensity` on `(0, π)` gives positive mass `μ₀ > 0` on the core where `P_m ≥ (1 − r²/16)^m`,
   while `P_m ≤ (1 − r²/4)^m` outside the negative region, making `∫ torusSum a · P_m² < 0` for large `m`.

2. *Supercritical separation (`α > 1`).* Factoring `ofReal_insertion_eq_tsum_pairs` on `g_α(y) = e^{−αy}`
   and inducting via `torusSum_cons` gives
   `torusSum (ampl g_α ℓ x) θ = e^{−αx} ∏_i ‖1 − e^{−αℓ_i} e^{iθ_i}‖⁻²`.
   For `α > 1` and distinct primes `p_i`, `‖1 − p_i^{−α} e^{iθ_i}‖ ≤ exp(p_i^{−α})`, bounding the Euler
   product below by `c_α = exp(−2 ∑'_{m : ℕ} m^{−α}) > 0` uniformly in `n, p, θ`.
   With `η = (α − 1)/2 > 0`, bounding `(k_i + 1) ≤ 2^{k_i} ≤ p_i^{η k_i}` for `p_i ≥ ⌈2^{1/η}⌉₊` and
   uniformly on the finitely many smaller primes gives `chiSize k ≤ B_η N(k)^η` (`N(k) = ∏_i p_i^{k_i}`).
   Since `tentBump` vanishes on `[log 5, ∞)`, `|tentBump y| ≤ 5^α e^{−αy}`, and unique factorization
   injects `k ↦ N(k)` into `ℕ`, so `|torusSum (ampl tentBump (log p) x) θ| ≤ K_α e^{−αx}` uniformly via
   `∑'_m m^{−(α+1)/2} < ∞`. For `ε ≤ c_α / (2(K_α + 1))`, `f = g_α − ε · tentBump` is strictly
   torus-positive at all `n, p, x, θ`, while `tentBump(log 6) = tentBump(2 log 3) = 0` and
   `tentBump(2 log 2) = 1` force `f(2 log 2) f(2 log 3) < f(log 6)²` and negate `IsExpConvexFrom 0 f`
   at `t = (log 2, log 3)`, `c = (3^{−α}, −2^{−α})`.

3. *Critical collapse (`0 < α ≤ 1`).* By `Nat.Primes.not_summable_one_div`, for any `B > 0` there is a
   finite set `S` of primes `q ≥ 5` with `∑_{q ∈ S} q⁻¹ > B`, hence
   `∏_{q ∈ S} (1 + q^{−α})² ≥ 1 + ∑_{q ∈ S} q⁻¹ > B`. On `{2} ∪ S` at `x = 0` with `θ_2 = 0` and
   `θ_q = π` (`q ∈ S`), `torusSum (ampl g_α (log p) 0) θ < (1 − 2^{−α})⁻² / B`, whereas every nonzero
   contribution to `torusSum (ampl ψ (log p) 0) θ` comes from `k_2 ∈ {0, 1, 2}` (`k_q = 0`), where
   `chiProd θ k = k_2 + 1 > 0` and `torusSum (ampl ψ (log p) 0) θ ≥ 3 ψ(2 log 2) > 0`.

## Lean verification

Module: `GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheFixedBaseConeAndCriticalBernstein.lean`.
Main declarations: `cosSum_mul_cosSum`, `integral_torusSum_mul_sq_eq_dirichletHankel`,
`nonneg_torusSum_iff_dirichletHankel_nonneg`, `torusPositiveAt_iff_dirichletHankel_nonneg`,
`torusSum_ampl_exp_neg`, `exists_supercritical_not_expConvex`,
`exists_prime_set_torusSum_neg_of_le_one`, and `euler_abscissa_perturbation_dichotomy`.

Direct `lake --old env lean` check passed with default limits and no warnings.
All seven transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by the `ArithmeticInnerFunctionTheory` umbrella.
