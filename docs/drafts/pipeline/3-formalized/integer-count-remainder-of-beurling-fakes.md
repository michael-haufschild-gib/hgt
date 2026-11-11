# Least integer-count remainder of discrete integer-norm Beurling fakes

- **ID:** integer-count-remainder-of-beurling-fakes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §4, Question B182 (wall Γ230)
- **Statement:** Complete determination of the integer-count remainder exponent regimes for discrete integer-norm Beurling fakes, together with their structural obstructions, real-zero law for prime deletions, quadratic `L`-function calibration, and ZFC frontier dichotomy (`integerNormFake_complete_solution`).

## Lean Modules and Main Declarations

Namespace: `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`

1. `formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/IntegerNormFakeObstructions.lean`
   - `NotNormEquivPrimes`, `IsIntegerNormFakeAt`, `integerNormFakeExponents`, `IsIntegerNormFakeAt.mono`
   - `density_unique_of_lt_one`, `hasLinearCounting_of_count_sub_le`, `not_unit_density_sublogarithmic_of_integerNormFakeAt`
   - `pos_density_of_integerNormFakeAt_le_half`, `nonneg_of_integerNormFakeAt`, `bddBelow_integerNormFakeExponents`
   - `keptPrimeSystem`, `keptPrimeSystem_count_sub_le_of_summable`
   - `no_fake_zero_of_finite_missing_primes`, `infinite_missing_primes_of_integerNormFakeAt`, `not_isIntegerNormFakeAt_of_surjective_primes`, `not_isIntegerNormFakeAt_keptPrimeSystem_of_finite`
   - `quadraticCharacterSystem`, `quadraticCharacterSystem_count_sub_le`, `quadraticCharacterSystem_zetaSeriesC_eq`, `isIntegerNormFakeAt_half_of_quadratic_LFunction_zero`
2. `formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/IntegerNormFakesAboveOneHalf.lean`
   - `necklaceCount`, `sum_divisors_mul_necklaceCount`, `tsum_necklaceCount_mul_neg_log_eq`, `exp_tsum_necklaceCount_log_cpow_eq`
   - `exists_shortInterval_necklace_primes`, `exists_keptPrimeSystem_fake_above_half`
   - `exists_integerNormFakeAt_of_half_lt`, `Ioi_half_subset_integerNormFakeExponents`, `nonempty_integerNormFakeExponents`, `csInf_integerNormFakeExponents_mem_Icc`
3. `formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/IntegerNormFakesBelowOneHalf.lean`
   - `isIntegerNormFakeAt_keptPrimeSystem_of_deletionData`
   - `exists_integerNormFakeAt_lt_half_of_zeroFree`, `csInf_integerNormFakeExponents_lt_half_of_zeroFree`
   - `exists_integerNormFakeAt_of_riemannHypothesis`, `csInf_integerNormFakeExponents_le_one_third_of_riemannHypothesis`
   - `zetaZeroAbscissa_lt_one_iff_zetaAsymptoticAbscissa_lt_one`, `zetaZeroAbscissa_eq_one_iff_zetaAsymptoticAbscissa_eq_one`
   - `zetaZeroAbscissa_eq_one_or_exists_integerNormFakeAt_lt_half`, `asymptoticAbscissaLaw_or_exists_integerNormFakeAt_lt_half`, `exists_integerNormFakeAt_lt_half_of_not_asymptoticAbscissaLaw`
   - `exists_real_fake_zero_of_keptPrimeSystem`, `exists_real_fake_zero_of_keptPrimeSystem_le_half`
   - `integerNormFake_complete_solution`

## Definitions

A discrete Beurling system `B : RHTower.BeurlingSystem` is an **integer-norm fake at exponent `β`** (`IsIntegerNormFakeAt B β`) if:
1. `HasIntegerNorms B` and `B.IsDiscrete`;
2. `NotNormEquivPrimes B`: `¬ Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} // ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)}`;
3. `∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β`;
4. `∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧ ∃ ρ₀ : ℂ, 1 / 2 < ρ₀.re ∧ ρ₀ ≠ 1 ∧ G ρ₀ = 0 ∧ riemannZeta ρ₀ ≠ 0`.

## Mathematical Proofs

### 1. Unconditional existence on `(1/2, ∞)` via Moreau necklaces and short prime intervals
Given `β > 1/2`, set `β₁ = min β (29/50) ∈ (1/2, 29/50]` and choose `b ≥ 4` so that `M = b^2 ≥ 16`, `a = b + 1 ≥ 5`, and `β₀ = log a / log M ∈ (1/2, β₁)` (`M^{β₀} = a`).

For `k ≥ 1`, `ZMod k` acts by cyclic shift on `ZMod k → Fin a`. Partitioning words by minimal positive period `d ∣ k` yields primitive necklace counts `u(a, k) = necklaceCount a k` satisfying `1 ≤ u(a, k) ≤ a^k` and `∑_{d ∣ m} d · u(a, d) = a^m` (`sum_divisors_mul_necklaceCount`), hence `∏_{k ≥ 1} (1 - z^k)^{u(a, k)} = 1 - a z` for `a ‖z‖ < 1` (`exp_tsum_necklaceCount_log_cpow_eq`).

By `exists_theta_window_lower_seventeenThirtieths` (`17/30 < 29/50 < 3/5`), for all `k ≥ k₀` the disjoint short intervals `(M^k, M^k + M^{3k/5}]` each contain at least `u(a, k) ≤ M^{k β₀}` primes (`exists_shortInterval_necklace_primes`); for `1 ≤ k < k₀`, disjoint `u(a, k)`-element prime sets are chosen above `M^{k₀}` outside those intervals. Letting `S = ⋃_{k ≥ 1} S_k`:
- `∑_{p ∈ S} p^{-β'} < ∞` for `β' = min β (3/4) > β₀`, so Rankin convolution (`keptPrimeSystem_count_sub_le_of_summable`) gives `|N_{ℙ \ S}(x) - A x| ≤ C x^β` with `A > 0`.
- For `Re s > 1/4`, `∑_k ∑_{p ∈ S_k} ‖(1 - p^{-s})/(1 - M^{-ks}) - 1‖` converges locally uniformly because `β₀ - 2/5 < 1/5 < 1/4`, giving a nonvanishing holomorphic perturbation factor `E(s)` and continuation `G(s) = ζ_u(s) (1 - a M^{-s}) E(s)` of `(s - 1) ζ_{ℙ \ S}(s)` across `{Re s > 1/2}`.
- `1 - a M^{-s}` vanishes both at the real point `ρ₀ = β₀ ∈ (1/2, 1)` and at the off-real point `ρ₁ = β₀ + 2π i / log M` (`0 < Im ρ₁ < 4`), where `ζ` is nonzero by `riemannZeta_ne_zero_of_abs_im_lt_four` (`exists_keptPrimeSystem_fake_above_half`, `Ioi_half_subset_integerNormFakeExponents`).

### 2. Lower bound, structural obstructions, and real fake zero law for prime deletions
- **Zero-density obstruction (`pos_density_of_integerNormFakeAt_le_half`) and nonnegativity (`nonneg_of_integerNormFakeAt`):** If `A = 0` and `β ≤ 1/2`, then `N_B(x) = O(x^{1/2})` gives absolute convergence and Euler-product nonvanishing of `ζ_B` on `{Re s > 1/2}`. Hence every fake at `β ≤ 1/2` has `A > 0`. Since `N_B` is constant on `[n + 1/4, n + 3/4]`, `A / 2 ≤ 2 C n^β` forces `β ≥ 0` for every fake, so `sInf integerNormFakeExponents ∈ [0, 1/2]` (`csInf_integerNormFakeExponents_mem_Icc`).
- **Infinite missing primes (`no_fake_zero_of_finite_missing_primes`, `infinite_missing_primes_of_integerNormFakeAt`):** If `B` has integer norms, linear counting, and omits only a finite prime set `D`, injecting one generator per prime in `ℙ \ D` factors `B.zetaSeriesC s = (∏_{p ∈ D} (1 - p^{-s})) ζ(s) Z_R(s)` where `Z_R` has nonnegative Dirichlet coefficients (`Z_R(1) ≥ 1`). Applying `landau_local_summability_transfer` along `(1/2, ∞)` using `ζ(σ) ≠ 0` on `(0, 1)` extends absolute convergence of `Z_R` to `{Re s > 1/2}`, where Euler inversion forces `Z_R(s) ≠ 0`. Thus every fake at `β ≤ 1` omits infinitely many primes; neither pure additions (`not_isIntegerNormFakeAt_of_surjective_primes`) nor finite deletions (`not_isIntegerNormFakeAt_keptPrimeSystem_of_finite`) ever yield a fake.
- **Unit-density sublogarithmic rigidity (`not_unit_density_sublogarithmic_of_integerNormFakeAt`):** Immediate from `primes_of_sublogarithmic_count_error`.
- **Real fake zero law for prime deletions (`exists_real_fake_zero_of_keptPrimeSystem`, `exists_real_fake_zero_of_keptPrimeSystem_le_half`):** If `keptPrimeSystem S` is a fake at `β < 1` with `A > 0` (automatic when `β ≤ 1/2`), injective multiplication `SFree S × sOnly S → ℕ` inside `[1, X]` at `X = max(N, (N C' + 1)^{1/(1 - β')})` bounds `∑_{n ≤ N, S-smooth} 1/n ≤ 2/A`, so `L_S(s) = ∑_{n S-smooth} n^{-s}` converges at `s = 1` with `‖L_S(σ)‖ ≤ 2/A` for `σ ≥ 1`. From `G(s) L_S(s) = ζ_u(s)` and `ζ_u(1) = 1` it follows that `G(1) ≠ 0`. Letting `σ_c = sInf {σ > 1/2 | LSeriesSummable sSmoothR σ} ∈ [1/2, 1]`, `G(s) L_S(s) = ζ_u(s)` holds on `{Re s > σ_c}`, so every fake zero `ρ` satisfies `Re ρ ≤ σ_c` (giving `σ_c > 1/2`). If `G(σ_c) ≠ 0`, `landau_local_summability_transfer` applied to `ζ_u / G` transfers summability of `L_S` to `σ_c - δ/2`, contradicting `σ_c = sInf`. Hence `G(σ_c) = 0`, `σ_c < 1` (since `G(1) ≠ 0`), and `ζ(σ_c) ≠ 0`.
- **Quadratic `L`-function model (`isIntegerNormFakeAt_half_of_quadratic_LFunction_zero`):** For `χ^2 = 1`, `χ ≠ 1` modulo `N`, `quadraticCharacterSystem χ` realizes Euler factors `(1 - p^{-s})^{-1}(1 - χ(p) p^{-s})^{-1}` with integer norms, satisfies `|N_B(x) - L(1, χ) x| ≤ (6 N + 1) x^{1/2}` via hyperbola splitting at `√x` and Pólya–Vinogradov/abelian character bounds, and `(s - 1) ζ_B(s) = ζ_u(s) L(s, χ)`.

### 3. Sub-`1/2` prime-deletion fakes and unconditional ZFC frontier dichotomy
Given `Θ < 1` with `ζ(z) ≠ 0` on `{Re z > Θ}`, set `Θ' = max Θ (3/4)`, `c = (1 - Θ') / 8 ∈ (0, 1/32]`, `α = 1/2 + c/8`, `σ₀ = 1/2 - c`, and choose `D : DeletionData α` (`exists_deletionData`). On `Re s ≥ σ₀`, `Re(s + 1 - α) ≥ 1 - 9c/8 > Θ'`, so Hadamard three-circles (`exists_zeta_lower_bound_subpolynomial_of_zeroFree`) bounds `1/ζ_u(s + 1 - α)` subpolynomially while Weyl subconvexity (`exists_norm_riemannZeta_le_subconvex`) bounds `|ζ(σ₀ + i t + 1 - α)| ≪ |t|^{c/3}`, giving `|L(λ_S, σ₀ + i t)| ≪ (|t| + 3)^{c/2}`. Dyadic sawtooth-hyperbola splitting between `M₁ = X^{1 - 9c/8}` and `M₂ = X^{1 - c/2}` yields `|N_{ℙ \ D.S}(X) - A X| ≤ C X^{1/2 - c/8}` where `1/2 - c/8 = 1/2 - (1 - max Θ (3/4)) / 64 < 1/2`, while `D.perronNum` is holomorphic on `{Re s > 1/2}` and vanishes at `s = α` (`exists_integerNormFakeAt_lt_half_of_zeroFree`). Under `RiemannHypothesis`, `D.exists_norm_count_sub_le_saw` reaches every `β > 1/3` (`exists_integerNormFakeAt_of_riemannHypothesis`).

Finally, since `ζ` has no zeros on `Re s ≥ 1`, any finite upper layer `{q : XiZeroCopy | σ < Re q}` (`σ < 1`) has maximum strictly below `1`, proving `zetaZeroAbscissa < 1 ↔ zetaAsymptoticAbscissa < 1` (`zetaZeroAbscissa_lt_one_iff_zetaAsymptoticAbscissa_lt_one`). Combining `zetaZeroAbscissa ≤ 1` with `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa` yields the unconditional ZFC dichotomy (`zetaZeroAbscissa_eq_one_or_exists_integerNormFakeAt_lt_half`, `asymptoticAbscissaLaw_or_exists_integerNormFakeAt_lt_half`).
