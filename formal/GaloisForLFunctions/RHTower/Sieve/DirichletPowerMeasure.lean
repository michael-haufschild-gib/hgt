import GaloisForLFunctions.RHTower.Sieve.DirichletPowerPrimeSupport
import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureSixthMoment

/-!
# Level sets of a prime-supported Dirichlet polynomial at a free power

Raising a Dirichlet polynomial to the `k`-th power turns the level `V` into `V^k` without changing
the level set.  For prime-supported coefficients the `k`-fold convolution has `ℓ²` norm at most
`k^k` times the `k`-th power of the coefficient energy, so the measure of the level set is bounded
with `V^{2k}` in the denominator and no power of the length in the numerator.

The exponent `k` is free, which is what a large-values estimate for prime polynomials needs: taking
`k ≍ log T / log N` balances the two terms of the mean-value factor.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- Raising to the `k`-th power does not change the level set. -/
private theorem largeValues_pow_setOf (k N : ℕ) (hk : 1 ≤ k) (a : Fin N → ℂ) (S : Set ℝ) {V : ℝ}
    (hV : 0 ≤ V) :
    {t ∈ S | V ^ k ≤ ‖dirPoly (N ^ k) (dirichletPowerConvolutionConvPow k N a) t‖}
      = {t ∈ S | V ≤ ‖dirPoly N a t‖} := by
  ext t
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  rw [dirichletPowerConvolutionDirPoly_convPow, norm_pow]
  constructor
  · intro h
    exact le_of_pow_le_pow_left₀ (by omega) (norm_nonneg _) h
  · intro h
    exact pow_le_pow_left₀ hV h k

/-- **The level-set bound for a prime-supported polynomial at a free power.** -/
theorem volume_largeValues_pow_le_of_prime_support (k N : ℕ) (hk : 1 ≤ k) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ (2 * k) * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * ((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k) := by
  have hVk : (0 : ℝ) ≤ V ^ k := by positivity
  have hbase := volume_largeValues_le (N ^ k) (dirichletPowerConvolutionConvPow k N a) hT hVk
  rw [largeValues_pow_setOf k N hk a _ hV] at hbase
  have hpow : (V ^ k) ^ (2 : ℕ) = V ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogNk : (0 : ℝ) ≤ Real.log ((N ^ k : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ k) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ k := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)) := by nlinarith
  exact mul_le_mul_of_nonneg_left
    (sum_normSq_convPow_le_of_prime_support k N a hsupp) hfactor

/-- **The level-set bound on a symmetric range, prime-supported coefficients, free power.** -/
theorem volume_largeValues_pow_symm_le_of_prime_support (k N : ℕ) (hk : 1 ≤ k) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ (2 * k) * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * ((T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * ((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k)) := by
  have hVk : (0 : ℝ) ≤ V ^ k := by positivity
  have hbase := volume_largeValues_symm_le (N ^ k) (dirichletPowerConvolutionConvPow k N a) hT hVk
  rw [largeValues_pow_setOf k N hk a (Set.Icc (-T) T) hV] at hbase
  have hpow : (V ^ k) ^ (2 : ℕ) = V ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogNk : (0 : ℝ) ≤ Real.log ((N ^ k : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ k) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ k := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)) := by nlinarith
  have hstep := mul_le_mul_of_nonneg_left
    (sum_normSq_convPow_le_of_prime_support k N a hsupp) hfactor
  linarith

end RHTower.Sieve
