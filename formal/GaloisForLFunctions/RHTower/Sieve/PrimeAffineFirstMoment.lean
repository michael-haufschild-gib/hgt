import GaloisForLFunctions.RHTower.Sieve.AffineMeanSquareL1
import GaloisForLFunctions.RHTower.Sieve.GhsInnerFirstMoment
import GaloisForLFunctions.RHTower.Sieve.HalaszPrimeSavingBound

/-!
# The first moment of a prime-supported series, from the affine mean square

For coefficients supported on the primes of `[1, M]` with `‖a_k‖ ≤ A log k`, both masses of the affine
mean square are prime sums that the dyadic Chebyshev cap bounds *independently of `M`*:

`∑_p p^{-2σ}(log p)² ≤ cap(2σ)`,   `∑_p p·p^{-2σ}(log p)² = ∑_p p^{-(2σ-1)}(log p)² ≤ cap(2σ-1)`,

the second requiring only `σ > 1`.  Cauchy–Schwarz against `1` then gives

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖ dy ≤ √(2T(5πe·A²·cap(2σ−1) + (5π/2)·A²·cap(2σ)·T))`,

where the large-values route of `GhsInnerFirstMoment.lean` carries a factor `M log M` inside the root.
For a prime-supported weight the `n`-weighted mass is therefore bounded by a constant, not by `M`: the
saving is a factor `√(M log M / 1)` in the whole range `T ≤ M log M`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The damped power squared is a single power. -/
theorem rpow_neg_sq_eq {k : ℕ} (hk : 1 ≤ k) (σ : ℝ) :
    (((k : ℝ) ^ (-σ)) ^ 2) = (k : ℝ) ^ (-(2 * σ)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [← Real.rpow_natCast ((k : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hk0.le]
  congr 1
  ring

/-- The `n`-weighted damped power is a single shifted power. -/
theorem mul_rpow_neg_sq_eq {k : ℕ} (hk : 1 ≤ k) (σ : ℝ) :
    (k : ℝ) * (((k : ℝ) ^ (-σ)) ^ 2) = (k : ℝ) ^ (-(2 * σ - 1)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hadd : (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (-(2 * σ)) = (k : ℝ) ^ ((1 : ℝ) + -(2 * σ)) :=
    (Real.rpow_add hk0 1 (-(2 * σ))).symm
  rw [Real.rpow_one] at hadd
  rw [rpow_neg_sq_eq hk σ, hadd]
  congr 1
  ring

/-- **The plain mass of a prime-supported damped weight.** -/
theorem generalMeanSquareRate_prime_le {a : ℕ → ℂ} {A : ℝ} {M : ℕ}
    (hprime : ∀ k : ℕ, a k ≠ 0 → Nat.Prime k) (hA : ∀ k : ℕ, ‖a k‖ ≤ A * Real.log k) {σ : ℝ}
    (hσ : 1 < σ) :
    generalMeanSquareRate a (Finset.Icc 1 M) σ ≤ (5 * Real.pi / 2) * (A ^ 2 * sieveCapPrime (2 * σ)) := by
  classical
  have hw : (1 : ℝ) < 2 * σ := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 M,
      ‖a k * ((((k : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 = ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2 := by
    intro k _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _), mul_pow]
  have hdrop : ∑ k ∈ Finset.Icc 1 M with Nat.Prime k, ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2
      = ∑ k ∈ Finset.Icc 1 M, ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2 := by
    refine Finset.sum_filter_of_ne fun k _ hne => ?_
    refine hprime k ?_
    intro h0
    rw [h0] at hne
    simp at hne
  have hcap := sum_prime_logSq_rpow_neg_le hw M
  have hbound : ∑ k ∈ Finset.Icc 1 M with Nat.Prime k, ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2
      ≤ A ^ 2 * sieveCapPrime (2 * σ) := by
    have hstep : ∑ k ∈ Finset.Icc 1 M with Nat.Prime k, ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2
        ≤ ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
            A ^ 2 * ((k : ℝ) ^ (-(2 * σ)) * (Real.log k) ^ 2) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := hk.1.1
      have hsq : ‖a k‖ ^ 2 ≤ A ^ 2 * (Real.log k) ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg (a k)) (hA k) 2
        rwa [mul_pow] at h
      rw [rpow_neg_sq_eq hk1 σ]
      have hpow : (0 : ℝ) ≤ (k : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (Nat.cast_nonneg k) _
      calc ‖a k‖ ^ 2 * (k : ℝ) ^ (-(2 * σ))
          ≤ (A ^ 2 * (Real.log k) ^ 2) * (k : ℝ) ^ (-(2 * σ)) :=
            mul_le_mul_of_nonneg_right hsq hpow
        _ = A ^ 2 * ((k : ℝ) ^ (-(2 * σ)) * (Real.log k) ^ 2) := by ring
    rw [← Finset.mul_sum] at hstep
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hmul := mul_le_mul_of_nonneg_left hcap hA2
    calc ∑ k ∈ Finset.Icc 1 M with Nat.Prime k, ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2
        ≤ A ^ 2 * ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
            (k : ℝ) ^ (-(2 * σ)) * (Real.log k) ^ 2 := hstep
      _ ≤ A ^ 2 * sieveCapPrime (2 * σ) := hmul
  rw [generalMeanSquareRate, Finset.sum_congr rfl hterm, ← hdrop]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- **The `n`-weighted mass of a prime-supported damped weight.**  Bounded by a constant, not by `M`. -/
theorem generalMeanSquareConst_prime_le {a : ℕ → ℂ} {A : ℝ} {M : ℕ}
    (hprime : ∀ k : ℕ, a k ≠ 0 → Nat.Prime k) (hA : ∀ k : ℕ, ‖a k‖ ≤ A * Real.log k) {σ : ℝ}
    (hσ : 1 < σ) :
    generalMeanSquareConst a (Finset.Icc 1 M) σ
      ≤ 5 * Real.pi * Real.exp 1 * (A ^ 2 * sieveCapPrime (2 * σ - 1)) := by
  classical
  have hw : (1 : ℝ) < 2 * σ - 1 := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 M,
      (k : ℝ) * ‖a k * ((((k : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        = ‖a k‖ ^ 2 * ((k : ℝ) * ((k : ℝ) ^ (-σ)) ^ 2) := by
    intro k _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _), mul_pow]
    ring
  have hdrop : ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
        ‖a k‖ ^ 2 * ((k : ℝ) * ((k : ℝ) ^ (-σ)) ^ 2)
      = ∑ k ∈ Finset.Icc 1 M, ‖a k‖ ^ 2 * ((k : ℝ) * ((k : ℝ) ^ (-σ)) ^ 2) := by
    refine Finset.sum_filter_of_ne fun k _ hne => ?_
    refine hprime k ?_
    intro h0
    rw [h0] at hne
    simp at hne
  have hcap := sum_prime_logSq_rpow_neg_le hw M
  have hbound : ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
        ‖a k‖ ^ 2 * ((k : ℝ) * ((k : ℝ) ^ (-σ)) ^ 2)
      ≤ A ^ 2 * sieveCapPrime (2 * σ - 1) := by
    have hstep : ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
          ‖a k‖ ^ 2 * ((k : ℝ) * ((k : ℝ) ^ (-σ)) ^ 2)
        ≤ ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
            A ^ 2 * ((k : ℝ) ^ (-(2 * σ - 1)) * (Real.log k) ^ 2) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := hk.1.1
      have hsq : ‖a k‖ ^ 2 ≤ A ^ 2 * (Real.log k) ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg (a k)) (hA k) 2
        rwa [mul_pow] at h
      rw [mul_rpow_neg_sq_eq hk1 σ]
      have hpow : (0 : ℝ) ≤ (k : ℝ) ^ (-(2 * σ - 1)) := Real.rpow_nonneg (Nat.cast_nonneg k) _
      calc ‖a k‖ ^ 2 * (k : ℝ) ^ (-(2 * σ - 1))
          ≤ (A ^ 2 * (Real.log k) ^ 2) * (k : ℝ) ^ (-(2 * σ - 1)) :=
            mul_le_mul_of_nonneg_right hsq hpow
        _ = A ^ 2 * ((k : ℝ) ^ (-(2 * σ - 1)) * (Real.log k) ^ 2) := by ring
    rw [← Finset.mul_sum] at hstep
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hmul := mul_le_mul_of_nonneg_left hcap hA2
    calc ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
          ‖a k‖ ^ 2 * ((k : ℝ) * ((k : ℝ) ^ (-σ)) ^ 2)
        ≤ A ^ 2 * ∑ k ∈ Finset.Icc 1 M with Nat.Prime k,
            (k : ℝ) ^ (-(2 * σ - 1)) * (Real.log k) ^ 2 := hstep
      _ ≤ A ^ 2 * sieveCapPrime (2 * σ - 1) := hmul
  rw [generalMeanSquareConst, Finset.sum_congr rfl hterm, ← hdrop]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- **The first moment of a prime-supported series, `M`-free inside the root.** -/
theorem integral_Icc_norm_LSeries_prime_le_affine {a : ℕ → ℂ} {A : ℝ} {M : ℕ}
    (hsupp : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M)
    (hprime : ∀ k : ℕ, a k ≠ 0 → Nat.Prime k) (hA : ∀ k : ℕ, ‖a k‖ ≤ A * Real.log k) {σ : ℝ}
    (hσ : 1 < σ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ Real.sqrt (2 * T
          * (5 * Real.pi * Real.exp 1 * (A ^ 2 * sieveCapPrime (2 * σ - 1))
            + (5 * Real.pi / 2) * (A ^ 2 * sieveCapPrime (2 * σ)) * T)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  refine le_trans (integral_Icc_norm_LSeries_le_sqrt_general_affine hs0 hsupp σ hT)
    (Real.sqrt_le_sqrt ?_)
  have hC := generalMeanSquareConst_prime_le (M := M) hprime hA hσ
  have hR := generalMeanSquareRate_prime_le (M := M) hprime hA hσ
  have hRT : generalMeanSquareRate a (Finset.Icc 1 M) σ * T
      ≤ (5 * Real.pi / 2) * (A ^ 2 * sieveCapPrime (2 * σ)) * T :=
    mul_le_mul_of_nonneg_right hR hT0.le
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith
  exact mul_le_mul_of_nonneg_left (by linarith) h2T

end RHTower.Sieve
end
