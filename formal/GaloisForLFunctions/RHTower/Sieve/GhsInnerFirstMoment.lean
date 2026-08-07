import GaloisForLFunctions.RHTower.Sieve.LSeriesFirstMomentLargeValues
import GaloisForLFunctions.RHTower.Sieve.HalaszPrimeSavingBound
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue
/-!
# The first moment of the inner prime weight's series

The `ℓ²` mass of the damped coefficients of a finitely supported sequence is a sum over `[1, M]`, and for the inner
prime weight `f(q)log q` it is at most the prime sum `∑_p p^{−2σ}(log p)²`, which the dyadic Chebyshev cap bounds.
So the large-values first moment reads

`∫_{|y| ≤ nΔ} ‖L(b, σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M(1+log M))(1/Δ + 2 log M)·cap(2σ))`,

with `cap` the dyadic Chebyshev bound.  Every quantity on the right is explicit in `n, Δ, M, σ` — no window, no
measure, and no trivial size of the series.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- The `ℓ²` mass of the damped coefficients, as a sum over `[1, M]`. -/
theorem sum_fin_normSq_damped_eq (a : ℕ → ℂ) (M : ℕ) (σ : ℝ) :
    ∑ i : Fin M, ‖a ((i : ℕ) + 1) * (((((i : ℕ) + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2
      = ∑ k ∈ Finset.Icc 1 M, ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2 := by
  classical
  have hterm : ∀ k : ℕ, ‖a k * ((((k : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2
      = ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2 := by
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _), mul_pow]
  have h := sum_fin_eq_sum_Icc M (fun k => ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hterm ((i : ℕ) + 1)]

/-- **The first moment of the inner prime weight's series, by large values.**  The `ℓ²` mass of its damped
coefficients is a prime sum of squared logarithms, which the dyadic Chebyshev cap bounds. -/
theorem integral_norm_LSeries_ghsInner_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {M : ℕ} (hM : 2 ≤ M)
    {σ : ℝ} (hσ : 1 < σ) {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖LSeries (ghsInner f M) ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (M : ℝ) * (1 + Real.log M))
              * (1 / Δ + 2 * Real.log M) * sieveCapPrime (2 * σ))) := by
  classical
  have hsupp : ∀ k : ℕ, ghsInner f M k ≠ 0 → k ∈ Finset.Icc 1 M :=
    fun k hk => ghsInner_mem_Icc hk
  refine le_trans (integral_norm_LSeries_le_largeValues hM hsupp σ hΔ n hn) ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the mass against the dyadic cap
  rw [sum_fin_normSq_damped_eq]
  have hw : (1 : ℝ) < 2 * σ := by linarith
  have hcap := sum_prime_logSq_rpow_neg_le hw M
  refine le_trans ?_ (le_trans hcap (le_of_eq (by rw [sieveCapPrime])))
  -- termwise: the coefficients vanish off the primes and are at most `log` there
  have hterm : ∀ k ∈ Finset.Icc 1 M,
      ‖ghsInner f M k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2
        ≤ (if Nat.Prime k then (k : ℝ) ^ (-(2 * σ)) * (Real.log k) ^ 2 else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have hsq : ((k : ℝ) ^ (-σ)) ^ 2 = (k : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast ((k : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hkpos.le]
      norm_num
      ring_nf
    by_cases hp : Nat.Prime k
    · rw [if_pos hp, hsq]
      have hb : ‖ghsInner f M k‖ ≤ Real.log k := norm_ghsInner_le hf M k
      have hlogk : (0 : ℝ) ≤ Real.log k := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        exact Real.log_nonneg this
      have hsqb : ‖ghsInner f M k‖ ^ 2 ≤ (Real.log k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
      exact mul_le_mul_of_nonneg_right hsqb (Real.rpow_nonneg hkpos.le _) |>.trans
        (le_of_eq (by ring))
    · rw [if_neg hp]
      have hzero : ghsInner f M k = 0 := by
        rw [ghsInner, if_neg (by tauto)]
      rw [hzero, norm_zero]
      simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter]

end RHTower.Sieve
end
