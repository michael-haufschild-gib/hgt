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

/-- **The first moment of a prime-supported series, by large values.**  For coefficients supported on the primes of
`[1, M]` with `‖a_k‖ ≤ A log k`, the `ℓ²` mass of the damped coefficients is at most `A²` times the dyadic Chebyshev
cap, so

`∫_{|y| ≤ nΔ} ‖L(a, σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M(1+log M))(1/Δ + 2 log M)·A²·cap(2σ))`.

Everything on the right is explicit in `n, Δ, M, σ, A`: no window, no measure, and no trivial size of the series. -/
theorem integral_norm_LSeries_prime_le {a : ℕ → ℂ} {A : ℝ} {M : ℕ} (hM : 2 ≤ M)
    (hsupp : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hprime : ∀ k : ℕ, a k ≠ 0 → Nat.Prime k)
    (hA : ∀ k : ℕ, ‖a k‖ ≤ A * Real.log k) {σ : ℝ} (hσ : 1 < σ) {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ)
    (hn : 1 ≤ n) :
    (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (M : ℝ) * (1 + Real.log M))
              * (1 / Δ + 2 * Real.log M) * (A ^ 2 * sieveCapPrime (2 * σ)))) := by
  classical
  refine le_trans (integral_norm_LSeries_le_largeValues hM hsupp σ hΔ n hn) ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [sum_fin_normSq_damped_eq]
  have hw : (1 : ℝ) < 2 * σ := by linarith
  have hcap := sum_prime_logSq_rpow_neg_le hw M
  have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have hterm : ∀ k ∈ Finset.Icc 1 M,
      ‖a k‖ ^ 2 * ((k : ℝ) ^ (-σ)) ^ 2
        ≤ A ^ 2 * (if Nat.Prime k then (k : ℝ) ^ (-(2 * σ)) * (Real.log k) ^ 2 else 0) := by
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
      have hsqb : ‖a k‖ ^ 2 ≤ A ^ 2 * (Real.log k) ^ 2 := by
        have h := hA k
        have h0 : (0 : ℝ) ≤ ‖a k‖ := norm_nonneg _
        calc ‖a k‖ ^ 2 ≤ (A * Real.log k) ^ 2 := pow_le_pow_left₀ h0 h 2
          _ = A ^ 2 * (Real.log k) ^ 2 := by ring
      have := mul_le_mul_of_nonneg_right hsqb (Real.rpow_nonneg hkpos.le (-(2 * σ)))
      calc ‖a k‖ ^ 2 * (k : ℝ) ^ (-(2 * σ))
          ≤ A ^ 2 * (Real.log k) ^ 2 * (k : ℝ) ^ (-(2 * σ)) := this
        _ = A ^ 2 * ((k : ℝ) ^ (-(2 * σ)) * (Real.log k) ^ 2) := by ring
    · rw [if_neg hp]
      have hzero : a k = 0 := by
        by_contra hne
        exact hp (hprime k hne)
      rw [hzero, norm_zero]
      simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, ← Finset.sum_filter, sieveCapPrime]
  exact mul_le_mul_of_nonneg_left hcap hA2

/-- The inner prime weight: `A = 1`. -/
theorem integral_norm_LSeries_ghsInner_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {M : ℕ} (hM : 2 ≤ M)
    {σ : ℝ} (hσ : 1 < σ) {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖LSeries (ghsInner f M) ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (M : ℝ) * (1 + Real.log M))
              * (1 / Δ + 2 * Real.log M) * ((1 : ℝ) ^ 2 * sieveCapPrime (2 * σ)))) :=
  integral_norm_LSeries_prime_le hM (fun _ hk => ghsInner_mem_Icc hk)
    (fun _ hk => ghsInner_support hk) (by simpa using norm_ghsInner_le hf M) hσ hΔ n hn

/-- The outer prime weight: `A = 1/log 2`. -/
theorem integral_norm_LSeries_ghsOuter_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 2 ≤ N)
    {σ : ℝ} (hσ : 1 < σ) {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖LSeries (ghsOuter f N) ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (N : ℝ) * (1 + Real.log N))
              * (1 / Δ + 2 * Real.log N) * ((1 / Real.log 2) ^ 2 * sieveCapPrime (2 * σ)))) :=
  integral_norm_LSeries_prime_le hN (fun _ hk => ghsOuter_mem_Icc hk)
    (fun _ hk => ghsOuter_support hk) (norm_ghsOuter_le hf N) hσ hΔ n hn

end RHTower.Sieve
end
