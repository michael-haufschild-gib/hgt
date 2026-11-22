import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.DerivativeDetector
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.LargeDerivativePrimeMean
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeDoubleMean

/-! A zero near the sampling point forces a large integrated prime sum. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Finset
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

theorem derSeries_twist {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) (x τ : ℝ) :
    derSeries (fun n : ℕ => χ (n : ZMod q)) k ((x : ℝ) + τ * I) =
      derSeries (fun n : ℕ => χ (n : ZMod q) * (n : ℂ) ^ (-(τ * I))) k (x : ℝ) := by
  unfold derSeries
  refine tsum_congr fun n => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
    ring

theorem zero_detect_prime_mean : ∃ a b C C' r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < C' ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) →
      Real.log (q * (|τ| + 2)) ≤ L → 0 < r → 1 ≤ r * L → r ≤ r₀ → C' * (r * L) ≤ K → K₀ ≤ K →
      IsLZero χ ρ → ‖ρ - (1 + τ * I)‖ ≤ r →
      Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)),
        ‖primeSum χ (Real.exp (a * K / r)) y τ‖ ^ 2 / y := by
  obtain ⟨A, C3, r3, hA, hC3, hr3, H3⟩ := exists_large_log_derivative
  obtain ⟨a, b, C4, r4, K0, ha, hab, hC4, hr4, H4⟩ := large_mean_of_large_derivative A hA
  refine ⟨a, b, C4, C3, min r3 r4, K0, ha, hab, hC4, hC3, lt_min hr3 hr4, ?_⟩
  intro q _ χ τ r L K ρ h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨k, k1, k2, k3⟩ := H3 q χ τ r L K ρ h1 h2 h3 h4 (h5.trans (min_le_left _ _)) h6 h8 h9
  have hs : 1 < (((1 + r : ℝ) : ℂ) + τ * I).re := by simpa using h3
  rw [← derSeries_eq_log_derivative χ k hs, derSeries_twist, div_pow, one_pow] at k3
  have := H4 _ r K k (fun n => by
    rw [norm_mul]; exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_cpow_le n τ))
    h3 (h5.trans (min_le_right _ _)) h7 k1 k2 k3
  refine this.trans (le_of_eq ?_)
  congr 1
  ext y
  unfold primeSum
  congr 3
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem zero_near_sampling_line {ρ : ℂ} {σ r τ : ℝ} (h1 : σ ≤ ρ.re) (h2 : ρ.re < 1) (h3 : 2 * (1 - σ) ≤ r)
    (h4 : |τ - ρ.im| ≤ r / 2) : ‖ρ - (1 + τ * I)‖ ≤ r := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (ρ - (1 + τ * I)).re = ρ.re - 1 := by simp
  have e2 : (ρ - (1 + τ * I)).im = ρ.im - τ := by simp
  rw [e1, e2, abs_sub_comm ρ.im, abs_of_neg (by linarith)]
  linarith

end QH.PrimeProgressions
