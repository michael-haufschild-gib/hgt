import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Phases.FractionalTaylor
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes.ConvolutionBounds
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation

/-!
# Fractional phases in weighted arithmetic correlations

The short-block Taylor bound supplies the concrete phase error in the
corpus's Bourgain perturbation inequality. It applies to arbitrary complex
weights; higher von Mangoldt weights additionally have an explicit
logarithmic envelope. Frequencies are measured in radians.
-/

noncomputable section

open Finset RHTower
open scoped ArithmeticFunction
open GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Phases

/-- Polynomial replacement with a proved, frequency-dependent error. -/
theorem fractional_correlation_taylor {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (sample : ι → ℝ) (c θ ξ : ℝ) (k : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (hθ : θ ≤ 1)
    (hs : ∀ i ∈ s, sample i ∈ Set.Icc N (N + N ^ θ)) :
    ‖(∑ i ∈ s, a i * bourgainOscillation (ξ * sample i ^ c)) -
        ∑ i ∈ s, a i * bourgainOscillation (ξ * powerTaylor c N k (sample i))‖ ≤
      (|ξ| * powerTaylorConstant c k * N ^ (c - (k + 1) * (1 - θ))) *
        ∑ i ∈ s, ‖a i‖ := by
  apply norm_sum_weighted_bourgainOscillation_sub_le
  intro i hi
  rw [← mul_sub, abs_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (powerTaylor_short_remainder c θ k hN hθ (hs i hi)) (abs_nonneg ξ)

/-- Every genuinely short block admits a polynomial replacement with power saving. -/
theorem exists_fractional_correlation_saving (c : ℝ) {θ : ℝ} (hθ : θ < 1) :
    ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ (s : Finset ℕ) (a : ℕ → ℂ) (N ξ : ℝ),
      1 ≤ N → (∀ n ∈ s, (n : ℝ) ∈ Set.Icc N (N + N ^ θ)) →
      ‖(∑ n ∈ s, a n * bourgainOscillation (ξ * (n : ℝ) ^ c)) -
          ∑ n ∈ s, a n * bourgainOscillation (ξ * powerTaylor c N k n)‖ ≤
        (|ξ| * powerTaylorConstant c k * N ^ (-η)) * ∑ n ∈ s, ‖a n‖ := by
  obtain ⟨k, η, hη, hbound⟩ := exists_powerTaylor_saving c hθ
  refine ⟨k, η, hη, ?_⟩
  intro s a N ξ hN hs
  apply norm_sum_weighted_bourgainOscillation_sub_le
  intro n hn
  rw [← mul_sub, abs_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (hbound N n hN (hs n hn)) (abs_nonneg ξ)

/-- The error for almost-prime weights is explicit at every convolution order. -/
theorem almostPrime_fractional_correlation (s : Finset ℕ) (r k : ℕ)
    (c θ ξ : ℝ) {N : ℝ} (hN : 1 ≤ N) (hθ : θ ≤ 1)
    (hs : ∀ n ∈ s, (n : ℝ) ∈ Set.Icc N (N + N ^ θ)) :
    ‖(∑ n ∈ s, ((Λ ^ r) n : ℂ) * bourgainOscillation (ξ * (n : ℝ) ^ c)) -
        ∑ n ∈ s, ((Λ ^ r) n : ℂ) * bourgainOscillation (ξ * powerTaylor c N k n)‖ ≤
      (|ξ| * powerTaylorConstant c k * N ^ (c - (k + 1) * (1 - θ))) *
        (s.card * Real.log (N + N ^ θ) ^ r) := by
  refine (fractional_correlation_taylor s (fun n => ((Λ ^ r) n : ℂ))
    (fun n => (n : ℝ)) c θ ξ k hN hθ hs).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg (abs_nonneg ξ) (powerTaylorConstant_nonneg c k))
      (Real.rpow_nonneg (zero_le_one.trans hN) _))
  calc ∑ n ∈ s, ‖((Λ ^ r) n : ℂ)‖ ≤ ∑ _n ∈ s, Real.log (N + N ^ θ) ^ r := by
        apply sum_le_sum
        intro n hn
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (convolution_nonneg r n)]
        exact (convolution_le_log_pow r n).trans (pow_le_pow_left₀
          (Real.log_natCast_nonneg n)
          (Real.log_le_log (zero_lt_one.trans_le (hN.trans (hs n hn).1)) (hs n hn).2) r)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Phases
