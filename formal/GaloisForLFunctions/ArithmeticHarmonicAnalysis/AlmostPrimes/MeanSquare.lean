import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes.ConvolutionBounds
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import GaloisForLFunctions.RHTower.ShortWindowNoGo

/-!
# Mean squares of higher von Mangoldt polynomials

The almost-prime coefficients of arXiv:2611.05000 fit the existing
Dirichlet-polynomial mean-value theorem at every order. Their logarithmic
envelope gives unconditional bounds on every vertical line and an explicit
critical-line bound, without shifted-moment or zero-location assumptions.
-/

noncomputable section

open Finset MeasureTheory RHTower
open scoped ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes

/-- The logarithmic coefficient envelope controls energy on every vertical line. -/
theorem convolution_meanSquare_le (k N : ℕ) (d : ℝ) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ τ in T₁..T₂,
      ‖edPoly (fun n => (((Λ ^ k) n : ℝ) : ℂ)) (Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      (T₂ - T₁ + 8 * N * (1 + Real.log N)) *
        ∑ n ∈ Icc 1 N, Real.log n ^ (2 * k) * (n : ℝ) ^ (2 * d - 1) := by
  refine (integral_normSq_edPoly_displaced_le d _ N T₁ T₂).trans ?_
  have hlen : 0 ≤ T₂ - T₁ + 8 * N * (1 + Real.log N) :=
    add_nonneg (sub_nonneg.mpr hT)
      (mul_nonneg (by positivity) (add_nonneg zero_le_one (Real.log_natCast_nonneg N)))
  apply mul_le_mul_of_nonneg_left _ hlen
  apply sum_le_sum
  intro n _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (convolution_sq_le_log_pow k n)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- At the critical line the coefficient energy has at most logarithmic growth. -/
theorem convolution_critical_energy_le (k N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, ((Λ ^ k) n) ^ 2 / n ≤
      Real.log N ^ (2 * k) * (1 + Real.log N) := by
  calc
    ∑ n ∈ Icc 1 N, ((Λ ^ k) n) ^ 2 / n ≤
        ∑ n ∈ Icc 1 N, Real.log N ^ (2 * k) * (1 / n) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlog := Real.log_le_log hn0 (show (n : ℝ) ≤ N by exact_mod_cast hnN)
      rw [div_eq_mul_inv, one_div]
      exact mul_le_mul_of_nonneg_right
        ((convolution_sq_le_log_pow k n).trans
          (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog _)) (inv_nonneg.mpr hn0.le)
    _ = Real.log N ^ (2 * k) * ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_Icc_le_one_add_log N hN) (by positivity)

/-- A finite mean-square estimate for every logarithmic-derivative power. -/
theorem convolution_critical_meanSquare_le (k N : ℕ) (hN : 1 ≤ N)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ τ in T₁..T₂,
      ‖edPoly (fun n => (((Λ ^ k) n : ℝ) : ℂ)) (Icc 1 N) (displacedLinePt 0 τ)‖ ^ 2) ≤
      (T₂ - T₁ + 8 * N * (1 + Real.log N)) *
        (Real.log N ^ (2 * k) * (1 + Real.log N)) := by
  have h := integral_normSq_edPoly_displaced_le 0 (fun n => (((Λ ^ k) n : ℝ) : ℂ)) N T₁ T₂
  simp only [mul_zero, zero_sub, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, ← div_eq_mul_inv] at h
  refine h.trans (mul_le_mul_of_nonneg_left (convolution_critical_energy_le k N hN) ?_)
  exact add_nonneg (sub_nonneg.mpr hT)
    (mul_nonneg (by positivity) (add_nonneg zero_le_one (Real.log_natCast_nonneg N)))

#print axioms convolution_meanSquare_le
#print axioms convolution_critical_meanSquare_le

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes
