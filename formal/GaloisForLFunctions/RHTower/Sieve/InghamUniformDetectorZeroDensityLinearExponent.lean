import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityUniformPolylog

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Full-strip density with one universal constant, one uniform height threshold, fixed
polylogarithmic loss, and the linear Route-T exponent `16/5 * (1 - sigma)`. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in Filter.atTop,
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 + Real.log (X : ℝ)) ^ (14 : ℕ) *
          (1 +
            (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma)) *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨K, hK, hdensity⟩ :=
    exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformPolylog
  refine ⟨K, hK, ?_⟩
  filter_upwards [hdensity, eventually_ge_atTop (1 : ℕ)] with X hdensityX hX
  intro sigma hsigma0 hsigma1
  let Log : ℝ := 1 + Real.log (X : ℝ)
  let E : ℝ := inghamUniformGabrielConservativeExponent sigma
  let E' : ℝ := (16 / 5 : ℝ) * (1 - sigma)
  let P : ℝ := (X : ℝ) ^ E
  let P' : ℝ := (X : ℝ) ^ E'
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hLog0 : 0 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXR1]
  have hE : E ≤ E' := by
    dsimp only [E, E']
    exact inghamUniformGabrielConservativeExponent_le_sixteen_fifths_mul hsigma1.le
  have hP : P ≤ P' := by
    dsimp only [P, P']
    exact Real.rpow_le_rpow_of_exponent_le hXR1 hE
  have hLogSq0 : 0 ≤ Log ^ (2 : ℕ) := pow_nonneg hLog0 _
  have htail :
      1 + P * Log ^ (2 : ℕ) + Log ^ (2 : ℕ) ≤
        1 + P' * Log ^ (2 : ℕ) + Log ^ (2 : ℕ) := by
    linarith [mul_le_mul_of_nonneg_right hP hLogSq0]
  have hcoeff0 : 0 ≤ K * Log ^ (14 : ℕ) :=
    mul_nonneg hK (pow_nonneg hLog0 _)
  have hbound := mul_le_mul_of_nonneg_left htail hcoeff0
  simpa only [Log, E, E', P, P'] using
    (hdensityX hsigma0 hsigma1).trans hbound

end

end RHTower.Sieve
