import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsKernel

/-!
# First-order flatness of the critical Gibbs force coefficients

The mean-radius and denominator expansions force zero linear correction
in the shared prefactor. The only first-order profile asymmetry must
therefore come from the radial reciprocal and polynomial residual.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsNormalizer (τ φ : ℝ) : ℝ :=
  2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
def egbFixedChargeAGibbsCriticalNormalizer (φ : ℝ) : ℝ := 12 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)
def egbFixedChargeAGibbsPrefactor (w φ τ : ℝ) : ℝ := egbFixedChargeAMeanRadius w φ τ / egbFixedChargeAGibbsNormalizer τ φ
def egbFixedChargeAGibbsCriticalPrefactor (w φ : ℝ) : ℝ := egbFixedChargeACriticalRadius w φ / egbFixedChargeAGibbsCriticalNormalizer φ

theorem egbFixedChargeAGibbsNormalizer_pos (τ φ : ℝ) : 0 < egbFixedChargeAGibbsNormalizer τ φ := by
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  unfold egbFixedChargeAGibbsNormalizer
  positivity

theorem egbFixedChargeAGibbsCriticalNormalizer_pos (φ : ℝ) : 0 < egbFixedChargeAGibbsCriticalNormalizer φ := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbFixedChargeAGibbsCriticalNormalizer
  positivity

theorem egbFixedChargeAGibbsPrefactor_pos (w φ τ : ℝ) : 0 < egbFixedChargeAGibbsPrefactor w φ τ :=
  div_pos (egbFixedChargeAMeanRadius_pos w φ τ) (egbFixedChargeAGibbsNormalizer_pos τ φ)

theorem egbFixedChargeAGibbsCriticalPrefactor_pos (w φ : ℝ) : 0 < egbFixedChargeAGibbsCriticalPrefactor w φ :=
  div_pos (egbFixedChargeACriticalRadius_pos w φ) (egbFixedChargeAGibbsCriticalNormalizer_pos φ)

theorem egbFixedChargeAMeanDenominator_linear_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanDenominator τ φ - (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanDenominator_quadratic_critical_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanPressureNumerator_linear_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanPressureNumerator τ φ - (3 - 2 * egbFixedChargeACriticalCouplingWeight φ)) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanPressureNumerator_quadratic_critical_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMiddleMeanLinearCombination_difference (τ φ : ℝ) :
    ((2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ) -
      4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ =
      4 * ((egbFixedChargeAMeanPressureNumerator τ φ - (3 - 2 * egbFixedChargeACriticalCouplingWeight φ)) /
        egbCoexistenceASymmetricRatio τ) - 8 * egbCoexistenceASymmetricRatio τ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMiddleMeanLinear
  field_simp <;> ring

theorem egbFixedChargeAMiddleMeanLinearCombination_linear_limit (φ : ℝ) :
    Tendsto (fun τ => ((2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ) -
      4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  simp only [egbFixedChargeAMiddleMeanLinearCombination_difference]
  simpa using ((tendsto_const_nhds (x := (4 : ℝ))).mul (egbFixedChargeAMeanPressureNumerator_linear_limit φ)).sub
    ((tendsto_const_nhds (x := (8 : ℝ))).mul egbCoexistenceASymmetricRatio_critical_limit)

theorem egbFixedChargeAGibbsNormalizer_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsNormalizer τ φ) atBot (𝓝 (egbFixedChargeAGibbsCriticalNormalizer φ)) := by
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanDenominator_critical_limit φ)).mul h2
  have he : 2 * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * (1 + 0 ^ (2 : ℕ)) = egbFixedChargeAGibbsCriticalNormalizer φ := by
    unfold egbFixedChargeAGibbsCriticalNormalizer
    ring
  rw [he] at h
  exact h

theorem egbFixedChargeAGibbsNormalizer_difference (τ φ : ℝ) :
    (egbFixedChargeAGibbsNormalizer τ φ - egbFixedChargeAGibbsCriticalNormalizer φ) / egbCoexistenceASymmetricRatio τ =
      2 * ((egbFixedChargeAMeanDenominator τ φ - (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ +
        egbFixedChargeAMeanDenominator τ φ * egbCoexistenceASymmetricRatio τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAGibbsNormalizer egbFixedChargeAGibbsCriticalNormalizer
  field_simp <;> ring

theorem egbFixedChargeAGibbsNormalizer_linear_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsNormalizer τ φ - egbFixedChargeAGibbsCriticalNormalizer φ) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  simp only [egbFixedChargeAGibbsNormalizer_difference]
  simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul ((egbFixedChargeAMeanDenominator_linear_limit φ).add
    ((egbFixedChargeAMeanDenominator_critical_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit))

theorem egbFixedChargeAGibbsPrefactor_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAGibbsPrefactor w φ) atBot (𝓝 (egbFixedChargeAGibbsCriticalPrefactor w φ)) :=
  (egbFixedChargeAMeanRadius_critical_limit w φ).div (egbFixedChargeAGibbsNormalizer_critical_limit φ)
    (egbFixedChargeAGibbsCriticalNormalizer_pos φ).ne'

theorem egbFixedChargeAGibbsPrefactor_difference (w φ τ : ℝ) :
    (egbFixedChargeAGibbsPrefactor w φ τ - egbFixedChargeAGibbsCriticalPrefactor w φ) / egbCoexistenceASymmetricRatio τ =
      (((egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ) -
        egbFixedChargeAGibbsCriticalPrefactor w φ *
          ((egbFixedChargeAGibbsNormalizer τ φ - egbFixedChargeAGibbsCriticalNormalizer φ) / egbCoexistenceASymmetricRatio τ)) /
        egbFixedChargeAGibbsNormalizer τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hZ := egbFixedChargeAGibbsNormalizer_pos τ φ
  have hZ0 := egbFixedChargeAGibbsCriticalNormalizer_pos φ
  unfold egbFixedChargeAGibbsPrefactor egbFixedChargeAGibbsCriticalPrefactor
  field_simp <;> ring

theorem egbFixedChargeAGibbsPrefactor_linear_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsPrefactor w φ τ - egbFixedChargeAGibbsCriticalPrefactor w φ) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  simp only [egbFixedChargeAGibbsPrefactor_difference]
  simpa only [Pi.div_def, mul_zero, sub_self, zero_div] using ((egbFixedChargeAMeanRadius_linear_critical_limit w φ).sub
    ((tendsto_const_nhds (x := egbFixedChargeAGibbsCriticalPrefactor w φ)).mul (egbFixedChargeAGibbsNormalizer_linear_limit φ))).div
      (egbFixedChargeAGibbsNormalizer_critical_limit φ) (egbFixedChargeAGibbsCriticalNormalizer_pos φ).ne'

end GaloisForLFunctions.HTGeometry
