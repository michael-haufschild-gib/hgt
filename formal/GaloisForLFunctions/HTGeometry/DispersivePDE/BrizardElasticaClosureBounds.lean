import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaClosureFunction
import Mathlib.Tactic

/-!
# Analytic bounds for the closed-knot function

The defining integrands give `E(m) ≥ (1-m)K(m)` throughout the classical range.  This elementary
but useful bound proves, without numerical evaluation, that the paper's vertical-period scale
`Q(m)` is strictly positive on every classical modulus.  Therefore any negative or zero closure
scale is genuinely confined to the extended branch.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem classical_complete_integrand_bound (m : ClassicalModulus) (θ : ℝ) :
    (1 - (m : ℝ)) * completeKIntegrand m θ ≤ completeEIntegrand m θ := by
  have hm0 : 0 < (m : ℝ) := m.property.1
  have hrad : 0 < 1 - (m : ℝ) * Real.sin θ ^ 2 :=
    subcriticalRadicand_pos (classicalAsSubcritical m) θ
  have hs : 0 < Real.sqrt (1 - (m : ℝ) * Real.sin θ ^ 2) :=
    Real.sqrt_pos.mpr hrad
  have hsin : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have hmul : (m : ℝ) * Real.sin θ ^ 2 ≤ (m : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hsin hm0.le
  rw [completeKIntegrand, completeEIntegrand, ← div_eq_mul_inv]
  apply (div_le_iff₀ hs).2
  rw [← sq, Real.sq_sqrt hrad.le]
  linarith

/-- Classical complete-integral comparison used implicitly by the knot parameter range. -/
theorem one_sub_mul_completeK_le_completeE (m : ClassicalModulus) :
    (1 - (m : ℝ)) * completeEllipticK m ≤ completeEllipticE m := by
  have hKcont : Continuous (completeKIntegrand m) := by
    simpa [classicalAsSubcritical] using
      continuous_completeKIntegrand (classicalAsSubcritical m)
  have hEcont : Continuous (completeEIntegrand m) := by
    simpa [classicalAsSubcritical] using
      continuous_completeEIntegrand (classicalAsSubcritical m)
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    ((continuous_const.mul hKcont).intervalIntegrable _ _)
    (hEcont.intervalIntegrable _ _)
    (fun θ _ => classical_complete_integrand_bound m θ)
  simp only [Pi.mul_apply] at h
  rw [intervalIntegral.integral_const_mul] at h
  simpa [completeEllipticK, completeEllipticE, completeKIntegrand,
    completeEIntegrand] using h

/-- `Q(m)` is strictly positive throughout the classical interval `0<m<1`. -/
theorem closureQ_classical_pos (m : ClassicalModulus) : 0 < closureQ m := by
  have hK : 0 < completeEllipticK m := completeEllipticK_classical_pos m
  have hEK := one_sub_mul_completeK_le_completeE m
  have hratio : 1 - (m : ℝ) ≤ completeEllipticE m / completeEllipticK m := by
    exact (le_div_iff₀ hK).2 hEK
  calc
    closureQ m = 2 * (completeEllipticE m / completeEllipticK m) -
        (1 - (m : ℝ)) := by rw [closureQ]; ring
    _ > 0 := by linarith [m.property.2]

/-- Negative closure scale cannot occur on the classical Jacobi branch. -/
theorem closureQ_classical_not_nonpos (m : ClassicalModulus) :
    ¬ closureQ m ≤ 0 := not_le.mpr (closureQ_classical_pos m)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
