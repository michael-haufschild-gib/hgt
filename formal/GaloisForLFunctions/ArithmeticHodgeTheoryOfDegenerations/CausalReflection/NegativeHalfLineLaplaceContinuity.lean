import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CausalExponentialLaplaceReflection

/-!
# Laplace continuity on the closed right half-plane

For an actual L¹ profile supported on the negative half-line, every Laplace
weight in the closed right half-plane has modulus at most one on the support.
This supplies both integrability and continuity, including neutral real rates.
-/

noncomputable section
open MeasureTheory Filter Set

namespace GaloisForLFunctions.HTGeometry

/-- The actual Laplace transform of a negative-half-line profile. -/
def negativeHalfLineLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (z * (u : ℂ)) * f u

/-- The entire closed right half-plane shares the original L¹ majorant. -/
theorem norm_negativeHalfLineLaplaceIntegrand_le {f : ℝ → ℂ}
    (hsupport : ∀ u, 0 ≤ u → f u = 0) {z : ℂ} (hz : 0 ≤ z.re) (u : ℝ) :
    ‖Complex.exp (z * (u : ℂ)) * f u‖ ≤ ‖f u‖ := by
  by_cases hu : 0 ≤ u
  · simp only [hsupport u hu, mul_zero, norm_zero, le_refl]
  · rw [norm_mul, Complex.norm_exp]
    have hre : (z * (u : ℂ)).re = z.re * u := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre]
    have he : Real.exp (z.re * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hz (le_of_not_ge hu))
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)

/-- Actual L¹ data admit every Laplace value in the closed right half-plane. -/
theorem integrable_negativeHalfLineLaplace {f : ℝ → ℂ} (hf : Integrable f)
    (hsupport : ∀ u, 0 ≤ u → f u = 0) {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (fun u : ℝ => Complex.exp (z * (u : ℂ)) * f u) := by
  have hm : AEStronglyMeasurable (fun u : ℝ => Complex.exp (z * (u : ℂ)) * f u) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  exact hf.norm.mono' hm (Eventually.of_forall (norm_negativeHalfLineLaplaceIntegrand_le hsupport hz))

/-- Dominated continuity includes the boundary and every neutral kernel rate. -/
theorem continuousOn_negativeHalfLineLaplace {f : ℝ → ℂ} (hf : Integrable f)
    (hsupport : ∀ u, 0 ≤ u → f u = 0) :
    ContinuousOn (negativeHalfLineLaplace f) {z : ℂ | 0 ≤ z.re} := by
  unfold negativeHalfLineLaplace
  apply MeasureTheory.continuousOn_of_dominated (bound := fun u => ‖f u‖)
  · intro z hz
    exact (integrable_negativeHalfLineLaplace hf hsupport hz).aestronglyMeasurable
  · intro z hz
    exact Eventually.of_forall (norm_negativeHalfLineLaplaceIntegrand_le hsupport hz)
  · exact hf.norm
  · exact Eventually.of_forall fun u => (by fun_prop :
      Continuous (fun z : ℂ => Complex.exp (z * (u : ℂ)) * f u)).continuousOn

end GaloisForLFunctions.HTGeometry
