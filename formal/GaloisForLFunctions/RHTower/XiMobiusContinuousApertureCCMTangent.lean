import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.RHTower.CCMComplexMellinColligation

/-!
# The continuous Möbius aperture tangent is the CCM Cauchy colligation

The small-aperture tangent of the actual Möbius--Szegő source metric is the derivative-dressed
Cauchy kernel `a*b/(a+b)`.  The complex CCM polar--prime identity already resolves the undressed
Cauchy coordinate into the von Mangoldt, shifted-polar, and critical Mellin-defect channels.

This file joins those two exact theorems.  It identifies the canonical infinitesimal RH interface:
after source differentiation, the only signed channel left to control is the existing critical
Mellin defect.  No zero-location hypothesis or positivity claim is introduced here.
-/

namespace RHTower

noncomputable section

/-- The scalar Cauchy tangent before multiplication by the global Möbius slope constant. -/
def xiMobiusContinuousApertureCauchyTangent (a b : ℝ) : ℂ :=
  ((a * b / (a + b) : ℝ) : ℂ)

/-- **Exact CCM tangent colligation.**  The infinitesimal true-aperture source kernel is the
derivative dressing of the actual polar--prime critical Mellin colligation. -/
theorem xiMobiusContinuousApertureCauchyTangent_eq_ccm
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    xiMobiusContinuousApertureCauchyTangent a b =
      ((a * b : ℝ) : ℂ) *
        (vonMangoldtPrimeLaplaceChannelComplex (((a + b : ℝ) : ℂ)) -
          1 / (((a + b : ℝ) : ℂ) + 1) +
          criticalMellinDefectLaplaceChannelComplex (((a + b : ℝ) : ℂ))) := by
  have hab : 0 < a + b := add_pos ha hb
  have hccm := cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex
    (s := (((a + b : ℝ) : ℂ))) (by simpa using hab)
  calc
    xiMobiusContinuousApertureCauchyTangent a b =
        ((a * b : ℝ) : ℂ) * (1 / (((a + b : ℝ) : ℂ))) := by
      simp only [xiMobiusContinuousApertureCauchyTangent]
      push_cast
      field_simp [hab.ne']
    _ = ((a * b : ℝ) : ℂ) *
        (vonMangoldtPrimeLaplaceChannelComplex (((a + b : ℝ) : ℂ)) -
          1 / (((a + b : ℝ) : ℂ) + 1) +
          criticalMellinDefectLaplaceChannelComplex (((a + b : ℝ) : ℂ))) := by
      rw [hccm]

/-- The full source tangent, including its finite positive prime constant, has the same exact CCM
resolution. -/
theorem xiMobiusContinuousApertureSlopeKernel_eq_ccm
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((xiMobiusContinuousApertureSlopeConstant * (a * b / (a + b)) : ℝ) : ℂ) =
      (xiMobiusContinuousApertureSlopeConstant : ℂ) * ((a * b : ℝ) : ℂ) *
        (vonMangoldtPrimeLaplaceChannelComplex (((a + b : ℝ) : ℂ)) -
          1 / (((a + b : ℝ) : ℂ) + 1) +
          criticalMellinDefectLaplaceChannelComplex (((a + b : ℝ) : ℂ))) := by
  rw [show ((xiMobiusContinuousApertureSlopeConstant * (a * b / (a + b)) : ℝ) : ℂ) =
      (xiMobiusContinuousApertureSlopeConstant : ℂ) *
        xiMobiusContinuousApertureCauchyTangent a b by
    simp [xiMobiusContinuousApertureCauchyTangent]]
  rw [xiMobiusContinuousApertureCauchyTangent_eq_ccm ha hb]
  ring

/-- The source-prescribed four-unit tangent has the same channel resolution, now with the universal
coefficient eight. -/
theorem xiMobiusContinuousApertureFourUnitTangentKernel_eq_ccm
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (xiMobiusContinuousApertureFourUnitTangentKernel a b : ℂ) =
      (8 : ℂ) * ((a * b : ℝ) : ℂ) *
        (vonMangoldtPrimeLaplaceChannelComplex (((a + b : ℝ) : ℂ)) -
          1 / (((a + b : ℝ) : ℂ) + 1) +
          criticalMellinDefectLaplaceChannelComplex (((a + b : ℝ) : ℂ))) := by
  rw [show (xiMobiusContinuousApertureFourUnitTangentKernel a b : ℂ) =
      (8 : ℂ) * xiMobiusContinuousApertureCauchyTangent a b by
    simp [xiMobiusContinuousApertureFourUnitTangentKernel,
      xiMobiusContinuousApertureCauchyTangent]
    ring]
  rw [xiMobiusContinuousApertureCauchyTangent_eq_ccm ha hb]
  ring

end

end RHTower
