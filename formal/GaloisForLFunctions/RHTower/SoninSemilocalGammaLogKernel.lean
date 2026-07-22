import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open Complex MeasureTheory Real Set
open scoped FourierTransform

namespace RHTower

def semilocalGammaLogKernel (a x : ℝ) : ℂ :=
  (Real.exp (-a * x) * Real.exp (-Real.exp (-x)) : ℝ)

theorem continuous_semilocalGammaLogKernel (a : ℝ) :
    Continuous (semilocalGammaLogKernel a) := by
  unfold semilocalGammaLogKernel
  fun_prop

theorem norm_semilocalGammaLogKernel (a x : ℝ) :
    ‖semilocalGammaLogKernel a x‖ =
      Real.exp (-a * x) * Real.exp (-Real.exp (-x)) := by
  unfold semilocalGammaLogKernel
  exact Complex.norm_of_nonneg (by positivity)

/-- Dropping the superexponential factor gives a global exponential majorant. -/
theorem norm_semilocalGammaLogKernel_le_of_nonneg
    {a x : ℝ} :
    ‖semilocalGammaLogKernel a x‖ ≤ Real.exp (-a * x) := by
  rw [norm_semilocalGammaLogKernel]
  have hfactor : Real.exp (-Real.exp (-x)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Real.exp_pos _).le)
  nlinarith [Real.exp_pos (-a * x)]

theorem norm_semilocalGammaLogKernel_le_of_nonpos
    (a x : ℝ) :
    ‖semilocalGammaLogKernel a x‖ ≤ Real.exp ((1 - a) * x) := by
  rw [norm_semilocalGammaLogKernel]
  have hexp : -Real.exp (-x) ≤ x := by
    nlinarith [Real.add_one_le_exp (-x)]
  have hfactor := Real.exp_le_exp.mpr hexp
  calc
    Real.exp (-a * x) * Real.exp (-Real.exp (-x)) ≤
        Real.exp (-a * x) * Real.exp x := by
      gcongr
    _ = Real.exp ((1 - a) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem integrable_semilocalGammaLogKernel
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Integrable (semilocalGammaLogKernel a) := by
  have hleftMajorant :
      IntegrableOn (fun x : ℝ ↦ Real.exp ((1 - a) * x)) (Iic 0) :=
    integrableOn_exp_mul_Iic (sub_pos.mpr ha1) 0
  have hrightMajorant :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-a * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ha0) 0
  have hmeas : AEStronglyMeasurable (semilocalGammaLogKernel a) :=
    (continuous_semilocalGammaLogKernel a).aestronglyMeasurable
  have hleft : IntegrableOn (semilocalGammaLogKernel a) (Iic 0) := by
    refine hleftMajorant.mono' (hmeas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact norm_semilocalGammaLogKernel_le_of_nonpos a x
  have hright : IntegrableOn (semilocalGammaLogKernel a) (Ioi 0) := by
    refine hrightMajorant.mono' (hmeas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_semilocalGammaLogKernel_le_of_nonneg
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hleft.union hright

theorem fourier_semilocalGammaLogKernel
    {a : ℝ} (ha : 0 < a) (y : ℝ) :
    FourierTransform.fourier (semilocalGammaLogKernel a) (y / (2 * Real.pi)) =
      Complex.Gamma (a + y * Complex.I) := by
  rw [Complex.Gamma_eq_integral (by simpa using ha),
    Complex.GammaIntegral_eq_mellin, mellin_eq_fourier]
  have hsource :
      (fun u : ℝ => Real.exp (-((a : ℂ) + (y : ℂ) * Complex.I).re * u) •
        (Real.exp (-Real.exp (-u)) : ℂ)) = semilocalGammaLogKernel a := by
    funext u
    simp [semilocalGammaLogKernel]
  rw [hsource]
  simp

theorem fourier_semilocalGammaLogKernel_frequency
    {a : ℝ} (ha : 0 < a) (xi : ℝ) :
    FourierTransform.fourier (semilocalGammaLogKernel a) xi =
      Complex.Gamma (a + (2 * Real.pi * xi) * Complex.I) := by
  convert fourier_semilocalGammaLogKernel ha (2 * Real.pi * xi) using 1
  · field_simp [Real.pi_ne_zero]
  · push_cast
    rfl

theorem integral_semilocalGammaLogKernel
    {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, semilocalGammaLogKernel a x = Complex.Gamma a := by
  have h := fourier_semilocalGammaLogKernel ha 0
  simpa [Real.fourier_eq] using h

end RHTower
