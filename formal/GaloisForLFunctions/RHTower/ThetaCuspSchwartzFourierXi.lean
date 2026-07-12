import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.XiSchwartzSpectralMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

theorem integral_eq_integral_Ioi_add_reflect
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, f x) = ∫ x : ℝ in Ioi 0, (f x + f (-x)) := by
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  simp only [compl_Ioi] at hsplit
  have hneg : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
  rw [← hsplit, hneg, ← integral_add hf.integrableOn hf.comp_neg.integrableOn]

theorem fourier_thetaCuspSchwartz_scaled (t : ℝ) :
    (𝓕 thetaCuspSchwartz) (t / (2 * Real.pi)) = XiC (t : ℂ) := by
  change FourierTransform.fourier (fun x : ℝ => thetaCuspSchwartz x)
    (t / (2 * Real.pi)) = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [XiC_ofReal_eq_two_mul_thetaCuspCosine]
  let F : ℝ → ℂ := fun x =>
    Complex.exp (((-t * x : ℝ) : ℂ) * I) * (thetaCuspFullSource x : ℂ)
  have hfun : (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * v * (t / (2 * Real.pi))) * I) •
        thetaCuspSchwartz v) = F := by
    funext v
    rw [thetaCuspSchwartz_apply]
    change Complex.exp (↑(-2 * Real.pi * v * (t / (2 * Real.pi))) * I) *
        (thetaCuspFullSource v : ℂ) = _
    congr 2
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hfun]
  have hPhi : Integrable (fun x : ℝ => (thetaCuspFullSource x : ℂ)) := by
    simpa only [thetaCuspSchwartz_apply] using
      (thetaCuspSchwartz.integrable (μ := (volume : Measure ℝ)))
  have hF : Integrable F := by
    apply hPhi.bdd_mul (c := 1)
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp (((-t * x : ℝ) : ℂ) * I))).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp
  rw [integral_eq_integral_Ioi_add_reflect hF]
  rw [← integral_const_mul]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [F]
  rw [thetaCuspFullSource_neg]
  rw [show -t * -x = t * x by ring, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I]
  rw [show -t * x = -(t * x) by ring, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

def twoPiScale : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (2 * Real.pi) (mul_ne_zero (by norm_num) Real.pi_ne_zero))

def xiThetaSchwartzSource : 𝓢(ℝ, ℂ) :=
  (2 * Real.pi : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ twoPiScale thetaCuspSchwartz

@[simp] theorem xiThetaSchwartzSource_apply (x : ℝ) :
    xiThetaSchwartzSource x =
      (2 * Real.pi : ℂ) * thetaCuspFullSource ((2 * Real.pi) * x) := by
  rfl

theorem fourier_xiThetaSchwartzSource (t : ℝ) :
    (𝓕 xiThetaSchwartzSource) t = XiC (t : ℂ) := by
  change FourierTransform.fourier (fun x : ℝ => xiThetaSchwartzSource x) t = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  let G : ℝ → ℂ := fun y =>
    Complex.exp (((-y * t : ℝ) : ℂ) * I) * (thetaCuspFullSource y : ℂ)
  have hfun : (fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * t) * I) • xiThetaSchwartzSource x) =
      fun x => (2 * Real.pi : ℂ) * G ((2 * Real.pi) * x) := by
    funext x
    rw [xiThetaSchwartzSource_apply]
    change Complex.exp (↑(-2 * Real.pi * x * t) * I) *
        ((2 * Real.pi : ℂ) * thetaCuspFullSource ((2 * Real.pi) * x)) = _
    dsimp [G]
    have hphase : Complex.exp (↑(-2 * Real.pi * x * t) * I) =
        Complex.exp (↑(-((2 * Real.pi) * x) * t) * I) := by
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  rw [hfun, integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_left G (2 * Real.pi)]
  have hscale : |((2 * Real.pi)⁻¹)| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [hscale]
  change (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) • (∫ y : ℝ, G y)) = _
  rw [real_smul]
  have hcancel : (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hcancel, one_mul]
  calc
    (∫ y : ℝ, G y) =
        FourierTransform.fourier (fun x : ℝ => thetaCuspSchwartz x)
          (t / (2 * Real.pi)) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaCuspSchwartz_apply]
      change G x = Complex.exp
        (↑(-2 * Real.pi * x * (t / (2 * Real.pi))) * I) *
          (thetaCuspFullSource x : ℂ)
      dsimp [G]
      congr 2
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = XiC (t : ℂ) := fourier_thetaCuspSchwartz_scaled t

theorem spectralMeasureForm_xiThetaSchwartzSource_self_eq_integral_xiRealNormSq
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    SchwartzMap.spectralMeasureForm μ xiThetaSchwartzSource xiThetaSchwartzSource =
      ∫ t, (xiRealNormSq t : ℂ) ∂μ :=
  spectralMeasureForm_self_eq_integral_xiRealNormSq μ xiThetaSchwartzSource
    fourier_xiThetaSchwartzSource

theorem spectralMeasure_eq_sum_smul_dirac_xiRealZeroSet_of_null_xiThetaSchwartzSource
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (hnull : SchwartzMap.spectralMeasureForm μ
      xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    μ = Measure.sum
      (fun t : xiRealZeroSet => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) :=
  spectralMeasure_eq_sum_smul_dirac_xiRealZeroSet_of_null_source
    μ xiThetaSchwartzSource fourier_xiThetaSchwartzSource hnull

end RHTower
