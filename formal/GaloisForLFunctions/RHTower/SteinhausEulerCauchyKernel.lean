import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import GaloisForLFunctions.HTGeometry.CauchyKernelFourier
import GaloisForLFunctions.RHTower.SteinhausEulerSmoothSeries
import Mathlib.Probability.Distributions.Cauchy

open MeasureTheory Complex

noncomputable section
namespace RHTower

local notation "ν" => ProbabilityTheory.cauchyMeasure (0 : ℝ) (1 / 2)

/-- Fourier transform of the precise half-scale Cauchy measure used by the critical energy. -/
theorem integral_halfCauchy_character (L : ℝ) :
    (∫ t : ℝ, Complex.exp (((-(L * t) : ℝ) : ℂ) * I) ∂ν) =
      ((Real.exp (-((1 / 2 : ℝ) * |L|)) : ℝ) : ℂ) := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (ProbabilityTheory.measurable_cauchyPDF 0 (1 / 2))
    (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  have hpoint (t : ℝ) :
      (ProbabilityTheory.cauchyPDF 0 (1 / 2) t).toReal •
          Complex.exp (((-(L * t) : ℝ) : ℂ) * I) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (((((1 / 2 : ℝ) ^ (2 : ℕ) + t ^ (2 : ℕ) : ℝ) : ℂ)⁻¹) *
            Complex.exp (((-(L * t) : ℝ) : ℂ) * I)) := by
    rw [ProbabilityTheory.cauchyPDF_def,
      ENNReal.toReal_ofReal (ProbabilityTheory.cauchyPDF_pos 0 (by norm_num) t).le,
      Complex.real_smul]
    norm_num [ProbabilityTheory.cauchyPDFReal]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_mul_cexp_neg (by norm_num)]
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- The exact Mellin pair kernel: the Cauchy average is the reciprocal maximum. -/
theorem integral_halfCauchy_criticalPower_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ, (a : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)) *
        (starRingEnd ℂ) ((b : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) ∂ν) =
      (((max a b)⁻¹ : ℝ) : ℂ) := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpoint (t : ℝ) : (a : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)) *
        (starRingEnd ℂ) ((b : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) =
      ((Real.exp (-(Real.log a + Real.log b) / 2) : ℝ) : ℂ) *
        Complex.exp (((-((Real.log a - Real.log b) * t) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hac, Complex.cpow_def_of_ne_zero hbc,
      ← Complex.exp_conj, ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le,
      Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp
    rw [Complex.conj_ofNat]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_halfCauchy_character, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_add]
  have hexp : -(Real.log a + Real.log b) / 2 +
      -((1 / 2 : ℝ) * |Real.log a - Real.log b|) = -Real.log (max a b) := by
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab)), max_eq_right hab]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba)), max_eq_left hba]
      ring
  rw [hexp, Real.exp_neg, Real.exp_log (ha.trans_le (le_max_left a b))]

end RHTower
