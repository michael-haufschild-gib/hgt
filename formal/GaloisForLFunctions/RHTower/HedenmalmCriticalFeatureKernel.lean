import GaloisForLFunctions.RHTower.XiWardCubicTranslationEnergySeparator
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener

/-!
# Reproducing kernel of the Hedenmalm critical rigging

Critical conormal features have an explicit two-sided Laplace kernel.  For strip points `w,z`,
evaluation of the feature centered at `w` is

`2 / (1 + (z - conj w)^2)`.

The open half-strip makes both Laplace rates strict and keeps the denominator nonzero.  In
particular every strip evaluation is seen by every real-centered critical feature.  This removes
an abstract nonvanishing hypothesis from source-energy separators.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile
open GaloisForLFunctions.HTGeometry

def criticalFeatureKernelPlusRate (w z : ℂ) : ℂ :=
  -1 + Complex.I * (z - (starRingEnd ℂ) w)

def criticalFeatureKernelMinusRate (w z : ℂ) : ℂ :=
  1 + Complex.I * (z - (starRingEnd ℂ) w)

theorem criticalFeatureKernelPlusRate_re (w z : ℂ) :
    (criticalFeatureKernelPlusRate w z).re = -1 - z.im - w.im := by
  simp [criticalFeatureKernelPlusRate, Complex.mul_re]
  ring

theorem criticalFeatureKernelMinusRate_re (w z : ℂ) :
    (criticalFeatureKernelMinusRate w z).re = 1 - z.im - w.im := by
  simp [criticalFeatureKernelMinusRate, Complex.mul_re]
  ring

theorem criticalFeatureKernelPlusRate_re_neg {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    (criticalFeatureKernelPlusRate w z).re < 0 := by
  rw [criticalFeatureKernelPlusRate_re]
  rcases abs_lt.mp hw with ⟨hw0, _⟩
  rcases abs_lt.mp hz with ⟨hz0, _⟩
  linarith

theorem criticalFeatureKernelMinusRate_re_pos {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    0 < (criticalFeatureKernelMinusRate w z).re := by
  rw [criticalFeatureKernelMinusRate_re]
  rcases abs_lt.mp hw with ⟨_, hw1⟩
  rcases abs_lt.mp hz with ⟨_, hz1⟩
  linarith

theorem criticalFeatureKernelPlusRate_ne_zero {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    criticalFeatureKernelPlusRate w z ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [criticalFeatureKernelPlusRate_re] at hre
  rcases abs_lt.mp hw with ⟨hw0, _⟩
  rcases abs_lt.mp hz with ⟨hz0, _⟩
  simp at hre
  linarith

theorem criticalFeatureKernelMinusRate_ne_zero {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    criticalFeatureKernelMinusRate w z ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [criticalFeatureKernelMinusRate_re] at hre
  rcases abs_lt.mp hw with ⟨_, hw1⟩
  rcases abs_lt.mp hz with ⟨_, hz1⟩
  simp at hre
  linarith

theorem criticalFeatureRaw_mul_sourceChar_of_nonneg
    (w z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    criticalFeatureRaw w x * sourceChar z x =
      Complex.exp (criticalFeatureKernelPlusRate w z * (x : ℂ)) := by
  rw [criticalFeatureRaw, criticalWeight, sourceChar, sourceChar,
    ← Complex.exp_conj, Complex.ofReal_exp, div_eq_mul_inv,
    ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [abs_of_nonneg hx]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [criticalFeatureKernelPlusRate]
  ring

theorem criticalFeatureRaw_mul_sourceChar_of_nonpos
    (w z : ℂ) {x : ℝ} (hx : x ≤ 0) :
    criticalFeatureRaw w x * sourceChar z x =
      Complex.exp (criticalFeatureKernelMinusRate w z * (x : ℂ)) := by
  rw [criticalFeatureRaw, criticalWeight, sourceChar, sourceChar,
    ← Complex.exp_conj, Complex.ofReal_exp, div_eq_mul_inv,
    ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [abs_of_nonpos hx]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [criticalFeatureKernelMinusRate]
  push_cast
  ring

theorem integral_criticalFeatureRaw_mul_sourceChar {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    (∫ x : ℝ, criticalFeatureRaw w x * sourceChar z x) =
      (criticalFeatureKernelMinusRate w z)⁻¹ -
        (criticalFeatureKernelPlusRate w z)⁻¹ := by
  have hp := criticalFeatureKernelPlusRate_re_neg hw hz
  have hm := criticalFeatureKernelMinusRate_re_pos hw hz
  have hleft : IntegrableOn
      (fun x : ℝ => criticalFeatureRaw w x * sourceChar z x) (Iic 0) := by
    refine IntegrableOn.congr_fun (integrableOn_exp_mul_complex_Iic hm 0)
      (fun x hx => ?_) measurableSet_Iic
    exact (criticalFeatureRaw_mul_sourceChar_of_nonpos w z hx).symm
  have hright : IntegrableOn
      (fun x : ℝ => criticalFeatureRaw w x * sourceChar z x) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_exp_mul_complex_Ioi hp 0)
      (fun x hx => ?_) measurableSet_Ioi
    exact (criticalFeatureRaw_mul_sourceChar_of_nonneg w z hx.le).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright]
  rw [show (∫ x : ℝ in Iic 0, criticalFeatureRaw w x * sourceChar z x) =
      ∫ x : ℝ in Iic 0,
        Complex.exp (criticalFeatureKernelMinusRate w z * (x : ℂ)) by
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    exact criticalFeatureRaw_mul_sourceChar_of_nonpos w z hx]
  rw [show (∫ x : ℝ in Ioi 0, criticalFeatureRaw w x * sourceChar z x) =
      ∫ x : ℝ in Ioi 0,
        Complex.exp (criticalFeatureKernelPlusRate w z * (x : ℂ)) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact criticalFeatureRaw_mul_sourceChar_of_nonneg w z hx.le]
  rw [integral_exp_mul_complex_Iic hm 0,
    integral_exp_mul_complex_Ioi hp 0]
  simp [div_eq_mul_inv]
  abel

theorem criticalFeatureKernelDenominator_ne_zero {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    1 + (z - (starRingEnd ℂ) w) ^ 2 ≠ 0 := by
  have hp := criticalFeatureKernelPlusRate_ne_zero hw hz
  have hm := criticalFeatureKernelMinusRate_ne_zero hw hz
  have hfactor :
      1 + (z - (starRingEnd ℂ) w) ^ 2 =
        -(criticalFeatureKernelMinusRate w z *
          criticalFeatureKernelPlusRate w z) := by
    rw [criticalFeatureKernelMinusRate, criticalFeatureKernelPlusRate]
    ring_nf
    norm_num [Complex.I_sq]
    abel
  rw [hfactor]
  exact neg_ne_zero.mpr (mul_ne_zero hm hp)

theorem criticalFeatureKernel_rate_algebra {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    (criticalFeatureKernelMinusRate w z)⁻¹ -
        (criticalFeatureKernelPlusRate w z)⁻¹ =
      2 / (1 + (z - (starRingEnd ℂ) w) ^ 2) := by
  have hp := criticalFeatureKernelPlusRate_ne_zero hw hz
  have hm := criticalFeatureKernelMinusRate_ne_zero hw hz
  have hden := criticalFeatureKernelDenominator_ne_zero hw hz
  field_simp [hp, hm, hden]
  rw [criticalFeatureKernelMinusRate, criticalFeatureKernelPlusRate]
  ring_nf
  norm_num [Complex.I_sq]
  abel

/-- Explicit reproducing kernel for two arbitrary points of the open critical strip. -/
theorem criticalEvaluation_criticalFeature_eq {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    criticalEvaluation z hz (criticalFeature w hw) =
      2 / (1 + (z - (starRingEnd ℂ) w) ^ 2) := by
  rw [criticalEvaluation_eq_integral]
  calc
    (∫ x : ℝ, (criticalFeature w hw : ℝ → ℂ) x * sourceChar z x) =
        ∫ x : ℝ, criticalFeatureRaw w x * sourceChar z x := by
      apply integral_congr_ae
      have hfeature := (withDensity_realDensity_ae_eq measurable_criticalWeight
        criticalWeight_pos).mp (criticalFeatureRaw_memLp hw).coeFn_toLp
      filter_upwards [hfeature] with x hx
      rw [criticalFeature, hx]
    _ = (criticalFeatureKernelMinusRate w z)⁻¹ -
        (criticalFeatureKernelPlusRate w z)⁻¹ :=
      integral_criticalFeatureRaw_mul_sourceChar hw hz
    _ = 2 / (1 + (z - (starRingEnd ℂ) w) ^ 2) :=
      criticalFeatureKernel_rate_algebra hw hz

theorem criticalEvaluation_criticalFeature_ne_zero {w z : ℂ}
    (hw : |w.im| < 1 / 2) (hz : |z.im| < 1 / 2) :
    criticalEvaluation z hz (criticalFeature w hw) ≠ 0 := by
  rw [criticalEvaluation_criticalFeature_eq hw hz]
  exact div_ne_zero (by norm_num) (criticalFeatureKernelDenominator_ne_zero hw hz)

/-- A real-centered critical feature sees every point of the open critical strip. -/
theorem criticalEvaluation_realCriticalFeature_ne_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    criticalEvaluation z hz
      (criticalFeature (t : ℂ) (by norm_num)) ≠ 0 :=
  criticalEvaluation_criticalFeature_ne_zero (by norm_num) hz

end

end RHTower
