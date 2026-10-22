import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmWardGreenCriticalFeatureTrace
import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmAdjacentFeatureKreinIndexSeparator
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Critical-feature Ward--Green Plancherel fracture

Continuous real-centered critical features form an exact Fourier frame for the strip-tilted source
profile. This module compares its Hermitian mass with its holomorphic polarization. The latter is
the constant `2π`; the former is `2π / (1 - Im(z)^(2 : ℕ))`. Thus every transverse signal lies in the
exact excess `2π Im(z)^(2 : ℕ) / (1 - Im(z)^(2 : ℕ))`.

Off the Ward kernel, multiplying this excess by the source Green weight reconstructs the whole
Hermitian mass. On the kernel, totalized Green inversion and the excess both vanish while Hermitian
mass remains `2π`. Consequently continuous positive-frame completion does not manufacture the
missing arithmetic same-copy trace: it reconstructs nonholomorphic mass from precisely the
fracture that prime--Gamma holomorphic polarization cannot see.

Integrating one five-shift Ward--Green copy over the complete frame also erases its height. Every
strict-right copy nevertheless deposits at least `2π/81` total charge. This is the strongest
positive survivor of the continuous-frame attempt and an exact no-go for using full-orbit
Plancherel as Route P's arithmetic producer.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open FourierTransform HedenmalmThetaSource HedenmalmQuantile
open GaloisForLFunctions.HTGeometry

def criticalFeatureFrameSourceProfile (z : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-|x|) : ℂ) * sourceChar z x

theorem continuous_criticalFeatureFrameSourceProfile (z : ℂ) :
    Continuous (criticalFeatureFrameSourceProfile z) := by
  unfold criticalFeatureFrameSourceProfile
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (continuous_sourceChar z)

theorem norm_criticalFeatureFrameSourceProfile (z : ℂ) (x : ℝ) :
    ‖criticalFeatureFrameSourceProfile z x‖ =
      Real.exp (-|x| - z.im * x) := by
  rw [criticalFeatureFrameSourceProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_sourceChar, ← Real.exp_add]
  congr 1
  ring

theorem integrable_criticalFeatureFrameSourceProfile
    {z : ℂ} (hz : |z.im| < 1 / 2) :
    Integrable (criticalFeatureFrameSourceProfile z) := by
  have hc : 0 < 1 - |z.im| := by linarith
  refine Integrable.mono' (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hc)
    (continuous_criticalFeatureFrameSourceProfile z).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_criticalFeatureFrameSourceProfile]
  apply Real.exp_le_exp.mpr
  have hzx : -(z.im * x) ≤ |z.im| * |x| := by
    calc
      -(z.im * x) ≤ |-(z.im * x)| := le_abs_self _
      _ = |z.im| * |x| := by rw [abs_neg, abs_mul]
  linarith

theorem memLp_two_criticalFeatureFrameSourceProfile
    {z : ℂ} (hz : |z.im| < 1 / 2) :
    MemLp (criticalFeatureFrameSourceProfile z) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_criticalFeatureFrameSourceProfile z).aestronglyMeasurable]
  have hc : 0 < 2 * (1 - |z.im|) := by linarith
  refine Integrable.mono' (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hc) ?_ ?_
  · exact ((continuous_criticalFeatureFrameSourceProfile z).norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_criticalFeatureFrameSourceProfile]
    rw [← Real.exp_nat_mul]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hzx : -(z.im * x) ≤ |z.im| * |x| := by
      calc
        -(z.im * x) ≤ |-(z.im * x)| := le_abs_self _
        _ = |z.im| * |x| := by rw [abs_neg, abs_mul]
    calc
      (2 : ℝ) * (-|x| - z.im * x) =
          -2 * |x| + 2 * (-(z.im * x)) := by ring
      _ ≤ -2 * |x| + 2 * (|z.im| * |x|) := by gcongr
      _ = -(2 * (1 - |z.im|) * |x|) := by ring

theorem criticalEvaluation_realCriticalFeature_eq_fourier
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)) =
      𝓕 (criticalFeatureFrameSourceProfile z) (t / (2 * Real.pi)) := by
  rw [criticalEvaluation_eq_integral, Real.fourier_real_eq]
  apply integral_congr_ae
  have hfeature := (withDensity_realDensity_ae_eq measurable_criticalWeight
    criticalWeight_pos).mp
      (criticalFeatureRaw_memLp (z := (t : ℂ)) (by norm_num)).coeFn_toLp
  filter_upwards [hfeature] with x hx
  rw [criticalFeature, hx]
  change criticalFeatureRaw (t : ℂ) x * sourceChar z x =
    (Real.fourierChar (-(x * (t / (2 * Real.pi)))) : ℂ) *
      criticalFeatureFrameSourceProfile z x
  rw [Real.fourierChar_apply]
  unfold criticalFeatureRaw criticalWeight criticalFeatureFrameSourceProfile sourceChar
  have harg : ((2 * Real.pi * (-(x * (t / (2 * Real.pi)))) : ℝ) : ℂ) =
      -((x : ℂ) * (t : ℂ)) := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [harg, Complex.ofReal_exp]
  have hweight : (Complex.exp ((|x| : ℝ) : ℂ))⁻¹ =
      Complex.exp (((-|x| : ℝ) : ℂ)) := by
    rw [← Complex.exp_neg]
    congr 2
    norm_num
  rw [div_eq_mul_inv]
  simp_rw [Complex.ofReal_exp]
  rw [hweight]
  have hconj :
      (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
        Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 2
    simp
    ring
  rw [hconj]
  ring

/-- Continuous real-centered critical features are the angular-frequency Plancherel frame of the
fixed strip-tilted source profile. -/
theorem integral_normSq_criticalEvaluation_realCriticalFeature_eq_sourceEnergy
    (z : ℂ) (hz : |z.im| < 1 / 2) :
    (∫ t : ℝ,
      Complex.normSq
        (criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)))) =
      2 * Real.pi *
        ∫ x : ℝ, ‖criticalFeatureFrameSourceProfile z x‖ ^ (2 : ℕ) := by
  let H : ℝ → ℝ := fun ξ => ‖𝓕 (criticalFeatureFrameSourceProfile z) ξ‖ ^ (2 : ℕ)
  have hline : (fun t : ℝ =>
      Complex.normSq
        (criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)))) =
      fun t : ℝ => H (t / (2 * Real.pi)) := by
    funext t
    rw [criticalEvaluation_realCriticalFeature_eq_fourier,
      Complex.normSq_eq_norm_sq]
  rw [hline]
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  rw [hscale, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  simp only [smul_eq_mul]
  rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    (integrable_criticalFeatureFrameSourceProfile hz)
    (memLp_two_criticalFeatureFrameSourceProfile hz)]

theorem fourier_criticalFeatureFrameSourceProfile_conj
    (z : ℂ) (hz : |z.im| < 1 / 2) (ξ : ℝ) :
    𝓕 (criticalFeatureFrameSourceProfile ((starRingEnd ℂ) z)) ξ =
      (starRingEnd ℂ) (𝓕 (criticalFeatureFrameSourceProfile z) ξ) := by
  let t : ℝ := 2 * Real.pi * ξ
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  have hc := criticalEvaluation_realCriticalFeature_conj_eq t hz
  dsimp only at hc
  rw [criticalEvaluation_realCriticalFeature_eq_fourier t ((starRingEnd ℂ) z) hzc,
    criticalEvaluation_realCriticalFeature_eq_fourier t z hz] at hc
  have ht : t / (2 * Real.pi) = ξ := by
    dsimp [t]
    field_simp [Real.pi_ne_zero]
  simpa only [ht] using hc

theorem conj_criticalFeatureFrameSourceProfile_conj
    (z : ℂ) (x : ℝ) :
    (starRingEnd ℂ)
        (criticalFeatureFrameSourceProfile ((starRingEnd ℂ) z) x) =
      criticalFeatureFrameSourceProfile z (-x) := by
  unfold criticalFeatureFrameSourceProfile
  rw [map_mul, Complex.conj_ofReal, abs_neg]
  congr 1
  unfold sourceChar
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem criticalFeatureFrameSourceProfile_neg_mul_self
    (z : ℂ) (x : ℝ) :
    criticalFeatureFrameSourceProfile z (-x) *
        criticalFeatureFrameSourceProfile z x =
      (Real.exp (-2 * |x|) : ℂ) := by
  have hchar : sourceChar z (-x) * sourceChar z x = 1 := by
    unfold sourceChar
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  unfold criticalFeatureFrameSourceProfile
  rw [abs_neg]
  rw [show
      ((Real.exp (-|x|) : ℝ) : ℂ) * sourceChar z (-x) *
          (((Real.exp (-|x|) : ℝ) : ℂ) * sourceChar z x) =
        (((Real.exp (-|x|) : ℝ) : ℂ) * ((Real.exp (-|x|) : ℝ) : ℂ)) *
          (sourceChar z (-x) * sourceChar z x) by ring,
    hchar, mul_one]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Holomorphic Plancherel polarization of one strip profile is independent of transverse
displacement. -/
theorem integral_fourier_criticalFeatureFrameSourceProfile_sq
    (z : ℂ) (hz : |z.im| < 1 / 2) :
    (∫ ξ : ℝ,
      𝓕 (criticalFeatureFrameSourceProfile z) ξ *
        𝓕 (criticalFeatureFrameSourceProfile z) ξ) = 1 := by
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  let f : Lp ℂ 2 (volume : Measure ℝ) :=
    (memLp_two_criticalFeatureFrameSourceProfile hzc).toLp
      (criticalFeatureFrameSourceProfile ((starRingEnd ℂ) z))
  let g : Lp ℂ 2 (volume : Measure ℝ) :=
    (memLp_two_criticalFeatureFrameSourceProfile hz).toLp
      (criticalFeatureFrameSourceProfile z)
  have hfFourier : ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (criticalFeatureFrameSourceProfile ((starRingEnd ℂ) z)) := by
    exact GaloisForLFunctions.RHTower.coeFn_fourier_toLp
      (integrable_criticalFeatureFrameSourceProfile hzc)
      (memLp_two_criticalFeatureFrameSourceProfile hzc)
  have hgFourier : ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (criticalFeatureFrameSourceProfile z) := by
    exact GaloisForLFunctions.RHTower.coeFn_fourier_toLp
      (integrable_criticalFeatureFrameSourceProfile hz)
      (memLp_two_criticalFeatureFrameSourceProfile hz)
  have hfSource : ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      criticalFeatureFrameSourceProfile ((starRingEnd ℂ) z) :=
    (memLp_two_criticalFeatureFrameSourceProfile hzc).coeFn_toLp
  have hgSource : ((g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      criticalFeatureFrameSourceProfile z :=
    (memLp_two_criticalFeatureFrameSourceProfile hz).coeFn_toLp
  calc
    (∫ ξ : ℝ,
        𝓕 (criticalFeatureFrameSourceProfile z) ξ *
          𝓕 (criticalFeatureFrameSourceProfile z) ξ) =
        ∫ ξ : ℝ,
          inner ℂ ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ)
            ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) ξ) := by
      apply integral_congr_ae
      filter_upwards [hfFourier, hgFourier] with ξ hfξ hgξ
      rw [RCLike.inner_apply, hfξ, hgξ,
        fourier_criticalFeatureFrameSourceProfile_conj z hz ξ]
      simp
    _ = inner ℂ (𝓕 f : Lp ℂ 2 (volume : Measure ℝ))
          (𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) := by
      rw [MeasureTheory.L2.inner_def]
    _ = inner ℂ f g := by rw [Lp.inner_fourier_eq]
    _ = ∫ x : ℝ,
          criticalFeatureFrameSourceProfile z (-x) *
            criticalFeatureFrameSourceProfile z x := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfSource, hgSource] with x hfx hgx
      rw [RCLike.inner_apply, hfx, hgx,
        conj_criticalFeatureFrameSourceProfile_conj]
      ring
    _ = ∫ x : ℝ, (Real.exp (-2 * |x|) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [criticalFeatureFrameSourceProfile_neg_mul_self]
    _ = 1 := by
      rw [integral_complex_ofReal]
      have hmoment := HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0
        (by norm_num : (0 : ℝ) < 2)
      norm_cast
      norm_num at hmoment ⊢
      simpa only [zero_mul, pow_zero, one_mul] using hmoment

/-- The holomorphic continuous-frame polarization is the constant `2π` throughout the strip. -/
theorem integral_criticalEvaluation_realCriticalFeature_sq
    (z : ℂ) (hz : |z.im| < 1 / 2) :
    (∫ t : ℝ,
      criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)) ^ (2 : ℕ)) =
      (2 * Real.pi : ℝ) := by
  let H : ℝ → ℂ := fun ξ =>
    𝓕 (criticalFeatureFrameSourceProfile z) ξ *
      𝓕 (criticalFeatureFrameSourceProfile z) ξ
  have hline : (fun t : ℝ =>
      criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)) ^ (2 : ℕ)) =
      fun t : ℝ => H (t / (2 * Real.pi)) := by
    funext t
    rw [criticalEvaluation_realCriticalFeature_eq_fourier]
    dsimp [H]
    rw [pow_two]
  rw [hline]
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  rw [hscale, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [integral_fourier_criticalFeatureFrameSourceProfile_sq z hz]
  rw [Complex.real_smul]
  push_cast
  ring

theorem integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_ne_zero
    (z : ℂ) (hz : |z.im| < 1 / 2) (hy : z.im ≠ 0) :
    (∫ t : ℝ,
      Complex.normSq
        (HedenmalmThetaSource.criticalEvaluation z hz
          (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)))) =
      2 * Real.pi / (1 - z.im ^ (2 : ℕ)) := by
  let y : ℝ := z.im
  let a : ℝ := 1 - y
  let b : ℝ := 1 + y
  let g : ℝ → ℝ := fun u =>
    4 / ((a ^ (2 : ℕ) + u ^ (2 : ℕ)) * (b ^ (2 : ℕ) + u ^ (2 : ℕ)))
  have ha : 0 < a := by
    dsimp [a, y]
    linarith [(abs_lt.mp hz).2]
  have hb : 0 < b := by
    dsimp [b, y]
    linarith [(abs_lt.mp hz).1]
  have hy' : y ≠ 0 := by simpa only [y] using hy
  have hkernel : (fun t : ℝ =>
      Complex.normSq
        (HedenmalmThetaSource.criticalEvaluation z hz
          (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)))) =
      fun t => g (t - z.re) := by
    funext t
    rw [normSq_criticalEvaluation_realCriticalFeature_eq t hz]
    dsimp only [g, a, b, y]
    congr 1
    ring
  have hpartial : g = fun u =>
      y⁻¹ * ((a ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹ - (b ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹) := by
    funext u
    dsimp only [g]
    have hda : a ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
    have hdb : b ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
    field_simp
    dsimp only [a, b]
    ring
  rw [hkernel, integral_sub_right_eq_self g z.re, hpartial,
    integral_const_mul]
  rw [integral_sub (HTGeometry.integrable_inv_sq_add_sq ha)
    (HTGeometry.integrable_inv_sq_add_sq hb),
    integral_inv_sq_add_sq_univ ha,
    integral_inv_sq_add_sq_univ hb]
  dsimp only [a, b, y]
  have hza : 1 - z.im ≠ 0 := by linarith [ha]
  have hzb : 1 + z.im ≠ 0 := by linarith [hb]
  have hzden : 1 - z.im ^ (2 : ℕ) ≠ 0 := by
    have hyabs := abs_lt.mp hz
    nlinarith [sq_nonneg (z.im - 1 / 2), sq_nonneg (z.im + 1 / 2)]
  field_simp [hy, hza, hzb, hzden]
  ring

theorem integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_eq_zero
    (z : ℂ) (hz : |z.im| < 1 / 2) (hy : z.im = 0) :
    (∫ t : ℝ,
      Complex.normSq
        (criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)))) =
      2 * Real.pi := by
  rw [integral_normSq_criticalEvaluation_realCriticalFeature_eq_sourceEnergy]
  have hprofile : (fun x : ℝ => ‖criticalFeatureFrameSourceProfile z x‖ ^ (2 : ℕ)) =
      fun x : ℝ => Real.exp (-2 * |x|) := by
    funext x
    rw [norm_criticalFeatureFrameSourceProfile, hy, zero_mul, sub_zero,
      ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hprofile]
  have hmoment := HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0
    (by norm_num : (0 : ℝ) < 2)
  have hexp : (∫ x : ℝ, Real.exp (-2 * |x|)) = 1 := by
    norm_num at hmoment ⊢
    simpa only [zero_mul, pow_zero, one_mul] using hmoment
  rw [hexp]
  ring

/-- Exact Hermitian continuous-frame mass on the entire critical strip. -/
theorem integral_normSq_criticalEvaluation_realCriticalFeature_eq
    (z : ℂ) (hz : |z.im| < 1 / 2) :
    (∫ t : ℝ,
      Complex.normSq
        (criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)))) =
      2 * Real.pi / (1 - z.im ^ (2 : ℕ)) := by
  by_cases hy : z.im = 0
  · rw [integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_eq_zero
      z hz hy, hy]
    norm_num
  · exact integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_ne_zero
      z hz hy

/-- Non-holomorphic excess of the Hermitian frame row over its holomorphic polarization. -/
def criticalFeatureContinuousFrameHermitianExcess
    (z : ℂ) (hz : |z.im| < 1 / 2) : ℝ :=
  (∫ t : ℝ,
      Complex.normSq
        (criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)))) -
    (∫ t : ℝ,
      criticalEvaluation z hz (criticalFeature (t : ℂ) (by norm_num)) ^ (2 : ℕ)).re

/-- Exact Hermitian/holomorphic fracture: transverse displacement is the entire excess. -/
theorem criticalFeatureContinuousFrameHermitianExcess_eq_of_im_ne_zero
    (z : ℂ) (hz : |z.im| < 1 / 2) (hy : z.im ≠ 0) :
    criticalFeatureContinuousFrameHermitianExcess z hz =
      2 * Real.pi * z.im ^ (2 : ℕ) / (1 - z.im ^ (2 : ℕ)) := by
  rw [criticalFeatureContinuousFrameHermitianExcess,
    integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_ne_zero z hz hy,
    integral_criticalEvaluation_realCriticalFeature_sq z hz]
  simp only [Complex.ofReal_re]
  have hden : 1 - z.im ^ (2 : ℕ) ≠ 0 := by
    have hyabs := abs_lt.mp hz
    nlinarith [sq_nonneg (z.im - 1 / 2), sq_nonneg (z.im + 1 / 2)]
  field_simp [hden]
  ring

/-- Exact fracture law on the whole strip, including its zero locus on the critical line. -/
theorem criticalFeatureContinuousFrameHermitianExcess_eq
    (z : ℂ) (hz : |z.im| < 1 / 2) :
    criticalFeatureContinuousFrameHermitianExcess z hz =
      2 * Real.pi * z.im ^ (2 : ℕ) / (1 - z.im ^ (2 : ℕ)) := by
  rw [criticalFeatureContinuousFrameHermitianExcess,
    integral_normSq_criticalEvaluation_realCriticalFeature_eq z hz,
    integral_criticalEvaluation_realCriticalFeature_sq z hz]
  simp only [Complex.ofReal_re]
  have hden : 1 - z.im ^ (2 : ℕ) ≠ 0 := by
    have hyabs := abs_lt.mp hz
    nlinarith [sq_nonneg (z.im - 1 / 2), sq_nonneg (z.im + 1 / 2)]
  field_simp [hden]
  ring

/-- Off the Ward kernel, Green inversion of the Hermitian/holomorphic fracture reconstructs the
whole Hermitian continuous-frame mass. It does not create an independently source-evaluable
quantity. -/
theorem wardGreen_mul_criticalFeatureContinuousFrameHermitianExcess_eq
    (q : XiZeroCopy) (hy : (xiSpectralPoint q).im ≠ 0) :
    thetaXiWardTransverseGreenWeight q *
        criticalFeatureContinuousFrameHermitianExcess
          (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) =
      ∫ t : ℝ,
        Complex.normSq
          (criticalEvaluation (xiSpectralPoint q)
            (abs_xiSpectralPoint_im_lt_half q)
            (criticalFeature (t : ℂ) (by norm_num))) := by
  rw [thetaXiWardTransverseGreenWeight_eq,
    criticalFeatureContinuousFrameHermitianExcess_eq_of_im_ne_zero
      (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) hy,
    integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_ne_zero
      (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) hy]
  have hden : 1 - (xiSpectralPoint q).im ^ (2 : ℕ) ≠ 0 := by
    have hyabs := abs_lt.mp (abs_xiSpectralPoint_im_lt_half q)
    nlinarith [sq_nonneg ((xiSpectralPoint q).im - 1 / 2),
      sq_nonneg ((xiSpectralPoint q).im + 1 / 2)]
  field_simp [hy, hden]

/-- The same reconstruction has explicit source energy `2π/(1-y²)`. -/
theorem wardGreen_mul_criticalFeatureContinuousFrameHermitianExcess_eq_sourceEnergy
    (q : XiZeroCopy) (hy : (xiSpectralPoint q).im ≠ 0) :
    thetaXiWardTransverseGreenWeight q *
        criticalFeatureContinuousFrameHermitianExcess
          (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) =
      2 * Real.pi /
        (1 - (xiSpectralPoint q).im ^ (2 : ℕ)) := by
  rw [wardGreen_mul_criticalFeatureContinuousFrameHermitianExcess_eq q hy,
    integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_ne_zero
      (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) hy]

/-- On the Ward kernel, Hermitian mass remains `2π`, while both fracture and totalized Green
reconstruction vanish. -/
theorem wardGreen_kernel_continuousFrame_fracture
    (q : XiZeroCopy) (hy : (xiSpectralPoint q).im = 0) :
    criticalFeatureContinuousFrameHermitianExcess
        (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) = 0 ∧
      thetaXiWardTransverseGreenWeight q *
          criticalFeatureContinuousFrameHermitianExcess
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) = 0 ∧
      (∫ t : ℝ,
        Complex.normSq
          (criticalEvaluation (xiSpectralPoint q)
            (abs_xiSpectralPoint_im_lt_half q)
            (criticalFeature (t : ℂ) (by norm_num)))) = 2 * Real.pi := by
  constructor
  · rw [criticalFeatureContinuousFrameHermitianExcess_eq, hy]
    norm_num
  · constructor
    · rw [(thetaXiWardTransverseGreenWeight_eq_zero_iff q).2 hy, zero_mul]
    · exact integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_eq_zero
        (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) hy

/-- Height-erased continuous-frame density of one Ward--Green Xi copy. -/
def fiveShiftWardGreenContinuousFrameDensity (q : XiZeroCopy) : ℝ :=
  fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q *
    (2 * Real.pi / (1 - (xiSpectralPoint q).im ^ (2 : ℕ)))

/-- Tonelli atom law: integrating one fixed-feature current over every real feature center removes
height and leaves the explicit transverse density. -/
theorem integral_fiveShiftCriticalFeatureWardGreenCurrent_eq_density
    (q : XiZeroCopy) :
    (∫ t : ℝ, fiveShiftCriticalFeatureWardGreenCurrent t q) =
      fiveShiftWardGreenContinuousFrameDensity q := by
  by_cases hy : (xiSpectralPoint q).im = 0
  · have hline : (q.1 : ℂ).re = 1 / 2 := by
      rw [xiSpectralPoint_im_eq] at hy
      linarith
    have hfun : (fun t : ℝ => fiveShiftCriticalFeatureWardGreenCurrent t q) =
        fun _ : ℝ => 0 := by
      funext t
      exact (fiveShiftCriticalFeatureWardGreenCurrent_eq_zero_iff_line t q).mpr hline
    rw [hfun, integral_zero, fiveShiftWardGreenContinuousFrameDensity,
      (fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_eq_zero_iff q).mpr hline,
      zero_mul]
  · have hfactor :
        (fun t : ℝ => fiveShiftCriticalFeatureWardGreenCurrent t q) =
          fun t : ℝ =>
            fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q *
              Complex.normSq
                (criticalEvaluation (xiSpectralPoint q)
                  (abs_xiSpectralPoint_im_lt_half q)
                  (criticalFeature (t : ℂ) (by norm_num))) := by
      funext t
      exact fiveShiftCriticalFeatureWardGreenCurrent_eq_renormalizedKrein_mul t q
    rw [hfactor, integral_const_mul,
      integral_normSq_criticalEvaluation_realCriticalFeature_eq_of_im_ne_zero
        (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) hy,
      fiveShiftWardGreenContinuousFrameDensity]

/-- Every strict-right multiplicity copy deposits at least `2π/81` total continuous-frame charge. -/
theorem fiveShiftWardGreenContinuousFrameDensity_right_ge
    (q : XiRightZeroCopy) :
    2 * Real.pi / 81 ≤ fiveShiftWardGreenContinuousFrameDensity q.1 := by
  have hscalar := fiveShiftEulerGammaRenormalizedKreinDefectCombination_right_ge q
  have hyabs := abs_lt.mp (abs_xiSpectralPoint_im_lt_half q.1)
  have hdenpos : 0 < 1 - (xiSpectralPoint q.1).im ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ((xiSpectralPoint q.1).im - 1 / 2),
      sq_nonneg ((xiSpectralPoint q.1).im + 1 / 2)]
  have hinv : 1 ≤ (1 - (xiSpectralPoint q.1).im ^ (2 : ℕ))⁻¹ := by
    exact (one_le_inv₀ hdenpos).2 (sub_le_self _ (sq_nonneg _))
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hscalar_nonneg :
      0 ≤ fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q.1 :=
    fiveShiftEulerGammaRenormalizedKreinDefectCombination_one_nonneg q.1
  have htwopi :
      2 * Real.pi ≤
        (2 * Real.pi) * (1 - (xiSpectralPoint q.1).im ^ (2 : ℕ))⁻¹ :=
    by simpa using mul_le_mul_of_nonneg_left hinv hpi
  rw [fiveShiftWardGreenContinuousFrameDensity, div_eq_mul_inv]
  calc
    2 * Real.pi / 81 = (1 / 81 : ℝ) * (2 * Real.pi) := by ring
    _ ≤ fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q.1 *
          (2 * Real.pi) := mul_le_mul_of_nonneg_right hscalar hpi
    _ ≤ fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q.1 *
          ((2 * Real.pi) * (1 - (xiSpectralPoint q.1).im ^ (2 : ℕ))⁻¹) := by
      exact mul_le_mul_of_nonneg_left htwopi hscalar_nonneg
    _ = fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q.1 *
          (2 * Real.pi * (1 - (xiSpectralPoint q.1).im ^ (2 : ℕ))⁻¹) := rfl

end

end RHTower

