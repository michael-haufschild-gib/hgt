import GaloisForLFunctions.RHTower.CCM.CCMThetaSmallMeasureEnergy

/-!
# Literal support measure bounds the low-frequency mass of CCM sources

The physical source's L¹--L² bound gives a pointwise Fourier bound with the
exact total support measure. Integration over `[-R,R]` retains the factor
`2 R`. This makes the small-support mechanism quantitative and includes
arbitrary disconnected support.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform

namespace RHTower

def ccmSmoothSupportMeasure {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : ℝ :=
  (volume (Function.support u)).toReal

theorem ccmSmoothSupportMeasure_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : 0 ≤ ccmSmoothSupportMeasure u :=
  ENNReal.toReal_nonneg

theorem ccmSmooth_support_volume_lt_top {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : volume (Function.support u) < ⊤ :=
  (measure_mono (u.support_subset.trans Ioo_subset_Icc_self)).trans_lt
    (isCompact_Icc.measure_lt_top)

theorem ccmSmooth_integral_norm_sq_eq_physical {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (∫ x : ℝ, ‖u x‖ ^ 2) = ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [u.toCCMFormVector_physical_coeFn] with x hx
  change (ccmArchimedeanFormEmbedding a u.toCCMFormVector : ℝ → ℂ) x = u x at hx
  rw [hx]

/-- Cauchy--Schwarz with the actual support measure, including all disconnected pieces. -/
theorem ccmSmooth_integral_norm_sq_le_supportMeasure
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    (∫ x : ℝ, ‖u x‖) ^ 2 ≤
      ccmSmoothSupportMeasure u * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  let S := Function.support u
  letI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using ccmSmooth_support_volume_lt_top u⟩
  have hu : MemLp (fun x : ℝ => u x) (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by
    have he : (u.toSchwartz : ℝ → ℂ) = (fun x => u x) :=
      funext (CCMComplexSmoothInteriorSource.toSchwartz_apply u)
    rw [← he, ENNReal.ofReal_ofNat]
    exact (u.toSchwartz.memLp 2 volume).restrict S
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict S) (f := fun x : ℝ => u x) (g := fun _ : ℝ => (1 : ℂ))
    Real.HolderConjugate.two_two hu (memLp_const (1 : ℂ))
  simp only [norm_one, mul_one, Real.rpow_two, one_pow, integral_const,
    measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, ← Real.sqrt_eq_rpow] at h
  have h₁ : (∫ x in S, ‖u x‖) = ∫ x : ℝ, ‖u x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [Function.notMem_support.mp hx, norm_zero]
  have h₂ : (∫ x in S, ‖u x‖ ^ 2) = ∫ x : ℝ, ‖u x‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [Function.notMem_support.mp hx, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  rw [h₁, h₂] at h
  have hsquare := pow_le_pow_left₀ (integral_nonneg (fun x => norm_nonneg (u x))) h 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖u x‖)),
    Real.sq_sqrt ENNReal.toReal_nonneg, ccmSmooth_integral_norm_sq_eq_physical] at hsquare
  simpa only [ccmSmoothSupportMeasure, S, mul_comm] using hsquare

/-- Pointwise Fourier uncertainty bound in the corpus's exact Fourier normalization. -/
theorem norm_fourier_ccmSmooth_sq_le_supportMeasure
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (xi : ℝ) :
    ‖𝓕 (u.toSchwartz : ℝ → ℂ) xi‖ ^ 2 ≤
      ccmSmoothSupportMeasure u * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  have h : ‖𝓕 (u.toSchwartz : ℝ → ℂ) xi‖ ≤ ∫ x : ℝ, ‖u x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (u.toSchwartz : ℝ → ℂ) xi
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (ccmSmooth_integral_norm_sq_le_supportMeasure u)

theorem fourier_ccmSmooth_physical_coeFn {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (fourierUnitary (ccmArchimedeanFormEmbedding a u.toCCMFormVector) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (u.toSchwartz : ℝ → ℂ) := by
  change (fourierUnitary (ccmArchimedeanFourierToTime u.toCCMFormVector.1) : ℝ → ℂ) =ᵐ[volume] _
  rw [fourierUnitary_ccmArchimedeanFourierToTime]
  exact (ccmArchimedeanWeightedToL2_coeFn u.toCCMFormVector.1).trans
    u.toCCMFormVector_fourier_coeFn

/-- The exact low-frequency mass is bounded by frequency width times support measure. -/
theorem ccmSmooth_fourierWindow_mass_le_supportMeasure
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ xi in centralInterval R,
        ‖(fourierUnitary (ccmArchimedeanFormEmbedding a u.toCCMFormVector) : ℝ → ℂ) xi‖ ^ 2) ≤
      2 * R * ccmSmoothSupportMeasure u * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  let f := ccmArchimedeanFormEmbedding a u.toCCMFormVector
  have hi : Integrable (fun xi : ℝ => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hfinite : volume (centralInterval R) ≠ ⊤ := by
    rw [centralInterval, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hb : (∫ xi in centralInterval R, ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) ≤
      ∫ _xi in centralInterval R, ccmSmoothSupportMeasure u * ‖f‖ ^ 2 := by
    apply setIntegral_mono_on_ae hi.integrableOn (integrableOn_const hfinite)
      (measurableSet_centralInterval R)
    filter_upwards [fourier_ccmSmooth_physical_coeFn u] with xi hxi
    intro _
    rw [show (fourierUnitary f : ℝ → ℂ) xi = 𝓕 (u.toSchwartz : ℝ → ℂ) xi from hxi]
    exact norm_fourier_ccmSmooth_sq_le_supportMeasure u xi
  have hvol : (volume (centralInterval R)).toReal = 2 * R := by
    rw [centralInterval, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
    ring
  rw [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, hvol] at hb
  simpa only [mul_assoc, f] using hb

end RHTower
