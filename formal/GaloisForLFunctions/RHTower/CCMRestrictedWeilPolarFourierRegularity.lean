import GaloisForLFunctions.RHTower.CCMRestrictedWeilBoundedRemainder
import GaloisForLFunctions.RHTower.CCMArchimedeanLogWeightEquivalence
import GaloisForLFunctions.RHTower.SuzukiH01FormDomain
import GaloisForLFunctions.RHTower.SuzukiApertureFourierDecay

/-!
# Spectral regularity of the truncated pole profiles

For every real exponential slope, the classical Fourier transform of the compact
pole profile has finite squared logarithmic energy. Integration by parts retains
both endpoint values. The global comparison for the exact Gamma form weight then
places its product with the actual unitary Fourier transform in L².

This establishes the maximal Fourier multiplier domain condition. Identification
with the compressed Friedrichs operator requires the weighted form representation.
-/

open Complex MeasureTheory Set Filter
open scoped FourierTransform ENNReal InnerProduct
noncomputable section
namespace RHTower

def ccmPolarFourierIntegral (a : SuzukiPositiveAperture) (s : ℝ) : ℝ → ℂ :=
  𝓕 ((centralInterval a.1).indicator (ccmPolarProfile s))

private theorem polar_integrable (a : SuzukiPositiveAperture) (s : ℝ) :
    Integrable ((centralInterval a.1).indicator (ccmPolarProfile s)) := by
  have hc : Continuous (ccmPolarProfile s) := by unfold ccmPolarProfile; fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem ccmPolarFourierIntegral_eq_interval (a : SuzukiPositiveAperture) (s ξ : ℝ) :
    ccmPolarFourierIntegral a s ξ = ∫ x in (-a.1)..a.1,
      ccmPolarProfile s x * Complex.exp ((((-2*Real.pi*ξ)*x : ℝ) : ℂ)*I) := by
  rw [ccmPolarFourierIntegral, Real.fourier_real_eq_integral_exp_smul]
  rw [intervalIntegral.integral_of_le (by linarith [a.property]),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ centralInterval a.1
  · have hxc : x ∈ Icc (-a.1) a.1 := hx
    rw [indicator_of_mem hx, indicator_of_mem hxc]
    simp only [smul_eq_mul]
    rw [show -2*Real.pi*x*ξ=(-2*Real.pi*ξ)*x by ring]
    ring
  · have hxc : x ∉ Icc (-a.1) a.1 := hx
    rw [indicator_of_notMem hx, indicator_of_notMem hxc, smul_zero]

theorem continuous_ccmPolarFourierIntegral (a : SuzukiPositiveAperture) (s : ℝ) :
    Continuous (ccmPolarFourierIntegral a s) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (polar_integrable a s)

private theorem polar_deriv (s x : ℝ) :
    HasDerivAt (ccmPolarProfile s) ((s : ℂ)*ccmPolarProfile s x) x := by
  have hr : HasDerivAt (fun x : ℝ => Real.exp (s*x)) (s*Real.exp (s*x)) x := by
    simpa only [id_eq, mul_comm, mul_one] using ((hasDerivAt_id x).const_mul s).exp
  have hc : HasDerivAt (fun x : ℝ => (Real.exp (s*x) : ℂ))
      ((s*Real.exp (s*x) : ℝ) : ℂ) x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hr
  change HasDerivAt (fun x : ℝ => (Real.exp (s*x) : ℂ))
    ((s : ℂ)*(Real.exp (s*x) : ℂ)) x
  rw [← Complex.ofReal_mul]
  exact hc

/-- The literal pole profile has square-logarithmic Fourier energy despite its hard endpoints. -/
theorem integrable_suzukiLogWeight_sq_ccmPolarFourier (a : SuzukiPositiveAperture) (s : ℝ) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ ^ 2 * ‖ccmPolarFourierIntegral a s ξ‖ ^ 2) := by
  let C := ∫ x in (-a.1)..a.1, ‖ccmPolarProfile s x‖
  let M := (‖ccmPolarProfile s a.1‖ + ‖ccmPolarProfile s (-a.1)‖ +
    ∫ x in (-a.1)..a.1, ‖(s : ℂ)*ccmPolarProfile s x‖)/(2*Real.pi)
  apply integrable_suzukiLogWeight_sq_norm_sq_of_general_fourier_envelope _ C M
    (continuous_ccmPolarFourierIntegral a s).aestronglyMeasurable
  intro ξ hξ
  have ha : -a.1 ≤ a.1 := by linarith [a.property]
  have hz : -2*Real.pi*ξ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ
  rw [ccmPolarFourierIntegral_eq_interval]
  apply le_min
  · exact (norm_intervalIntegral_fourier_le_l1 ha (ccmPolarProfile s) (-2*Real.pi*ξ)).trans
      (le_abs_self C)
  · have hbound := norm_intervalIntegral_fourier_le_ibp ha hz
      (fun x _ => polar_deriv s x) (by
        apply Continuous.intervalIntegrable
        unfold ccmPolarProfile
        fun_prop)
    have hden : |-2*Real.pi*ξ| = (2*Real.pi)*|ξ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le]
      norm_num
    rw [hden] at hbound
    have heq : (‖ccmPolarProfile s a.1‖ + ‖ccmPolarProfile s (-a.1)‖ +
        ∫ x in (-a.1)..a.1, ‖(s : ℂ)*ccmPolarProfile s x‖) / ((2*Real.pi)*|ξ|) = M/|ξ| := by
      dsimp [M]
      ring
    rw [heq] at hbound
    exact hbound.trans (div_le_div_of_nonneg_right (le_abs_self M) (abs_nonneg ξ))

/-- The actual squared Gamma form weight is integrable against every truncated exponential. -/
theorem integrable_ccmFormWeight_sq_ccmPolarFourier (a : SuzukiPositiveAperture) (s : ℝ) :
    Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ ^ 2 *
      ‖ccmPolarFourierIntegral a s ξ‖ ^ 2) := by
  have hbase := (integrable_suzukiLogWeight_sq_ccmPolarFourier a s).const_mul
    (ccmArchimedeanLogComparisonConstant ^ 2)
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ ^ 2 *
      ‖ccmPolarFourierIntegral a s ξ‖ ^ 2) (volume : Measure ℝ) :=
    (measurable_ccmArchimedeanFormWeight.aestronglyMeasurable.pow 2).mul
    ((continuous_ccmPolarFourierIntegral a s).aestronglyMeasurable.norm.pow 2)
  refine hbase.mono' hmeas ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hC : 0 ≤ ccmArchimedeanLogComparisonConstant :=
    zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant
  have hlog : 0 ≤ suzukiLogWeight ξ := zero_le_one.trans (one_le_suzukiLogWeight ξ)
  have hW : 0 ≤ ccmArchimedeanFormWeight ξ := (ccmArchimedeanFormWeight_pos ξ).le
  have hbound := ccmArchimedeanFormWeight_le_logComparison ξ
  have hsq : ccmArchimedeanFormWeight ξ ^ 2 ≤
      ccmArchimedeanLogComparisonConstant ^ 2 * suzukiLogWeight ξ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg hW (mul_nonneg hC hlog))]
  calc
    ccmArchimedeanFormWeight ξ ^ 2 * ‖ccmPolarFourierIntegral a s ξ‖ ^ 2 ≤
        (ccmArchimedeanLogComparisonConstant ^ 2 * suzukiLogWeight ξ ^ 2) *
          ‖ccmPolarFourierIntegral a s ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = _ := by ring

/-- The actual unitary Fourier transform of the pole vector has the classical integral
as its coefficient function. -/
theorem fourierUnitary_ccmPolarL2Vector_coeFn (a : SuzukiPositiveAperture) (s : ℝ) :
    ((fourierUnitary (ccmPolarL2Vector a s) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      ccmPolarFourierIntegral a s := by
  let f := ccmPolarL2Vector a s
  have hcoe := ccmPolarL2Vector_coeFn a s
  have hint : Integrable (f : ℝ → ℂ) := (polar_integrable a s).congr hcoe.symm
  have hcoe1 : (((memLp_one_iff_integrable.mpr hint).toLp f : Lp ℂ 1 (volume : Measure ℝ)) :
      ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hint)
  have hclassical : ∀ w : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp f) : ℝ → ℂ) w =
        FourierTransform.fourier (f : ℝ → ℂ) w := by
    intro w
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe1 w
  have h1 := (l2_fourier_coeFn_eq_l1_fourier_of_integrable f hint).trans
    (Eventually.of_forall hclassical)
  refine h1.trans (Eventually.of_forall fun w => ?_)
  exact Real.fourier_congr_ae hcoe w

/-- Multiplication by the full shifted Gamma weight preserves L² for the classical pole transform. -/
theorem memLp_ccmFormWeight_mul_polarFourier (a : SuzukiPositiveAperture) (s : ℝ) :
    MemLp (fun ξ : ℝ => (ccmArchimedeanFormWeight ξ : ℂ) *
      ccmPolarFourierIntegral a s ξ) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => (ccmArchimedeanFormWeight ξ : ℂ) *
      ccmPolarFourierIntegral a s ξ) volume :=
    (Complex.measurable_ofReal.comp measurable_ccmArchimedeanFormWeight).aestronglyMeasurable.mul
      (continuous_ccmPolarFourierIntegral a s).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  refine (integrable_ccmFormWeight_sq_ccmPolarFourier a s).congr ?_
  filter_upwards with ξ
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The literal pole vector lies in the Fourier multiplier's maximal L² domain.
This is spectral regularity; the compressed Friedrichs representation still needs its form weld. -/
theorem memLp_ccmFormWeight_mul_fourier_polarVector (a : SuzukiPositiveAperture) (s : ℝ) :
    MemLp (fun ξ : ℝ => (ccmArchimedeanFormWeight ξ : ℂ) *
      (fourierUnitary (ccmPolarL2Vector a s) : SoninL2) ξ) 2 volume := by
  apply MemLp.ae_eq _ (memLp_ccmFormWeight_mul_polarFourier a s)
  filter_upwards [fourierUnitary_ccmPolarL2Vector_coeFn a s] with ξ hξ
  rw [hξ]
end RHTower
