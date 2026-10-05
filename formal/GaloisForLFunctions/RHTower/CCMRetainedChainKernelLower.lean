import GaloisForLFunctions.RHTower.CCMApertureChainProfile
import GaloisForLFunctions.RHTower.CCMRetainedKernelStrictSaving

/-!
# The all-displacement chain bound on the complete signed source

The geometric chain profile weights the physical kernel after both frequency
signs have been assembled. The bound holds on the whole form domain, and an
exact nonnegative inner-aperture saving improves the earlier outer-shell bound.
-/

open Complex MeasureTheory Set
open scoped FourierTransform
noncomputable section
namespace RHTower

theorem integrableOn_ccmChainProfile_mul_norm (a : SuzukiPositiveAperture)
    {k : ℝ → ℂ} (hk : Continuous k) (b c : ℝ) :
    IntegrableOn (fun h => ccmApertureChainProfile a h * ‖k h‖) (Icc b c) := by
  apply hk.norm.integrableOn_Icc.mono_nonneg
    ((measurable_ccmApertureChainProfile a).mul hk.norm.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun h =>
      mul_nonneg (ccmApertureChainProfile_bounds a h).1 (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun h => by
      change ccmApertureChainProfile a h * ‖k h‖ ≤ ‖k h‖
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (ccmApertureChainProfile_bounds a h).2 (norm_nonneg (k h))

def ccmApertureChainKernelMass (a : SuzukiPositiveAperture) (w : ℝ → ℂ) : ℝ :=
  ∫ h in Icc (-2*a.1) (2*a.1), ccmApertureChainProfile a h * ‖𝓕⁻ w h‖

theorem ccmApertureChainKernelMass_nonneg (a : SuzukiPositiveAperture) (w : ℝ → ℂ) :
    0 ≤ ccmApertureChainKernelMass a w := integral_nonneg fun h =>
  mul_nonneg (ccmApertureChainProfile_bounds a h).1 (norm_nonneg _)

/-- The full complex pairing obeys the chain profile at every displacement. -/
theorem norm_integral_weight_mul_ccmApertureFourierDensity_le_chain
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (w : ℝ → ℂ) (hw : Integrable w) :
    ‖∫ ξ, w ξ * ccmApertureFourierDensity a f ξ‖ ≤
      ccmApertureChainKernelMass a w * ‖f‖ ^ 2 := by
  have hk : Continuous (𝓕⁻ w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hw
  have hc := continuous_ccmApertureCorrelation a f
  rw [integral_weight_mul_ccmApertureFourierDensity a f w hw]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (-2*a.1) (2*a.1)) (fun h hh => by
      rw [ccmApertureCorrelation_eq_zero_of_outside a f hh, mul_zero])]
  calc
    _ ≤ ∫ h in Icc (-2*a.1) (2*a.1), ‖𝓕⁻ w h * ccmApertureCorrelation a f h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Icc (-2*a.1) (2*a.1),
        (ccmApertureChainProfile a h * ‖𝓕⁻ w h‖) * ‖f‖ ^ 2 := by
      apply integral_mono (hk.mul hc).norm.integrableOn_Icc
        ((integrableOn_ccmChainProfile_mul_norm a hk _ _).mul_const _)
      intro h
      change ‖𝓕⁻ w h * ccmApertureCorrelation a f h‖ ≤
        (ccmApertureChainProfile a h * ‖𝓕⁻ w h‖) * ‖f‖ ^ 2
      rw [norm_mul]
      have hb := mul_le_mul_of_nonneg_left (norm_ccmApertureCorrelation_le_profile a f h)
        (norm_nonneg (𝓕⁻ w h))
      simpa only [mul_left_comm, mul_assoc] using hb
    _ = _ := by rw [integral_mul_const]; rfl

def ccmRetainedChainKernelCeiling (a : SuzukiPositiveAperture) (α R θ : ℝ) : ℝ :=
  ccmApertureChainKernelMass a
    (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ))

/-- The explicit saving over the older shell bound comes from every inner displacement. -/
def ccmRetainedChainInnerSaving (a : SuzukiPositiveAperture) (α R θ : ℝ) : ℝ :=
  ∫ h in Icc (-a.1) a.1,
    (1 - ccmApertureChainProfile a h) * ‖ccmRetainedPhysicalKernel a α R θ h‖

theorem ccmRetainedChainKernelCeiling_nonneg (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    0 ≤ ccmRetainedChainKernelCeiling a α R θ := ccmApertureChainKernelMass_nonneg a _

theorem ccmRetainedChainInnerSaving_nonneg (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    0 ≤ ccmRetainedChainInnerSaving a α R θ := integral_nonneg fun h =>
  mul_nonneg (sub_nonneg.mpr (ccmApertureChainProfile_bounds a h).2) (norm_nonneg _)

/-- Exact accounting of the all-displacement improvement, including every cross term. -/
theorem ccmRetainedChainKernelCeiling_add_saving (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    ccmRetainedChainKernelCeiling a α R θ + ccmRetainedChainInnerSaving a α R θ =
      ccmRetainedKernelShellCeiling a α R θ := by
  let k := ccmRetainedPhysicalKernel a α R θ
  let r := ccmApertureChainProfile a
  have hk : Continuous k := continuous_ccmRetainedPhysicalKernel a α R θ
  have hi := integrableOn_ccmChainProfile_mul_norm a hk (-a.1) a.1
  have hb := integrableOn_ccmChainProfile_mul_norm a hk (-2*a.1) (2*a.1)
  have hsub : Icc (-a.1) a.1 ⊆ Icc (-2*a.1) (2*a.1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, a.property]
  have houter : (∫ h in Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1, r h * ‖k h‖) =
      (1 / 2 : ℝ) * ∫ h in Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1, ‖k h‖ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_Icc.diff measurableSet_Icc)
    intro h hh
    change ccmApertureChainProfile a h * ‖k h‖ = _
    rw [ccmApertureChainProfile_outer a
      (lt_of_not_ge fun hn => hh.2 (abs_le.mp hn))
      (abs_le.mpr ⟨by linarith only [hh.1.1], hh.1.2⟩)]
  have hsplit := setIntegral_sdiff measurableSet_Icc hb hsub
  have hsaving : ccmRetainedChainInnerSaving a α R θ =
      (∫ h in Icc (-a.1) a.1, ‖k h‖) - ∫ h in Icc (-a.1) a.1, r h * ‖k h‖ := by
    unfold ccmRetainedChainInnerSaving
    simp only [sub_mul, one_mul]
    exact integral_sub hk.norm.integrableOn_Icc hi
  rw [houter] at hsplit
  change (∫ h in Icc (-2*a.1) (2*a.1), r h * ‖k h‖) +
    ccmRetainedChainInnerSaving a α R θ =
    (∫ h in Icc (-a.1) a.1, ‖k h‖) +
      (1 / 2 : ℝ) * ∫ h in Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1, ‖k h‖
  rw [hsaving]
  linarith only [hsplit]

theorem ccmRetainedChainKernelCeiling_le_shell (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    ccmRetainedChainKernelCeiling a α R θ ≤ ccmRetainedKernelShellCeiling a α R θ := by
  linarith [ccmRetainedChainKernelCeiling_add_saving a α R θ,
    ccmRetainedChainInnerSaving_nonneg a α R θ]

theorem ccmRetainedChainKernelCeiling_at_threshold_lt_diameter
    (a : SuzukiPositiveAperture) (R θ : ℝ) :
    ccmRetainedChainKernelCeiling a (ccmRetainedPositiveThreshold a) R θ <
      ccmRetainedKernelCeiling a (ccmRetainedPositiveThreshold a) R θ :=
  (ccmRetainedChainKernelCeiling_le_shell a _ R θ).trans_lt
    (ccmRetainedKernelShellCeiling_at_threshold_lt a R θ)

/-- Every actual retained debt is controlled by the full chain-weighted signed kernel. -/
theorem ccmRetained_debt_abs_le_chainKernel (a : SuzukiPositiveAperture) (α R θ : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    |(∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) -
      θ * (∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R)| ≤
        ccmRetainedChainKernelCeiling a α R θ * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  have h := norm_integral_weight_mul_ccmApertureFourierDensity_le_chain a
    (ccmArchimedeanFormToAperture a u)
    (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ))
    (integrable_ccmRetainedSignedFrequencyWeight a α R θ)
  rw [ccmRetainedSignedFrequency_pairing, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The complete source lower bound has no coefficient-order or matrix-size factor. -/
theorem ccmRestrictedWeilSource_ge_retainedChainKernel (a : SuzukiPositiveAperture)
    (α R : ℝ) (θ : Icc (0 : ℝ) 1) (u : CCMArchimedeanFormDomain a) :
    (α - ccmRetainedChainKernelCeiling a α R θ.1) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  have hsource := ccmRestrictedWeilSource_ge_retainedPositiveWindow a α R θ u
  have hdebt := (le_abs_self _).trans (ccmRetained_debt_abs_le_chainKernel a α R θ.1 u)
  nlinarith only [hsource, hdebt]

end RHTower
