import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarFourierRegularity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiH01OperatorDomain

/-!
# Actual Weil operator domain of the truncated pole profiles

Every truncated real exponential has a canonical vector in the complete exact Gamma
form domain. Its squared Gamma weight is integrable, so the existing multiplier
representation theorem supplies an L² representative of its form functional.
Orthogonal aperture compression and the literal bounded remainder then place the
profile in the actual unrestricted Weil Friedrichs domain, with an exact operator value.

These domain and spectral-action results leave the physical logarithmic boundary
formula and the signed arithmetic comparison as separate mathematical obligations.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct FourierTransform
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

/-- Every truncated exponential belongs to the exact Gamma weighted Fourier space. -/
theorem memLp_ccmPolarFourierIntegral_formMeasure (a : SuzukiPositiveAperture) (s : ℝ) :
    MemLp (ccmPolarFourierIntegral a s) 2 ccmArchimedeanFormMeasure := by
  have hi : Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ *
      ‖ccmPolarFourierIntegral a s ξ‖ ^ 2) := by
    apply (integrable_ccmFormWeight_sq_ccmPolarFourier a s).mono'
      (measurable_ccmArchimedeanFormWeight.aestronglyMeasurable.mul
        ((continuous_ccmPolarFourierIntegral a s).aestronglyMeasurable.norm.pow 2))
    filter_upwards with ξ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h := one_le_ccmArchimedeanFormWeight ξ
    nlinarith
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_ccmPolarFourierIntegral a s).aestronglyMeasurable).mpr
  unfold ccmArchimedeanFormMeasure
  rw [integrable_withDensity_iff_integrable_smul
    measurable_ccmArchimedeanFormWeightNNReal]
  refine hi.congr ?_
  filter_upwards with ξ
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

/-- Canonical weighted Fourier vector of the actual truncated exponential. -/
def ccmPolarWeightedFourierVector (a : SuzukiPositiveAperture) (s : ℝ) :
    CCMArchimedeanFourierL2 :=
  (memLp_ccmPolarFourierIntegral_formMeasure a s).toLp (ccmPolarFourierIntegral a s)

theorem ccmPolarWeightedFourierVector_coeFn (a : SuzukiPositiveAperture) (s : ℝ) :
    (ccmPolarWeightedFourierVector a s : ℝ → ℂ) =ᵐ[volume]
      ccmPolarFourierIntegral a s :=
  (MemLp.coeFn_toLp (memLp_ccmPolarFourierIntegral_formMeasure a s)).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)

theorem ccmArchimedeanWeightedToL2_polar (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmArchimedeanWeightedToL2 (ccmPolarWeightedFourierVector a s) =
      fourierUnitary (ccmPolarL2Vector a s) := by
  apply Lp.ext
  exact (ccmArchimedeanWeightedToL2_coeFn _).trans
    ((ccmPolarWeightedFourierVector_coeFn a s).trans
      (fourierUnitary_ccmPolarL2Vector_coeFn a s).symm)

theorem ccmArchimedeanFourierToTime_polar (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmArchimedeanFourierToTime (ccmPolarWeightedFourierVector a s) =
      ccmPolarL2Vector a s := by
  apply fourierUnitary.injective
  rw [fourierUnitary_ccmArchimedeanFourierToTime, ccmArchimedeanWeightedToL2_polar]

/-- Canonical pole profile in the complete exact Gamma form domain. -/
def ccmPolarFormVector (a : SuzukiPositiveAperture) (s : ℝ) :
    CCMArchimedeanFormDomain a := by
  refine ⟨ccmPolarWeightedFourierVector a s, ?_⟩
  rw [LinearMap.mem_ker]
  change (1 - indicatorCutoff (centralInterval a.1)
    (measurableSet_centralInterval a.1))
      (ccmArchimedeanFourierToTime (ccmPolarWeightedFourierVector a s)) = 0
  rw [ccmArchimedeanFourierToTime_polar, sub_apply, one_apply_eq_self,
    indicatorCutoff_ccmPolarL2Vector, sub_self]

theorem ccmArchimedeanFormToAperture_polar (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmArchimedeanFormToAperture a (ccmPolarFormVector a s) =
      ccmPolarApertureVector a s := by
  apply Subtype.ext
  exact ccmArchimedeanFourierToTime_polar a s

/-- The actual weighted pole vector admits the exact Gamma L² multiplier representative. -/
theorem memLp_ccmArchimedeanMultiplierProfile_polar (a : SuzukiPositiveAperture) (s : ℝ) :
    MemLp (ccmArchimedeanMultiplierProfile (ccmPolarFormVector a s).1) 2 volume := by
  apply MemLp.ae_eq _ (memLp_ccmFormWeight_mul_polarFourier a s)
  filter_upwards [ccmPolarWeightedFourierVector_coeFn a s] with ξ hξ
  change (ccmArchimedeanFormWeight ξ : ℂ) * ccmPolarFourierIntegral a s ξ =
    (ccmArchimedeanFormWeight ξ : ℂ) * ccmPolarWeightedFourierVector a s ξ
  rw [hξ]

/-- Compressed exact shifted Gamma multiplier acting on a pole profile. -/
def ccmPolarArchimedeanRepresentative (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiApertureHilbert a :=
  (suzukiApertureHilbert a).subtypeL.adjoint
    (ccmArchimedeanOperatorRepresentative (ccmPolarFormVector a s).1
      (memLp_ccmArchimedeanMultiplierProfile_polar a s))

theorem inner_ccmPolarArchimedeanRepresentative (a : SuzukiPositiveAperture) (s : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmPolarFormVector a s) v =
      inner ℂ (ccmPolarArchimedeanRepresentative a s) (ccmArchimedeanFormToAperture a v) := by
  rw [ccmPolarArchimedeanRepresentative,
    (suzukiApertureHilbert a).subtypeL.adjoint_inner_left]
  exact inner_ccmArchimedeanOperatorRepresentative _ _ _

/-- Exact full Weil representative, including the fixed scalar, polar and finite-prime terms. -/
def ccmPolarWeilRepresentative (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiApertureHilbert a :=
  ccmPolarArchimedeanRepresentative a s +
    ccmRestrictedWeilBoundedRemainder a (ccmPolarApertureVector a s)

theorem ccmPolarWeilRepresentative_represents_form (a : SuzukiPositiveAperture) (s : ℝ)
    (v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (ccmPolarFormVector a s) v =
      inner ℂ (ccmPolarWeilRepresentative a s) (ccmArchimedeanFormToAperture a v) := by
  rw [ccmRestrictedWeilForm, ccmPolarWeilRepresentative, inner_add_left,
    ccmArchimedeanFormToAperture_polar, inner_ccmPolarArchimedeanRepresentative]

private theorem polar_representation (a : SuzukiPositiveAperture) (s : ℝ) :
    ∃ hmem : ccmPolarApertureVector a s ∈ (ccmRestrictedWeilOperator a).domain,
      ccmRestrictedWeilOperator a ⟨ccmPolarApertureVector a s, hmem⟩ =
        ccmPolarWeilRepresentative a s := by
  have h := boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a) (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a) (denseRange_ccmArchimedeanFormToAperture a)
    (ccmPolarFormVector a s) (ccmPolarWeilRepresentative a s)
    (ccmPolarWeilRepresentative_represents_form a s)
  rw [ccmArchimedeanFormToAperture_polar] at h
  exact h

/-- Every truncated real exponential lies in the actual unrestricted Weil Friedrichs domain. -/
theorem ccmPolarApertureVector_mem_weilOperator_domain (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmPolarApertureVector a s ∈ (ccmRestrictedWeilOperator a).domain :=
  (polar_representation a s).choose

/-- The actual unrestricted Weil operator takes the exact spectral-plus-bounded value. -/
theorem ccmRestrictedWeilOperator_polar_apply (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmRestrictedWeilOperator a
      ⟨ccmPolarApertureVector a s, ccmPolarApertureVector_mem_weilOperator_domain a s⟩ =
        ccmPolarWeilRepresentative a s :=
  (polar_representation a s).choose_spec
end RHTower
