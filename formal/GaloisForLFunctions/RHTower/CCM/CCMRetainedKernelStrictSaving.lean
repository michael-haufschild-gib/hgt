import GaloisForLFunctions.RHTower.CCM.CCMRetainedKernelOuterSaving
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# An actual strict outer-shell saving

A positive threshold strictly above the actual symbol at zero makes the
retained weight nonzero for every window and every retention fraction. Fourier
uniqueness then forces positive kernel mass in the outer aperture shell.
This proves strict improvement of the kernel budget, not source positivity.
-/

open Complex MeasureTheory Set
open scoped FourierTransform
noncomputable section
namespace RHTower

def ccmRetainedPositiveThreshold (a : SuzukiPositiveAperture) : ℝ :=
  1 + max 0 (ccmActualWeilSymbol a 0)

theorem ccmRetainedPositiveThreshold_pos (a : SuzukiPositiveAperture) :
    0 < ccmRetainedPositiveThreshold a := by
  unfold ccmRetainedPositiveThreshold
  linarith [le_max_left (0 : ℝ) (ccmActualWeilSymbol a 0)]

theorem ccmRetainedSignedFrequencyWeight_at_threshold_zero_pos
    (a : SuzukiPositiveAperture) (R θ : ℝ) :
    0 < ccmRetainedSignedFrequencyWeight a (ccmRetainedPositiveThreshold a) R θ 0 := by
  have hm : ccmActualWeilSymbol a 0 < ccmRetainedPositiveThreshold a := by
    unfold ccmRetainedPositiveThreshold
    linarith [le_max_right (0 : ℝ) (ccmActualWeilSymbol a 0)]
  simp only [ccmRetainedSignedFrequencyWeight, ccmActualSourceNegativeWeight,
    ccmPositiveFrequencyWeight, max_eq_left (sub_nonpos.mpr hm.le),
    zero_mul, mul_zero, sub_zero, max_eq_right (sub_nonneg.mpr hm.le)]
  exact sub_pos.mpr hm

/-- The outer saving is strictly positive on actual retained source data. -/
theorem ccmRetainedKernelOuterSaving_at_threshold_pos
    (a : SuzukiPositiveAperture) (R θ : ℝ) :
    0 < ccmRetainedKernelOuterSaving a (ccmRetainedPositiveThreshold a) R θ := by
  let α := ccmRetainedPositiveThreshold a
  let w : ℝ → ℂ := fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ)
  let k := ccmRetainedPhysicalKernel a α R θ
  let S : Set ℝ := Icc (-2*a.1) (2*a.1) \ Icc (-a.1) a.1
  have hw : Integrable w := integrable_ccmRetainedSignedFrequencyWeight a α R θ
  have hc : Continuous w := Complex.continuous_ofReal.comp
    (continuous_ccmRetainedSignedFrequencyWeight a α R θ)
  have hk : Continuous k := continuous_ccmRetainedPhysicalKernel a α R θ
  have hs : MeasurableSet S := measurableSet_Icc.diff measurableSet_Icc
  have hi : IntegrableOn (fun h => ‖k h‖) S := hk.norm.integrableOn_Icc.mono_set sdiff_subset
  have hcompact : HasCompactSupport w :=
    (hasCompactSupport_ccmRetainedSignedFrequencyWeight a α R θ).comp_left
      Complex.ofReal_zero
  obtain ⟨B, hB⟩ := hcompact.isBounded.subset_closedBall (0 : ℝ)
  have hsupport : ∀ᵐ x ∂volume, x ∉ Icc (-B) B → w x = 0 := by
    filter_upwards with x hx
    by_contra hne
    have hb := hB (subset_tsupport w hne)
    have habs : |x| ≤ B := by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hb
    exact hx (abs_le.mp habs)
  by_contra hnot
  have hz : ccmRetainedKernelOuterSaving a α R θ = 0 :=
    le_antisymm (le_of_not_gt hnot) (ccmRetainedKernelOuterSaving_nonneg a α R θ)
  have hzint : (∫ h in S, ‖k h‖) = 0 := by
    change (1 / 2 : ℝ) * (∫ h in S, ‖k h‖) = 0 at hz
    linarith only [hz]
  have hae : ∀ᵐ h ∂volume, h ∈ S → k h = 0 := by
    have hnorm := (integral_eq_zero_iff_of_nonneg (fun h => norm_nonneg (k h)) hi).mp hzint
    have hm := (ae_restrict_iff' hs).mp hnorm
    filter_upwards [hm] with h hh hmem
    exact norm_eq_zero.mp (hh hmem)
  have hopen : k =ᵐ[volume.restrict (Ioo a.1 (2*a.1))] 0 := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hae] with h hh hmem
    apply hh
    refine ⟨⟨?_, hmem.2.le⟩, fun hn => ?_⟩
    · linarith [hmem.1, a.property]
    · exact (not_le_of_gt hmem.1) hn.2
  have hpoint : EqOn k 0 (Ioo a.1 (2*a.1)) :=
    Measure.eqOn_open_of_ae_eq hopen isOpen_Ioo hk.continuousOn continuous_zero.continuousOn
  have hFT : ∀ ξ, 𝓕 w ξ = 0 := fourier_eq_zero_of_ae_zero_on_Ioo hw hsupport
    (c := -2*a.1) (d := -a.1) (by linarith [a.property]) (by
      filter_upwards with ξ hξ
      have hz' : k (-ξ) = 0 := hpoint (by constructor <;> linarith [hξ.1, hξ.2])
      simpa only [k, ccmRetainedPhysicalKernel, Real.fourierInv_eq_fourier_neg, neg_neg]
        using hz')
  have heq := Measure.eq_of_ae_eq
    (_root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hw hFT) hc continuous_zero
  have hz0 : ccmRetainedSignedFrequencyWeight a α R θ 0 = 0 := by
    have := congrFun heq 0
    exact Complex.ofReal_eq_zero.mp this
  exact (ne_of_gt (ccmRetainedSignedFrequencyWeight_at_threshold_zero_pos a R θ)) hz0

/-- The actual shell ceiling strictly improves the unsplit ceiling at a positive threshold. -/
theorem ccmRetainedKernelShellCeiling_at_threshold_lt
    (a : SuzukiPositiveAperture) (R θ : ℝ) :
    ccmRetainedKernelShellCeiling a (ccmRetainedPositiveThreshold a) R θ <
      ccmRetainedKernelCeiling a (ccmRetainedPositiveThreshold a) R θ := by
  linarith [ccmRetainedKernelShellCeiling_add_saving a (ccmRetainedPositiveThreshold a) R θ,
    ccmRetainedKernelOuterSaving_at_threshold_pos a R θ]

end RHTower
