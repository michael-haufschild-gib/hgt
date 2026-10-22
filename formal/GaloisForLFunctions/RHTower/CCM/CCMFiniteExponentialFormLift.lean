import GaloisForLFunctions.RHTower.CCM.CCMFiniteExponentialLogEnergy
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPrimeOuterShell

open MeasureTheory Set Filter
open scoped Topology FourierTransform
noncomputable section
namespace RHTower


/-- A certified finite-exponential aperture vector belongs to the actual
Gamma form domain; the same literal lift satisfies every logarithmic-band
energy estimate. No regularity of an unknown response is assumed. -/
theorem CCMFiniteExponentialBudget.exists_ccmFormLift
    {a : SuzukiPositiveAperture} {f : suzukiApertureHilbert a} {V : ℝ}
    (hf : CCMFiniteExponentialBudget f.1 V) :
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f ∧
      ∀ R : ℝ, 1 ≤ R → ‖u‖ ^ 2 ≤ ccmArchimedeanLogComparisonConstant *
        ((1 + Real.log R) * ‖f‖ ^ 2 + 2 * V ^ 2 * (Real.log R + 2) / (Real.pi ^ 2 * R)) := by
  let g : ℝ → ℂ := (fourierUnitary f.1 : ℝ → ℂ)
  have hg : StronglyMeasurable g := Lp.stronglyMeasurable _
  have hC : 0 ≤ ccmArchimedeanLogComparisonConstant :=
    zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant
  have hlog : Integrable (fun ξ => suzukiLogWeight ξ * ‖g ξ‖ ^ 2) :=
    (hf.logarithmic_energy (R := 1) le_rfl).1
  have hpoint (ξ : ℝ) : ccmArchimedeanFormWeight ξ * ‖g ξ‖ ^ 2 ≤
      ccmArchimedeanLogComparisonConstant * (suzukiLogWeight ξ * ‖g ξ‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (ccmArchimedeanFormWeight_le_logComparison ξ)
      (sq_nonneg ‖g ξ‖)
    simpa only [mul_assoc] using h
  have harch : Integrable (fun ξ => ccmArchimedeanFormWeight ξ * ‖g ξ‖ ^ 2) := by
    apply (hlog.const_mul ccmArchimedeanLogComparisonConstant).mono'
      (measurable_ccmArchimedeanFormWeight.aestronglyMeasurable.mul
        (hg.aestronglyMeasurable.norm.pow 2))
    filter_upwards with ξ
    change ‖ccmArchimedeanFormWeight ξ * ‖g ξ‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le
      (sq_nonneg _))]
    exact hpoint ξ
  have hmem : MemLp g 2 ccmArchimedeanFormMeasure := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
    unfold ccmArchimedeanFormMeasure
    rw [integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal]
    refine harch.congr ?_
    filter_upwards with ξ
    rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]
  let q : CCMArchimedeanFourierL2 := hmem.toLp g
  have hq : (q : ℝ → ℂ) =ᵐ[volume] g :=
    hmem.coeFn_toLp.filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hQ : ccmArchimedeanWeightedToL2 q = fourierUnitary f.1 := by
    apply Lp.ext
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn q, hq] with ξ hξ hqξ
    exact hξ.trans hqξ
  have htime : ccmArchimedeanFourierToTime q = f.1 := by
    apply fourierUnitary.injective
    rw [fourierUnitary_ccmArchimedeanFourierToTime, hQ]
  have hsupport : q ∈ (ccmArchimedeanSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1))
      (ccmArchimedeanFourierToTime q) = 0
    rw [htime, sub_apply, one_apply_eq_self,
      indicatorCutoff_suzukiApertureHilbert a f, sub_self]
  let u : CCMArchimedeanFormDomain a := ⟨q, hsupport⟩
  refine ⟨u, ?_, ?_⟩
  · apply Subtype.ext
    exact htime
  · intro R hR
    have hnorm : ‖u‖ ^ 2 = ∫ ξ, ccmArchimedeanFormWeight ξ * ‖g ξ‖ ^ 2 := by
      change ‖q‖ ^ 2 = _
      rw [norm_sq_ccmArchimedeanFourierL2]
      apply integral_congr_ae
      filter_upwards [hq] with ξ hξ
      rw [hξ]
    rw [hnorm]
    calc
      _ ≤ ∫ ξ, ccmArchimedeanLogComparisonConstant * (suzukiLogWeight ξ * ‖g ξ‖ ^ 2) :=
        integral_mono_ae harch (hlog.const_mul _) (Eventually.of_forall hpoint)
      _ = ccmArchimedeanLogComparisonConstant * suzukiHlogMoment f.1 := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hf.logarithmic_energy hR).2 hC

/-- Every actual odd-source remainder iterate belongs to the actual Gamma
form domain, with its certified quantitative logarithmic energy bound. -/
theorem ccmNormalizedWeilRemainder_odd_iterate_exists_ccmFormLift
    (a : SuzukiPositiveAperture) (n : ℕ) :
    let f := ((ccmNormalizedWeilRemainder a)^[n])
      ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) - ccmPolarApertureVector a (-1 / 2)))
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f ∧
      ∀ R : ℝ, 1 ≤ R → ‖u‖ ^ 2 ≤ ccmArchimedeanLogComparisonConstant *
        ((1 + Real.log R) * ‖f‖ ^ 2 +
          2 * ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a.1 / 2)) ^ 2 *
            (Real.log R + 2) / (Real.pi ^ 2 * R)) :=
  CCMFiniteExponentialBudget.exists_ccmFormLift (a := a)
    (f := ((ccmNormalizedWeilRemainder a)^[n])
      ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) - ccmPolarApertureVector a (-1 / 2))))
    (ccmNormalizedWeilRemainder_odd_iterate_budget a n)

end RHTower
end
