import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureFourierSourceAlias

/-!
# Quantitative HCF phase saving from source-alias variance

The phase-preserving HCF alias has Haar mean zero. Mere sign selection only shows that some phase
has nonpositive alias. This module extracts a quantitative saving: for a continuous zero-mean
reporter bounded above by `M`, its minimum is at most `-variance / M`.

Applied to the coefficient-faithful HCF source alias, `M` is its exact Fourier coefficient `ℓ¹`
mass. The resulting real phase lowers the full periodized pole--Gamma source observable below its
zero mode by `alias variance / coefficient mass`. This exposes a new source-only target: obtain a
height-local lower bound for alias variance from the corpus eta pair-correlation/rank--trace ledger.
No Xi divisor is selected in the definitions or the phase choice.
-/

open Complex Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

theorem exists_re_le_neg_variance_div_of_zeroMean
    (f : UnitAddCircle → ℂ) (hf : Continuous f) (M : ℝ) (hM : 0 < M)
    (hupper : ∀ θ, (f θ).re ≤ M)
    (hmean : (∫ θ, f θ ∂GaloisForLFunctions.unitCircleHaar) = 0) :
    ∃ θ, (f θ).re ≤
      -(∫ θ, ((f θ).re) ^ (2 : ℕ) ∂GaloisForLFunctions.unitCircleHaar) / M := by
  let h : UnitAddCircle → ℝ := fun θ => (f θ).re
  have hh : Continuous h := Complex.continuous_re.comp hf
  obtain ⟨θ₀, _hθ₀mem, hmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hh.continuousOn
  have hfInt : Integrable f GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hf.continuousOn.integrableOn_compact isCompact_univ
  have hhInt : Integrable h GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact hh.continuousOn.integrableOn_compact isCompact_univ
  have hsqInt : Integrable (fun θ => (h θ) ^ (2 : ℕ))
      GaloisForLFunctions.unitCircleHaar := by
    rw [← integrableOn_univ]
    exact (hh.pow 2).continuousOn.integrableOn_compact isCompact_univ
  have hmajorInt : Integrable (fun θ => (M + h θ₀) * h θ - h θ₀ * M)
      GaloisForLFunctions.unitCircleHaar := by
    fun_prop
  have hpoint : ∀ θ, (h θ) ^ (2 : ℕ) ≤ (M + h θ₀) * h θ - h θ₀ * M := by
    intro θ
    have hlow : h θ₀ ≤ h θ := hmin (Set.mem_univ θ)
    have hhi : h θ ≤ M := hupper θ
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hhi)]
  have hint := integral_mono hsqInt hmajorInt hpoint
  have hre := Complex.reCLM.integral_comp_comm hfInt
  have hzero : (∫ θ, h θ ∂GaloisForLFunctions.unitCircleHaar) = 0 := by
    change (∫ θ, Complex.reCLM (f θ) ∂GaloisForLFunctions.unitCircleHaar) = 0
    rw [hre, hmean]
    simp
  have hbound :
      (∫ θ, (h θ) ^ (2 : ℕ) ∂GaloisForLFunctions.unitCircleHaar) ≤ -h θ₀ * M := by
    have hmulInt : Integrable (fun θ => (M + h θ₀) * h θ)
        GaloisForLFunctions.unitCircleHaar := hhInt.const_mul _
    have hconstInt : Integrable (fun _θ : UnitAddCircle => h θ₀ * M)
        GaloisForLFunctions.unitCircleHaar := integrable_const _
    calc
      (∫ θ, (h θ) ^ (2 : ℕ) ∂GaloisForLFunctions.unitCircleHaar) ≤
          ∫ θ, ((M + h θ₀) * h θ - h θ₀ * M)
            ∂GaloisForLFunctions.unitCircleHaar := hint
      _ = -h θ₀ * M := by
        rw [MeasureTheory.integral_sub hmulInt hconstInt,
          MeasureTheory.integral_const_mul,
          hzero, mul_zero, MeasureTheory.integral_const]
        simp
  refine ⟨θ₀, ?_⟩
  change h θ₀ ≤ -_ / M
  apply (le_div_iff₀ hM).2
  nlinarith

/-- Total absolute mass of all nonzero HCF Fourier-source coefficients. -/
def criticalFeatureSourceAliasCoefficientMass
    (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℤ, ‖if n = 0 then 0 else
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n‖

/-- Real phase variance of the complete HCF source alias. -/
def criticalFeatureSourceAliasRealVariance
    (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ θ : UnitAddCircle,
    ((criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g).re) ^ (2 : ℕ)
      ∂GaloisForLFunctions.unitCircleHaar

theorem norm_criticalFeatureSourceNonzeroFourierAliasAtPhase_le_coefficientMass
    (θ : UnitAddCircle) (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ) :
    ‖criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g‖ ≤
      criticalFeatureSourceAliasCoefficientMass μ g := by
  let a : ℤ → ℂ := fun n => if n = 0 then 0 else
    (criticalFeatureFourierMode n : ℂ) *
      criticalFeatureSourceFourierCoefficient μ g n
  have hbase : Summable fun n : ℤ =>
      (criticalFeatureFourierMode n : ℂ) *
        criticalFeatureSourceFourierCoefficient μ g n :=
    summable_criticalFeatureWeightedSourceFourierCoefficient μ hg
  have ha : Summable a := by
    exact Summable.of_norm_bounded hbase.norm fun n => by
      by_cases hn : n = 0
      · subst n
        simp only [a, if_pos, norm_zero, norm_mul]
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · simp [a, hn]
  have hphase : Summable fun n : ℤ => a n * fourier n θ := by
    exact Summable.of_norm_bounded ha.norm fun n => by
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hnorm : (∑' n : ℤ, ‖a n * fourier n θ‖) = ∑' n : ℤ, ‖a n‖ := by
    apply tsum_congr
    intro n
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  calc
    ‖criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g‖ ≤
        ∑' n : ℤ, ‖a n * fourier n θ‖ := by
      simpa only [criticalFeatureSourceNonzeroFourierAliasAtPhase,
        a, ite_mul, zero_mul] using
          (norm_tsum_le_tsum_norm hphase.norm)
    _ = ∑' n : ℤ, ‖a n‖ := hnorm
    _ = criticalFeatureSourceAliasCoefficientMass μ g := by
      rfl

/-- Quantitative source phase selection: alias variance forces a definite saving below zero
mode. -/
theorem exists_criticalFeatureSourceAliasPhase_re_le_neg_variance_div
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ)
    (hmass : 0 < criticalFeatureSourceAliasCoefficientMass μ g) :
    ∃ θ : UnitAddCircle,
      (criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g).re ≤
        -criticalFeatureSourceAliasRealVariance μ g /
          criticalFeatureSourceAliasCoefficientMass μ g := by
  apply exists_re_le_neg_variance_div_of_zeroMean
    (fun θ => criticalFeatureSourceNonzeroFourierAliasAtPhase θ μ g)
    (continuous_criticalFeatureSourceNonzeroFourierAliasAtPhase μ hg)
    (criticalFeatureSourceAliasCoefficientMass μ g) hmass
  · intro θ
    exact (Complex.re_le_norm _).trans
      (norm_criticalFeatureSourceNonzeroFourierAliasAtPhase_le_coefficientMass θ μ hg)
  · exact integral_criticalFeatureSourceNonzeroFourierAliasAtPhase_eq_zero μ hg

/-- Quantitative pre-divisor scalarization. Phase selection lowers the full HCF periodization
below its zero Fourier mode by alias variance divided by coefficient mass. -/
theorem exists_real_criticalFeaturePeriodization_le_zeroMode_sub_variance_div
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Integrable g μ)
    (hmass : 0 < criticalFeatureSourceAliasCoefficientMass μ g) :
    ∃ θ : ℝ,
      (∫ x, criticalFeatureRealBoundaryPeriodization (x + θ) * g x ∂μ) ≤
        2 * Real.pi * ∫ x, g x ∂μ -
          criticalFeatureSourceAliasRealVariance μ g /
            criticalFeatureSourceAliasCoefficientMass μ g := by
  obtain ⟨ϑ, hϑ⟩ :=
    exists_criticalFeatureSourceAliasPhase_re_le_neg_variance_div μ hg hmass
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective ϑ
  refine ⟨θ, ?_⟩
  have hid :=
    ofReal_integral_criticalFeatureRealBoundaryPeriodization_add_mul_sub_zeroMode_eq_aliasAtPhase
      θ μ hg
  have hre := congrArg Complex.re hid
  simp only [ofReal_re] at hre
  rw [← hre] at hϑ
  calc
    (∫ x, criticalFeatureRealBoundaryPeriodization (x + θ) * g x ∂μ) =
        ((∫ x, criticalFeatureRealBoundaryPeriodization (x + θ) * g x ∂μ) -
          2 * Real.pi * ∫ x, g x ∂μ) +
          2 * Real.pi * ∫ x, g x ∂μ := by ring
    _ ≤ (-criticalFeatureSourceAliasRealVariance μ g /
          criticalFeatureSourceAliasCoefficientMass μ g) +
          2 * Real.pi * ∫ x, g x ∂μ :=
      by
        simpa only [add_comm] using
          add_le_add_right hϑ (2 * Real.pi * ∫ x, g x ∂μ)
    _ = 2 * Real.pi * ∫ x, g x ∂μ -
          criticalFeatureSourceAliasRealVariance μ g /
            criticalFeatureSourceAliasCoefficientMass μ g := by ring

end

end RHTower
