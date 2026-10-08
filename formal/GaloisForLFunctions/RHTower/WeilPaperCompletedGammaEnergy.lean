import GaloisForLFunctions.RHTower.WeilPaperPositiveExpectation
import GaloisForLFunctions.RHTower.WeilPaperConstrainedLogMinimizers

/-!
# Actual compensated gamma energy on completed Weil spectral families

The gamma symbol plus the explicit coercivity constant is a continuous
nonnegative weight. Its extended expectation agrees with native compensated
energy and retains its budget in the actual completion. This pays gamma
integrability and gives constrained minima of the actual gamma expectation.
-/

open MeasureTheory Filter Set Topology Zeta23
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

theorem continuous_paperSpectralGammaWeight : Continuous paperSpectralGammaWeight :=
  WeilHerglotz.continuous_gammaBracket.comp (continuous_const.mul continuous_id)

private theorem gammaCost_nonneg (ξ : ℝ) :
    0 ≤ paperSpectralGammaWeight ξ + (10 + Real.log 4) :=
  (paperSpectralLogWeight_nonneg ξ).trans (paperSpectralLogWeight_le_gamma ξ)

/-- The actual gamma symbol with the explicit constant making it nonnegative. -/
def paperGammaCostWeight : C(ℝ, ℝ≥0) :=
  ⟨fun ξ => ⟨paperSpectralGammaWeight ξ + (10 + Real.log 4), gammaCost_nonneg ξ⟩,
    (continuous_paperSpectralGammaWeight.add continuous_const).subtype_mk _⟩

@[simp] theorem paperGammaCostWeight_coe (ξ : ℝ) :
    (paperGammaCostWeight ξ : ℝ) = paperSpectralGammaWeight ξ + (10 + Real.log 4) := rfl

/-- Extended actual compensated energy of an arbitrary real probability law. -/
def paperExtendedCompensatedEnergy (μ : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  paperPositiveExpectation paperGammaCostWeight μ

theorem paperExtendedCompensatedEnergy_eq_lintegral (μ : ProbabilityMeasure ℝ) :
    paperExtendedCompensatedEnergy μ =
      ∫⁻ ξ, ENNReal.ofReal (paperSpectralGammaWeight ξ + (10 + Real.log 4)) ∂(μ : Measure ℝ) :=
  paperPositiveExpectation_eq_lintegral_ofReal paperGammaCostWeight μ

/-- Actual compensated energy is weakly lower semicontinuous as an extended expectation. -/
theorem lowerSemicontinuous_paperExtendedCompensatedEnergy :
    LowerSemicontinuous paperExtendedCompensatedEnergy :=
  lowerSemicontinuous_paperPositiveExpectation paperGammaCostWeight

theorem isClosed_paperExtendedCompensatedEnergy_sublevel (B : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure ℝ | paperExtendedCompensatedEnergy μ ≤ B} :=
  lowerSemicontinuous_paperExtendedCompensatedEnergy.isClosed_preimage B

/-- On native finite mixtures this extended cost is exactly the original compensated energy. -/
theorem paperExtendedCompensatedEnergy_spectralProbability (c : NormalizedMixture) :
    paperExtendedCompensatedEnergy (spectralProbability c) =
      ENNReal.ofReal (paperPoleCompensatedEnergy c) := by
  have hi : Integrable (fun ξ => paperSpectralGammaWeight ξ + (10 + Real.log 4))
      (spectralProbability c : Measure ℝ) :=
    (integrable_paperSpectralGammaWeight c).add (integrable_const (10 + Real.log 4))
  rw [paperExtendedCompensatedEnergy_eq_lintegral,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall gammaCost_nonneg)]
  congr 1
  rw [integral_add (integrable_paperSpectralGammaWeight c) (integrable_const _),
    integral_paperSpectralGammaWeight, integral_const, probReal_univ, one_smul]
  simp only [paperPoleCompensatedEnergy, energy_eq_paperMixturePole_add_gamma,
    add_sub_cancel_left]

/-- The original compensated energy budget itself survives completion. -/
theorem paperExtendedCompensatedEnergy_completion_le (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    paperExtendedCompensatedEnergy μ.1 ≤ ENNReal.ofReal B := by
  apply closure_minimal
    (t := {ν | paperExtendedCompensatedEnergy ν ≤ ENNReal.ofReal B})
    ?_ (isClosed_paperExtendedCompensatedEnergy_sublevel _) μ.2
  rintro _ ⟨c, hc, rfl⟩
  change paperExtendedCompensatedEnergy (spectralProbability c) ≤ ENNReal.ofReal B
  rw [paperExtendedCompensatedEnergy_spectralProbability]
  exact ENNReal.ofReal_le_ofReal hc

/-- Finite completed energy pays integrability of the nonnegative gamma cost. -/
theorem integrable_paperGammaCost_completion (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    Integrable (fun ξ => paperSpectralGammaWeight ξ + (10 + Real.log 4))
      (μ.1 : Measure ℝ) := by
  refine ⟨(continuous_paperSpectralGammaWeight.add continuous_const).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall gammaCost_nonneg)).mpr
  rw [← paperExtendedCompensatedEnergy_eq_lintegral]
  exact (paperExtendedCompensatedEnergy_completion_le B μ).trans_lt ENNReal.ofReal_lt_top

/-- The original signed gamma symbol is integrable for every completed law. -/
theorem integrable_paperSpectralGammaWeight_completion (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    Integrable paperSpectralGammaWeight (μ.1 : Measure ℝ) := by
  have hi : Integrable (fun ξ =>
      (paperSpectralGammaWeight ξ + (10 + Real.log 4)) - (10 + Real.log 4))
      (μ.1 : Measure ℝ) :=
    (integrable_paperGammaCost_completion B μ).sub (integrable_const (10 + Real.log 4))
  simpa only [add_sub_cancel_right] using hi

private theorem integral_gammaCost_completion (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    (∫ ξ, paperSpectralGammaWeight ξ + (10 + Real.log 4) ∂(μ.1 : Measure ℝ)) =
      (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) + (10 + Real.log 4) := by
  rw [integral_add (integrable_paperSpectralGammaWeight_completion B μ) (integrable_const _),
    integral_const, probReal_univ, one_smul]

private theorem integral_gammaCost_nonneg (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    0 ≤ (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) + (10 + Real.log 4) := by
  rw [← integral_gammaCost_completion B μ]
  exact integral_nonneg gammaCost_nonneg

/-- Extended compensated energy equals the finite actual gamma expectation plus the constant. -/
theorem paperExtendedCompensatedEnergy_completion_eq (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    paperExtendedCompensatedEnergy μ.1 =
      ENNReal.ofReal ((∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) + (10 + Real.log 4)) := by
  rw [paperExtendedCompensatedEnergy_eq_lintegral,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_paperGammaCost_completion B μ)
      (Filter.Eventually.of_forall gammaCost_nonneg), integral_gammaCost_completion]

/-- The real gamma expectation retains the original compensated budget. -/
theorem integral_paperGammaCost_completion_le (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) + (10 + Real.log 4) ≤ B := by
  have h := paperExtendedCompensatedEnergy_completion_le B μ
  rw [paperExtendedCompensatedEnergy_completion_eq] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (integral_gammaCost_nonneg B μ),
    ENNReal.toReal_ofReal (paperPoleCompensatedCompletion_budget_nonneg B μ)] using hr

/-- The extended logarithmic moment is dominated by actual compensated energy for every law. -/
theorem paperExtendedLogMoment_le_compensatedEnergy (μ : ProbabilityMeasure ℝ) :
    paperExtendedLogMoment μ ≤ paperExtendedCompensatedEnergy μ := by
  rw [paperExtendedCompensatedEnergy_eq_lintegral]
  exact lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (paperSpectralLogWeight_le_gamma ξ)

private theorem gammaIntegral_le_of_extended_le (B : ℝ)
    (μ ν : PaperPoleCompensatedCompletion B)
    (h : paperExtendedCompensatedEnergy μ.1 ≤ paperExtendedCompensatedEnergy ν.1) :
    (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ≤
      ∫ ξ, paperSpectralGammaWeight ξ ∂(ν.1 : Measure ℝ) := by
  rw [paperExtendedCompensatedEnergy_completion_eq,
    paperExtendedCompensatedEnergy_completion_eq] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (integral_gammaCost_nonneg B μ),
    ENNReal.toReal_ofReal (integral_gammaCost_nonneg B ν)] at hr
  exact (add_le_add_iff_right (10 + Real.log 4)).mp hr

/-- Every native law supplies a compact completion with a minimum actual gamma expectation. -/
theorem exists_paperCompletedGammaEnergy_minimizer (c : NormalizedMixture) :
    ∃ μ : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c),
      ∀ ν : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c),
        (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ≤
          ∫ ξ, paperSpectralGammaWeight ξ ∂(ν.1 : Measure ℝ) := by
  let μ₀ : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c) :=
    ⟨spectralProbability c, subset_closure ⟨c,
      show paperPoleCompensatedEnergy c ≤ paperPoleCompensatedEnergy c from le_rfl, rfl⟩⟩
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨μ₀, Set.mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_paperExtendedCompensatedEnergy.comp
      (continuous_subtype_val : Continuous
        (fun ν : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c) => ν.1))).lowerSemicontinuousOn Set.univ)
  exact ⟨μ, fun ν => gammaIntegral_le_of_extended_le _ μ ν (hμ (Set.mem_univ ν))⟩

/-- Gamma integrability is paid on every completed family with prescribed observations. -/
theorem integrable_paperObservedSpectralCompletion_gammaWeight
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    Integrable paperSpectralGammaWeight (μ.1 : Measure ℝ) :=
  integrable_paperSpectralGammaWeight_completion _
    ⟨μ.1, paperObservedSpectralCompletion_subset_budget c F μ.2⟩

theorem paperObservedSpectralCompletion_gammaCost_le
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) + (10 + Real.log 4) ≤
      paperPoleCompensatedEnergy c.1 :=
  integral_paperGammaCost_completion_le _
    ⟨μ.1, paperObservedSpectralCompletion_subset_budget c F μ.2⟩

/-- Actual gamma energy attains a minimum preserving every observation and origin constraint. -/
theorem exists_paperObservedGammaEnergy_minimizer
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    ∃ μ : PaperObservedSpectralCompletion c F,
      ∀ ν : PaperObservedSpectralCompletion c F,
        (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ≤
          ∫ ξ, paperSpectralGammaWeight ξ ∂(ν.1 : Measure ℝ) := by
  let μ₀ : PaperObservedSpectralCompletion c F :=
    ⟨spectralProbability c.1, spectralProbability_mem_paperObservedSpectralCompletion c F⟩
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨μ₀, Set.mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_paperExtendedCompensatedEnergy.comp
      (continuous_subtype_val : Continuous
        (fun ν : PaperObservedSpectralCompletion c F => ν.1))).lowerSemicontinuousOn Set.univ)
  refine ⟨μ, fun ν => ?_⟩
  exact gammaIntegral_le_of_extended_le _
    ⟨μ.1, paperObservedSpectralCompletion_subset_budget c F μ.2⟩
    ⟨ν.1, paperObservedSpectralCompletion_subset_budget c F ν.2⟩ (hμ (Set.mem_univ ν))

end RHTower.WeilWorkPBAP
