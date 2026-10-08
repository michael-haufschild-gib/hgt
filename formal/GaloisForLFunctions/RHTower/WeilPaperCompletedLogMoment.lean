import GaloisForLFunctions.RHTower.WeilPaperCompactSpectralRecovery
import GaloisForLFunctions.RHTower.WeilPaperPositiveExpectation

/-!
# Logarithmic moment control on the actual compact spectral completion

Bounded truncations make the extended logarithmic moment lower semicontinuous.
The native coercive estimate therefore survives closure, paying integrability
and the quantitative tail bound for every completed law.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The logarithmic moment on every real probability law, with infinity allowed. -/
def paperExtendedLogMoment (μ : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (paperSpectralLogWeight ξ) ∂(μ : Measure ℝ)

private def logPositiveWeight : C(ℝ, ℝ≥0) :=
  ⟨fun ξ => ⟨paperSpectralLogWeight ξ, paperSpectralLogWeight_nonneg ξ⟩,
    continuous_paperSpectralLogWeight.subtype_mk _⟩

/-- Extended logarithmic moment is lower semicontinuous for weak convergence. -/
theorem lowerSemicontinuous_paperExtendedLogMoment :
    LowerSemicontinuous paperExtendedLogMoment := by
  have heq : paperExtendedLogMoment = paperPositiveExpectation logPositiveWeight := by
    funext μ
    rw [paperPositiveExpectation_eq_lintegral_ofReal]
    rfl
  rw [heq]
  exact lowerSemicontinuous_paperPositiveExpectation logPositiveWeight

/-- Every extended logarithmic moment sublevel is weakly closed. -/
theorem isClosed_paperExtendedLogMoment_sublevel (B : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure ℝ | paperExtendedLogMoment μ ≤ B} :=
  lowerSemicontinuous_paperExtendedLogMoment.isClosed_preimage B

/-- The extended moment agrees with the already paid native logarithmic moment. -/
theorem paperExtendedLogMoment_spectralProbability (c : NormalizedMixture) :
    paperExtendedLogMoment (spectralProbability c) =
      ENNReal.ofReal (paperSpectralLogMoment c) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_paperSpectralLogWeight c)
    (Filter.Eventually.of_forall paperSpectralLogWeight_nonneg)).symm

/-- The original compensated budget survives in every completed spectral law. -/
theorem paperExtendedLogMoment_completion_le (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    paperExtendedLogMoment μ.1 ≤ ENNReal.ofReal B := by
  apply closure_minimal (t := {ν | paperExtendedLogMoment ν ≤ ENNReal.ofReal B})
    ?_ (isClosed_paperExtendedLogMoment_sublevel _) μ.2
  rintro _ ⟨c, hc, rfl⟩
  change paperExtendedLogMoment (spectralProbability c) ≤ ENNReal.ofReal B
  rw [paperExtendedLogMoment_spectralProbability]
  exact ENNReal.ofReal_le_ofReal
    ((paperSpectralLogMoment_le_pole_compensated_energy c).trans hc)

/-- A completed law itself witnesses that its compensated budget is nonnegative. -/
theorem paperPoleCompensatedCompletion_budget_nonneg (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) : 0 ≤ B := by
  have hs : paperPoleCompensatedSpectralLaws B ⊆
      {ν : ProbabilityMeasure ℝ | 0 ≤ B} := by
    rintro _ ⟨c, hc, rfl⟩
    exact (paperPoleCompensatedEnergy_nonneg c).trans hc
  have hc : IsClosed {ν : ProbabilityMeasure ℝ | 0 ≤ B} := by
    by_cases h : 0 ≤ B <;> simp [h]
  exact closure_minimal hs hc μ.2

/-- Logarithmic integrability of each completed law follows from the proved budget. -/
theorem integrable_paperSpectralLogWeight_completion (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    Integrable paperSpectralLogWeight (μ.1 : Measure ℝ) := by
  refine ⟨continuous_paperSpectralLogWeight.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall paperSpectralLogWeight_nonneg)).mpr
  exact (paperExtendedLogMoment_completion_le B μ).trans_lt ENNReal.ofReal_lt_top

/-- The real logarithmic moment of every completed law is bounded by its original budget. -/
theorem integral_paperSpectralLogWeight_completion_le (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    (∫ ξ, paperSpectralLogWeight ξ ∂(μ.1 : Measure ℝ)) ≤ B := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (paperExtendedLogMoment_completion_le B μ)
  change (∫⁻ ξ, ENNReal.ofReal (paperSpectralLogWeight ξ) ∂(μ.1 : Measure ℝ)).toReal ≤
    (ENNReal.ofReal B).toReal at h
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_paperSpectralLogWeight_completion B μ)
    (Filter.Eventually.of_forall paperSpectralLogWeight_nonneg),
    ENNReal.toReal_ofReal (integral_nonneg paperSpectralLogWeight_nonneg),
    ENNReal.toReal_ofReal (paperPoleCompensatedCompletion_budget_nonneg B μ)] at h
  exact h

/-- The quantitative logarithmic tail estimate remains valid beyond native finite mixtures. -/
theorem paperPoleCompensatedCompletion_tail_le (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) (R : ℝ≥0) :
    (μ.1 : Measure ℝ) {ξ : ℝ | (R : ℝ) < ‖ξ‖} ≤
      ENNReal.ofReal (B / paperSpectralLogWeight R) := by
  have hW := paperSpectralLogWeight_pos (R : ℝ)
  have hm := ((integrable_paperSpectralLogWeight_completion B μ).div_const
    (paperSpectralLogWeight R)).measure_le_integral
      (Filter.Eventually.of_forall fun ξ =>
        div_nonneg (paperSpectralLogWeight_nonneg ξ) hW.le)
      (s := {ξ : ℝ | (R : ℝ) < ‖ξ‖}) (by
        intro ξ hξ
        apply (le_div_iff₀ hW).mpr
        rw [one_mul, paperSpectralLogWeight_eq, paperSpectralLogWeight_eq,
          abs_of_nonneg R.coe_nonneg]
        apply Real.log_le_log (by positivity)
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_of_lt hξ)
          (by positivity : 0 ≤ 2 * Real.pi)))
  rw [integral_div] at hm
  exact hm.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (integral_paperSpectralLogWeight_completion_le B μ) hW.le))

/-- Every native law supplies a compact completion containing a logarithmic-moment minimizer. -/
theorem exists_paperCompletedLogMoment_minimizer (c : NormalizedMixture) :
    ∃ μ : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c),
      ∀ ν : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c),
        paperExtendedLogMoment μ.1 ≤ paperExtendedLogMoment ν.1 := by
  let μ₀ : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c) :=
    ⟨spectralProbability c, subset_closure ⟨c,
      show paperPoleCompensatedEnergy c ≤ paperPoleCompensatedEnergy c from le_rfl, rfl⟩⟩
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨μ₀, Set.mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_paperExtendedLogMoment.comp
      (continuous_subtype_val : Continuous
        (fun ν : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c) => ν.1))).lowerSemicontinuousOn Set.univ)
  exact ⟨μ, fun ν => hμ (Set.mem_univ ν)⟩

end RHTower.WeilWorkPBAP
