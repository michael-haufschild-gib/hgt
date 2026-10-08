import GaloisForLFunctions.RHTower.WeilPaperCompletedLogMoment
import GaloisForLFunctions.RHTower.WeilPaperCompactEnergyObstruction

/-!
# Logarithmic-moment minimizers preserving native Weil observations

Complete the actual complex-null native family satisfying a compensated budget
and prescribed bounded continuous observations. The completion retains every
observation and every integer origin constraint, and contains a minimizer of
the real logarithmic moment. No feasibility or integrability premise is needed:
the supplied native law proves feasibility, and coercivity pays integrability.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

variable {ι : Type*}

/-- Actual complex-null native laws with the base law's budget and exact observations. -/
def paperObservedSpectralFamily (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    Set (ProbabilityMeasure ℝ) :=
  (fun d : ComplexNullMixture => spectralProbability d.1) ''
    {d | paperPoleCompensatedEnergy d.1 ≤ paperPoleCompensatedEnergy c.1 ∧
      ∀ i, (∫ ξ, F i ξ ∂(spectralProbability d.1 : Measure ℝ)) =
        ∫ ξ, F i ξ ∂(spectralProbability c.1 : Measure ℝ)}

/-- The completion of the actual family, including its observation constraints. -/
abbrev PaperObservedSpectralCompletion (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :=
  closure (paperObservedSpectralFamily c F)

/-- The base law belongs to its observed completion, so feasibility is proved. -/
theorem spectralProbability_mem_paperObservedSpectralCompletion
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    spectralProbability c.1 ∈ PaperObservedSpectralCompletion c F := by
  apply subset_closure
  exact ⟨c, ⟨show paperPoleCompensatedEnergy c.1 ≤ paperPoleCompensatedEnergy c.1 from le_rfl,
    fun _ => rfl⟩, rfl⟩

/-- Completing the constrained native family stays within the proved compact budget. -/
theorem paperObservedSpectralCompletion_subset_budget
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    PaperObservedSpectralCompletion c F ⊆
      PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c.1) := by
  apply closure_mono
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨d.1, hd.1, rfl⟩

/-- Each actual observed completion is compact. -/
theorem isCompact_paperObservedSpectralCompletion
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    IsCompact (PaperObservedSpectralCompletion c F) :=
  (isCompact_closure_paperPoleCompensatedSpectralLaws _).of_isClosed_subset
    isClosed_closure (paperObservedSpectralCompletion_subset_budget c F)

instance instCompactSpacePaperObservedSpectralCompletion
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    CompactSpace (PaperObservedSpectralCompletion c F) :=
  isCompact_iff_compactSpace.mp (isCompact_paperObservedSpectralCompletion c F)

private theorem continuous_complex_observable (G : ℝ →ᵇ ℂ) :
    Continuous (fun μ : ProbabilityMeasure ℝ => ∫ ξ, G ξ ∂(μ : Measure ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  have ht : Tendsto (id : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (𝓝 μ) (𝓝 μ) :=
    tendsto_id
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp ht G

/-- Every prescribed complex observation survives passage to the completion. -/
theorem paperObservedSpectralCompletion_observation
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (i : ι) :
    (∫ ξ, F i ξ ∂(μ.1 : Measure ℝ)) =
      ∫ ξ, F i ξ ∂(spectralProbability c.1 : Measure ℝ) := by
  have hc := isClosed_eq (continuous_complex_observable (F i))
    (continuous_const (y := ∫ ξ, F i ξ ∂(spectralProbability c.1 : Measure ℝ)))
  apply closure_minimal ?_ hc μ.2
  rintro _ ⟨d, hd, rfl⟩
  exact hd.2 i

/-- All infinitely many integer origin constraints survive in the completed real law. -/
theorem paperObservedSpectralCompletion_represents_origin
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    ∀ n : ℕ, 2 ≤ n →
      ∫ z, arithmeticPhase n z ∂(paperPrimeSpectralPushforward μ.1 : Measure PrimePhaseSpace) = 0 := by
  have hc := isClosed_representingPhaseMeasures.preimage continuous_paperPrimeSpectralPushforward
  apply closure_minimal ?_ hc μ.2
  rintro _ ⟨d, _, rfl⟩
  exact (spectralRepresentingMeasure d).2

/-- Every completed feasible law has a finite logarithmic moment. -/
theorem integrable_paperObservedSpectralCompletion_logWeight
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    Integrable paperSpectralLogWeight (μ.1 : Measure ℝ) :=
  integrable_paperSpectralLogWeight_completion _
    ⟨μ.1, paperObservedSpectralCompletion_subset_budget c F μ.2⟩

/-- The original native compensated budget bounds every completed feasible logarithmic moment. -/
theorem paperObservedSpectralCompletion_logMoment_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    (∫ ξ, paperSpectralLogWeight ξ ∂(μ.1 : Measure ℝ)) ≤ paperPoleCompensatedEnergy c.1 :=
  integral_paperSpectralLogWeight_completion_le _
    ⟨μ.1, paperObservedSpectralCompletion_subset_budget c F μ.2⟩

/-- A real logarithmic-moment minimizer exists while retaining all prescribed observations. -/
theorem exists_paperObservedLogMoment_minimizer
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    ∃ μ : PaperObservedSpectralCompletion c F,
      ∀ ν : PaperObservedSpectralCompletion c F,
        (∫ ξ, paperSpectralLogWeight ξ ∂(μ.1 : Measure ℝ)) ≤
          ∫ ξ, paperSpectralLogWeight ξ ∂(ν.1 : Measure ℝ) := by
  let μ₀ : PaperObservedSpectralCompletion c F :=
    ⟨spectralProbability c.1, spectralProbability_mem_paperObservedSpectralCompletion c F⟩
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨μ₀, Set.mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_paperExtendedLogMoment.comp
      (continuous_subtype_val : Continuous
        (fun ν : PaperObservedSpectralCompletion c F => ν.1))).lowerSemicontinuousOn Set.univ)
  refine ⟨μ, fun ν => ?_⟩
  have h := hμ (Set.mem_univ ν)
  have heq (η : PaperObservedSpectralCompletion c F) :
      paperExtendedLogMoment η.1 =
        ENNReal.ofReal (∫ ξ, paperSpectralLogWeight ξ ∂(η.1 : Measure ℝ)) :=
    (ofReal_integral_eq_lintegral_ofReal
      (integrable_paperObservedSpectralCompletion_logWeight c F η)
      (Filter.Eventually.of_forall paperSpectralLogWeight_nonneg)).symm
  change paperExtendedLogMoment μ.1 ≤ paperExtendedLogMoment ν.1 at h
  rw [heq, heq] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg paperSpectralLogWeight_nonneg)] using hr

/-- The entire constrained completion retains faithful, continuous prime-torus recovery. -/
theorem isClosedEmbedding_paperObservedSpectralPushforward
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    IsClosedEmbedding (fun μ : PaperObservedSpectralCompletion c F =>
      paperPrimeSpectralPushforward μ.1) := by
  apply (continuous_paperPrimeSpectralPushforward.comp continuous_subtype_val).isClosedEmbedding
  intro μ ν h
  exact Subtype.ext (paperPrimeSpectralPushforward_injective h)

end RHTower.WeilWorkPBAP
