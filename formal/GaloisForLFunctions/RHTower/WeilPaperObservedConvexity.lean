import GaloisForLFunctions.RHTower.WeilPaperCovarianceEnergyCertificates
import GaloisForLFunctions.RHTower.WeilPaperNativeConvexGeometry
import GaloisForLFunctions.HTGeometry.ProbabilityMeasureSimplex
import Mathlib.Analysis.Convex.Basic

/-!
# Convex geometry of the actual observed spectral completion

Ordinary probability mixing agrees with native positive test mixing. It preserves
the compensated budget and all simultaneous complex observations, then passes to
the actual closure by joint weak continuity. Both covariance coordinates and the
integrable gamma objective are affine on the resulting completed segments.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
open GaloisForLFunctions.HTGeometry (probabilityMixture probabilityMixture_toMeasure)

/-- The existing probability mixture with the same orientation as native segments. -/
def paperRealProbabilitySegment (μ ν : ProbabilityMeasure ℝ) (t : Icc (0 : ℝ) 1) :
    ProbabilityMeasure ℝ :=
  probabilityMixture (ENNReal.ofReal t.1)
    (by simpa using ENNReal.ofReal_le_ofReal t.2.2) ν μ

private theorem integral_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ ν : ProbabilityMeasure ℝ) (t : Icc (0 : ℝ) 1)
    (f : ℝ → E) (hμ : Integrable f (μ : Measure ℝ)) (hν : Integrable f (ν : Measure ℝ)) :
    (∫ ξ, f ξ ∂(paperRealProbabilitySegment μ ν t : Measure ℝ)) =
      (1 - t.1) • (∫ ξ, f ξ ∂(μ : Measure ℝ)) + t.1 • (∫ ξ, f ξ ∂(ν : Measure ℝ)) := by
  change (∫ ξ, f ξ ∂(probabilityMixture _ _ ν μ : Measure ℝ)) = _
  rw [probabilityMixture_toMeasure, integral_add_measure
    (hν.smul_measure ENNReal.ofReal_ne_top)
    (hμ.smul_measure (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))),
    integral_smul_measure, integral_smul_measure]
  have hsub : (1 - ENNReal.ofReal t.1).toReal = 1 - t.1 := by
    rw [ENNReal.toReal_sub_of_le
      (by simpa using ENNReal.ofReal_le_ofReal t.2.2) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal t.2.1]
  rw [hsub, ENNReal.toReal_ofReal t.2.1, add_comm]

private theorem integrable_bounded {E : Type*} [NormedAddCommGroup E]
    (G : ℝ →ᵇ E) (μ : ProbabilityMeasure ℝ) : Integrable G (μ : Measure ℝ) :=
  (integrable_const (‖G‖ : ℝ)).mono' G.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall G.norm_coe_le_norm)

/-- Every bounded spectral expectation is affine under the actual probability mixture. -/
theorem integral_paperRealProbabilitySegment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (G : ℝ →ᵇ E)
    (μ ν : ProbabilityMeasure ℝ) (t : Icc (0 : ℝ) 1) :
    (∫ ξ, G ξ ∂(paperRealProbabilitySegment μ ν t : Measure ℝ)) =
      (1 - t.1) • (∫ ξ, G ξ ∂(μ : Measure ℝ)) + t.1 • (∫ ξ, G ξ ∂(ν : Measure ℝ)) :=
  integral_segment μ ν t G (integrable_bounded G μ) (integrable_bounded G ν)

/-- Mixing is jointly weakly continuous in both endpoint laws and the weight. -/
theorem continuous_paperRealProbabilitySegment :
    Continuous (fun p : Icc (0 : ℝ) 1 × ProbabilityMeasure ℝ × ProbabilityMeasure ℝ =>
      paperRealProbabilitySegment p.2.1 p.2.2 p.1) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro G
  simp only [integral_paperRealProbabilitySegment, smul_eq_mul]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).comp
      (continuous_fst.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).comp
        (continuous_snd.comp continuous_snd)))

/-- Native mixture interpolation is exactly ordinary real probability interpolation. -/
theorem spectralProbability_paperNormalizedSegment
    (a b : NormalizedMixture) (t : Icc (0 : ℝ) 1) :
    spectralProbability (paperNormalizedSegment a b t) =
      paperRealProbabilitySegment (spectralProbability a) (spectralProbability b) t := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro G
  rw [integral_spectralProbability_paperNormalizedSegment, integral_paperRealProbabilitySegment]
  rfl

/-- The actual pole-compensated budget is affine on native positive segments. -/
theorem paperPoleCompensatedEnergy_paperNormalizedSegment
    (a b : NormalizedMixture) (t : Icc (0 : ℝ) 1) :
    paperPoleCompensatedEnergy (paperNormalizedSegment a b t) =
      (1 - t.1) * paperPoleCompensatedEnergy a + t.1 * paperPoleCompensatedEnergy b := by
  unfold paperPoleCompensatedEnergy
  rw [paperNormalizedSegment_observe, paperNormalizedSegment_observe]
  simp only [smul_eq_mul]
  ring

variable {ι : Type*}

private theorem segment_mem_family (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    {μ ν : ProbabilityMeasure ℝ} (hμ : μ ∈ paperObservedSpectralFamily c F)
    (hν : ν ∈ paperObservedSpectralFamily c F) (t : Icc (0 : ℝ) 1) :
    paperRealProbabilitySegment μ ν t ∈ paperObservedSpectralFamily c F := by
  rcases hμ with ⟨a, ha, rfl⟩
  rcases hν with ⟨b, hb, rfl⟩
  refine ⟨paperComplexNullSegment a b t, ⟨?_, ?_⟩, ?_⟩
  · change paperPoleCompensatedEnergy (paperNormalizedSegment a.1 b.1 t) ≤ _
    rw [paperPoleCompensatedEnergy_paperNormalizedSegment]
    calc
      _ ≤ (1 - t.1) * paperPoleCompensatedEnergy c.1 +
          t.1 * paperPoleCompensatedEnergy c.1 :=
        add_le_add (mul_le_mul_of_nonneg_left ha.1 (sub_nonneg.mpr t.2.2))
          (mul_le_mul_of_nonneg_left hb.1 t.2.1)
      _ = _ := by ring
  · intro i
    change (∫ ξ, F i ξ ∂(spectralProbability (paperNormalizedSegment a.1 b.1 t) : Measure ℝ)) = _
    rw [spectralProbability_paperNormalizedSegment, integral_paperRealProbabilitySegment,
      ha.2 i, hb.2 i, ← add_smul, sub_add_cancel, one_smul]
  · exact spectralProbability_paperNormalizedSegment a.1 b.1 t

/-- Mixtures of completed laws remain in the closure of the actual simultaneously
constrained native family; no replacement feasible set is introduced. -/
theorem paperRealProbabilitySegment_mem_observedCompletion
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) (t : Icc (0 : ℝ) 1) :
    paperRealProbabilitySegment μ.1 ν.1 t ∈ PaperObservedSpectralCompletion c F := by
  have hc : Continuous (fun p : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ =>
      paperRealProbabilitySegment p.1 p.2 t) :=
    continuous_paperRealProbabilitySegment.comp (continuous_const.prodMk continuous_id)
  have hm : MapsTo (fun p : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ =>
      paperRealProbabilitySegment p.1 p.2 t)
      (paperObservedSpectralFamily c F ×ˢ paperObservedSpectralFamily c F)
      (paperObservedSpectralFamily c F) := fun _ h => segment_mem_family c F h.1 h.2 t
  have hp : (μ.1, ν.1) ∈ closure
      (paperObservedSpectralFamily c F ×ˢ paperObservedSpectralFamily c F) := by
    rw [closure_prod_eq]
    exact ⟨μ.2, ν.2⟩
  exact hm.closure hc hp

/-- A genuine segment inside the compact observed spectral completion. -/
def paperObservedProbabilitySegment
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) (t : Icc (0 : ℝ) 1) :
    PaperObservedSpectralCompletion c F :=
  ⟨paperRealProbabilitySegment μ.1 ν.1 t,
    paperRealProbabilitySegment_mem_observedCompletion c F μ ν t⟩

/-- All real and complex bounded expectations remain affine after completion. -/
theorem integral_paperObservedProbabilitySegment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (G : ℝ →ᵇ E) (μ ν : PaperObservedSpectralCompletion c F) (t : Icc (0 : ℝ) 1) :
    (∫ ξ, G ξ ∂((paperObservedProbabilitySegment c F μ ν t).1 : Measure ℝ)) =
      (1 - t.1) • (∫ ξ, G ξ ∂(μ.1 : Measure ℝ)) + t.1 • (∫ ξ, G ξ ∂(ν.1 : Measure ℝ)) :=
  integral_paperRealProbabilitySegment G μ.1 ν.1 t

/-- The unbounded gamma objective is affine because its integrability has already
been established at every completed law. -/
theorem paperPerturbedGammaExpectation_observedSegment
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ ν : PaperObservedSpectralCompletion c F) (t : Icc (0 : ℝ) 1) :
    paperPerturbedGammaExpectation G (paperObservedProbabilitySegment c F μ ν t).1 =
      (1 - t.1) * paperPerturbedGammaExpectation G μ.1 +
        t.1 * paperPerturbedGammaExpectation G ν.1 := by
  unfold paperPerturbedGammaExpectation
  change (∫ ξ, paperSpectralGammaWeight ξ ∂(paperRealProbabilitySegment μ.1 ν.1 t : Measure ℝ)) +
    (∫ ξ, G ξ ∂(paperRealProbabilitySegment μ.1 ν.1 t : Measure ℝ)) = _
  rw [integral_segment μ.1 ν.1 t paperSpectralGammaWeight
    (integrable_paperObservedSpectralCompletion_gammaWeight c F μ)
    (integrable_paperObservedSpectralCompletion_gammaWeight c F ν),
    integral_paperRealProbabilitySegment]
  simp only [smul_eq_mul]
  ring

/-- Every phase covariance is an affine coordinate on the completed law space. -/
theorem paperObservedPhaseCovariances_segment
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) (t : Icc (0 : ℝ) 1) :
    paperObservedPhaseCovariances c F (paperObservedProbabilitySegment c F μ ν t) =
      (1 - t.1) • paperObservedPhaseCovariances c F μ +
        t.1 • paperObservedPhaseCovariances c F ν := by
  funext k
  exact integral_paperObservedProbabilitySegment c F (paperPhaseCovarianceProbe k) μ ν t

/-- The compact range of realized covariance arrays is a convex set. -/
theorem convex_paperObservedPhaseCovariances_range
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    Convex ℝ (Set.range (paperObservedPhaseCovariances c F)) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  let t : Icc (0 : ℝ) 1 := ⟨b, hb, by linarith⟩
  refine ⟨paperObservedProbabilitySegment c F μ ν t, ?_⟩
  rw [paperObservedPhaseCovariances_segment]
  change (1 - b) • _ + b • _ = a • _ + b • _
  rw [show 1 - b = a by linarith]

end RHTower.WeilWorkPBAP
