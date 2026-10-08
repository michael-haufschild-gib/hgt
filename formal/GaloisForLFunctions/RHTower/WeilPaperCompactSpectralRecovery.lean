import GaloisForLFunctions.RHTower.WeilPaperSpectralCompactness
import GaloisForLFunctions.RHTower.WeilPaperTorusSpectralClassification
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuous recovery of the real spectral law on every compensated-energy completion

Prime-torus pushforward is injective on all real probability laws: rational
character moments determine a dense set of real characteristic-function values.
On each proved compact compensated-energy completion it is a closed embedding,
so its inverse is continuous, including at limits beyond finite mixtures.
-/

open MeasureTheory Filter Set Topology
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- Prime-torus pushforward on every real probability law. -/
def paperPrimeSpectralPushforward (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure PrimePhaseSpace :=
  μ.map continuous_primeSpectralPoint.measurable.aemeasurable

theorem continuous_paperPrimeSpectralPushforward : Continuous paperPrimeSpectralPushforward :=
  ProbabilityMeasure.continuous_map continuous_primeSpectralPoint

@[simp] theorem paperPrimeSpectralPushforward_spectralProbability (c : NormalizedMixture) :
    paperPrimeSpectralPushforward (spectralProbability c) = spectralTorusProbability c := rfl

/-- Rational character moments recover characteristic-function values for arbitrary laws. -/
theorem phaseMoment_paperPrimeSpectralPushforward (μ : ProbabilityMeasure ℝ)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    phaseMoment (paperPrimeSpectralPushforward μ) a b =
      charFun (μ : Measure ℝ) (2 * Real.pi * (Real.log a - Real.log b)) := by
  have hcont : Continuous (fun z : PrimePhaseSpace =>
      arithmeticPhase a z * (starRingEnd ℂ) (arithmeticPhase b z)) :=
    (arithmeticPhase a).continuous.mul (arithmeticPhase b).continuous.star
  unfold phaseMoment paperPrimeSpectralPushforward
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map continuous_primeSpectralPoint.measurable.aemeasurable hcont.aestronglyMeasurable,
    charFun_apply_real]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [rationalPhase_primeSpectralPoint ha hb]
    congr 1
    push_cast
    ring

/-- No real probability law loses information under the compact prime-torus representation. -/
theorem paperPrimeSpectralPushforward_injective : Function.Injective paperPrimeSpectralPushforward := by
  intro μ ν h
  have hk : (fun y : ℝ => charFun (μ : Measure ℝ) (2 * Real.pi * y)) =
      fun y : ℝ => charFun (ν : Measure ℝ) (2 * Real.pi * y) := by
    apply Continuous.ext_on dense_log_nat_ratios
      (continuous_charFun.comp (continuous_const.mul continuous_id))
      (continuous_charFun.comp (continuous_const.mul continuous_id))
    rintro y ⟨a, b, ha, hb, rfl⟩
    have hm := congrArg (fun η : ProbabilityMeasure PrimePhaseSpace => phaseMoment η a b) h
    simpa only [phaseMoment_paperPrimeSpectralPushforward _ ha hb,
      Function.comp_def, Pi.mul_apply, id_eq] using hm
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
    field_simp [Real.pi_ne_zero]
  simpa only [ht] using congrFun hk (t / (2 * Real.pi))

/-- The same pushforward restricted to the actual compact spectral completion. -/
def paperCompletedSpectralPushforward (B : ℝ) :
    C(PaperPoleCompensatedCompletion B, ProbabilityMeasure PrimePhaseSpace) :=
  ⟨fun μ => paperPrimeSpectralPushforward μ.1,
    continuous_paperPrimeSpectralPushforward.comp continuous_subtype_val⟩

/-- Every compensated budget supplies a closed embedding into the prime-torus law space. -/
theorem isClosedEmbedding_paperCompletedSpectralPushforward (B : ℝ) :
    IsClosedEmbedding (paperCompletedSpectralPushforward B) := by
  apply (paperCompletedSpectralPushforward B).continuous.isClosedEmbedding
  intro μ ν h
  apply Subtype.ext
  exact paperPrimeSpectralPushforward_injective h

/-- The image of each compensated spectral completion is compact. -/
theorem isCompact_paperCompletedSpectralPushforward_range (B : ℝ) :
    IsCompact (Set.range (paperCompletedSpectralPushforward B)) := by
  simpa only [Set.image_univ] using
    isCompact_univ.image (paperCompletedSpectralPushforward B).continuous

/-- Real spectral completion and its compact prime-torus image have identical topologies. -/
def paperSpectralRecoveryHomeomorph (B : ℝ) :
    PaperPoleCompensatedCompletion B ≃ₜ Set.range (paperCompletedSpectralPushforward B) :=
  (isClosedEmbedding_paperCompletedSpectralPushforward B).isEmbedding.toHomeomorph

@[simp] theorem paperSpectralRecoveryHomeomorph_apply (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    (paperSpectralRecoveryHomeomorph B μ).1 = paperPrimeSpectralPushforward μ.1 := rfl

/-- Continuous recovery of the unique real spectral lift, including completed limit laws. -/
def paperSpectralRecovery (B : ℝ) :
    C(Set.range (paperCompletedSpectralPushforward B), PaperPoleCompensatedCompletion B) :=
  ⟨(paperSpectralRecoveryHomeomorph B).symm, (paperSpectralRecoveryHomeomorph B).symm.continuous⟩

@[simp] theorem paperSpectralRecovery_roundtrip (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    paperSpectralRecovery B (paperSpectralRecoveryHomeomorph B μ) = μ :=
  (paperSpectralRecoveryHomeomorph B).symm_apply_apply μ

@[simp] theorem paperCompletedSpectralPushforward_recovery (B : ℝ)
    (ν : Set.range (paperCompletedSpectralPushforward B)) :
    paperCompletedSpectralPushforward B (paperSpectralRecovery B ν) = ν.1 :=
  congrArg Subtype.val ((paperSpectralRecoveryHomeomorph B).apply_symm_apply ν)

/-- Weak convergence in the compact torus and in the real spectral completion are equivalent. -/
theorem tendsto_paperCompletedSpectralPushforward_iff (B : ℝ)
    {α : Type*} {l : Filter α} {μ : α → PaperPoleCompensatedCompletion B}
    {μ₀ : PaperPoleCompensatedCompletion B} :
    Tendsto μ l (𝓝 μ₀) ↔
      Tendsto (fun i => paperPrimeSpectralPushforward (μ i).1) l
        (𝓝 (paperPrimeSpectralPushforward μ₀.1)) :=
  (isClosedEmbedding_paperCompletedSpectralPushforward B).tendsto_nhds_iff

end RHTower.WeilWorkPBAP
