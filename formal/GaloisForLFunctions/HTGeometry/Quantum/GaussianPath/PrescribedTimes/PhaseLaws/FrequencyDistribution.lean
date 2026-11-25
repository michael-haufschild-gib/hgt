import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleFourierDecay

/-! # The law of a single late phase observation with random frequencies -/

open Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.PhaseLaws
noncomputable section
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

private theorem measurable_snapshot (f : X→I→ℝ) (hf : Measurable f) (t : ℝ) :
    Measurable (fun x => finiteClockPhasePoint (f x) t) :=
  measurable_pi_lambda _ fun i => (AddCircle.continuous_mk' (1:ℝ)).measurable.comp
    (((measurable_pi_apply i).comp hf).const_mul t |>.div_const (2*Real.pi))

/-- Draw the frequencies once and read the entire phase vector at time t. -/
def frequencySnapshot (μ : ProbabilityMeasure X) (f : X→I→ℝ) (hf : Measurable f) (t : ℝ) :
    ProbabilityMeasure (UnitAddTorus I) :=
  μ.map (measurable_snapshot f hf t).aemeasurable

/-- Absolute continuity of each nontrivial scalar action suffices for the
whole vector at one late observation to converge in law to Haar measure. -/
theorem frequencySnapshot_haar_cocompact (μ : ProbabilityMeasure X) (f : X→I→ℝ) (hf : Measurable f)
    (h : ∀ m : I→ℤ, m≠0 →
      (μ : Measure X).map (fun x => -finiteTorusCharacterDetuning m (f x)) ≪ volume) :
    Tendsto (frequencySnapshot μ f hf) (cocompact ℝ) (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hm : m=0
  · subst m
    simp only [if_pos rfl,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,integral_const,probReal_univ,one_smul]
    exact tendsto_const_nhds
  rw [if_neg hm]
  let A (x : X) := -finiteTorusCharacterDetuning m (f x)
  have hA : Measurable A := (Finset.measurable_fun_sum _ fun i _ =>
    (((measurable_pi_apply i).comp hf).const_mul (m i:ℝ))).neg
  let ν := (μ : Measure X).map A
  have hν : ν ≪ volume := h m hm
  have ht := spectralDensityFourierAmplitude_tendsto_zero_cocompact (spectralMeasureDensity ν)
  apply ht.congr
  intro t
  rw [spectralDensityFourierAmplitude_spectralMeasureDensity ν hν,frequencySnapshot,ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_snapshot f hf t).aemeasurable (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable]
  rw [show ν=(μ : Measure X).map A from rfl,integral_map hA.aemeasurable (by fun_prop)]
  exact integral_congr_ae (.of_forall fun x => by
    simp only [A,mFourier_finiteClockPhasePoint,mul_neg,Complex.ofReal_neg,neg_neg])

theorem frequencySnapshot_haar (μ : ProbabilityMeasure X) (f : X→I→ℝ) (hf : Measurable f)
    (h : ∀ m : I→ℤ, m≠0 →
      (μ : Measure X).map (fun x => -finiteTorusCharacterDetuning m (f x)) ≪ volume) :
    Tendsto (frequencySnapshot μ f hf) atTop (𝓝 (finiteTorusHaarProbabilityMeasure I)) :=
  (frequencySnapshot_haar_cocompact μ f hf h).mono_left atTop_le_cocompact

#print axioms frequencySnapshot_haar_cocompact
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.PhaseLaws
