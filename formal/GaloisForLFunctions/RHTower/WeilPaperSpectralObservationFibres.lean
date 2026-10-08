import GaloisForLFunctions.RHTower.WeilPaperPacketNormalizedSeparation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Spectral freedom at fixed energy and finitely many correlations

Energy and any finite list of complex autocorrelation samples form a finite
real linear observation vector. The prime-mask null-space construction gives
distinct normalized spectral probabilities agreeing in all these observations.
A primitive rational sample with labels at most `2*k+4` separates the pair.
-/

noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Full energy together with a prescribed finite list of complex correlation samples. -/
def paperEnergySampleObserver {k : ℕ} (y : Fin k → ℝ) :
    (WeilTestFn →₀ ℝ) →ₗ[ℝ] (ℝ × (Fin k → ℂ)) :=
  energy.prod (LinearMap.pi fun i => Finsupp.linearCombination ℝ
    (fun f : WeilTestFn => Zeta23.EF.weilTest f.1 f.1 (y i)))

@[simp] theorem paperEnergySampleObserver_apply {k : ℕ} (y : Fin k → ℝ)
    (c : WeilTestFn →₀ ℝ) :
    paperEnergySampleObserver y c = (energy c, fun i => mixtureSample c (y i)) := rfl

/-- At any finite list of sample locations, two normalized integer-null mixtures agree there
and in full energy, yet a bounded-label primitive rational sample separates them. -/
theorem exists_normalized_null_same_energy_samples_pair {k : ℕ} (y : Fin k → ℝ) :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧
      energy a.1 = energy b.1 ∧ (∀ i, mixtureSample a.1 (y i) = mixtureSample b.1 (y i)) ∧
      ∃ r : PaperPacketPrimitiveEdge (2 * k + 4),
        mixtureSample a.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  let E := ℝ × (Fin k → ℂ)
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨a, b, ha, hb, hT, r, hr⟩ := exists_normalized_null_pair_same_finite_observations
    (Module.finrank ℝ E) (e.toLinearMap.comp (paperEnergySampleObserver y))
  have hobs : paperEnergySampleObserver y a.1 = paperEnergySampleObserver y b.1 :=
    e.injective hT
  have hdim : Module.finrank ℝ E + 3 = 2 * k + 4 := by
    dsimp [E]
    rw [Module.finrank_prod, Module.finrank_self, finrank_real_of_complex, Module.finrank_fin_fun]
    omega
  refine ⟨a, b, ha, hb, congrArg Prod.fst hobs,
    fun i => congrFun (congrArg Prod.snd hobs) i, ?_⟩
  rw [← hdim]
  exact ⟨r, hr⟩

/-- Distinct actual prime-torus spectral probabilities can agree in full energy and every
sample in any prescribed finite complex list. -/
theorem exists_distinct_spectralTorusProbabilities_same_energy_samples {k : ℕ} (y : Fin k → ℝ) :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧
      energy a.1 = energy b.1 ∧ (∀ i, mixtureSample a.1 (y i) = mixtureSample b.1 (y i)) ∧
      spectralTorusProbability a ≠ spectralTorusProbability b := by
  let E := ℝ × (Fin k → ℂ)
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨a, b, ha, hb, hT, hp⟩ :=
    exists_distinct_spectralTorusProbabilities_same_finite_observations (Module.finrank ℝ E)
      (e.toLinearMap.comp (paperEnergySampleObserver y))
  have hobs : paperEnergySampleObserver y a.1 = paperEnergySampleObserver y b.1 :=
    e.injective hT
  exact ⟨a, b, ha, hb, congrArg Prod.fst hobs,
    fun i => congrFun (congrArg Prod.snd hobs) i, hp⟩

/-- The corresponding spectral probabilities on the real line are distinct as well. -/
theorem exists_distinct_spectralProbabilities_same_energy_samples {k : ℕ} (y : Fin k → ℝ) :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧
      energy a.1 = energy b.1 ∧ (∀ i, mixtureSample a.1 (y i) = mixtureSample b.1 (y i)) ∧
      spectralProbability a ≠ spectralProbability b := by
  obtain ⟨a, b, ha, hb, he, hs, hp⟩ :=
    exists_distinct_spectralTorusProbabilities_same_energy_samples y
  refine ⟨a, b, ha, hb, he, hs, ?_⟩
  intro hab
  apply hp
  unfold spectralTorusProbability
  exact congrArg (fun μ : MeasureTheory.ProbabilityMeasure ℝ =>
    μ.map continuous_primeSpectralPoint.measurable.aemeasurable) hab

end RHTower.WeilWorkPBAP
