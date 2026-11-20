import GaloisForLFunctions.HTGeometry.Thermofield.InverseTimeSpectralSplit
import GaloisForLFunctions.HTGeometry.CompactMomentWeakConvergence
import GaloisForLFunctions.RHTower.FiniteAtomicObserverTimeGapLaw
import GaloisForLFunctions.RHTower.StationaryRecurrenceCompletionLaw

/-!
# Thermofield return distributions across time scales

Sampling a centered window gives a probability law of the survival fidelity.
The power-law collision hierarchy determines its weak limit on the compact
fidelity interval, including the inverse-time crossover distribution.
-/

open Filter MeasureTheory Set Topology
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry.Thermofield

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

private def gibbsEnergyMeasure (β : ℝ) (E : α → ℝ) : Measure ℝ :=
  RHTower.finiteAtomicObserverSpectrum (finiteGibbsStateWeight β E) E

private instance (β : ℝ) (E : α → ℝ) : IsProbabilityMeasure (gibbsEnergyMeasure β E) :=
  RHTower.finiteAtomicObserverSpectrum_isProbabilityMeasure _ _
    (fun i => (finiteGibbsStateWeight_pos β E i).le) (sum_finiteGibbsStateWeight_eq_one β E)

omit [DecidableEq α] in
private theorem charFun_gibbsEnergyMeasure (β : ℝ) (E : α → ℝ) (t : ℝ) :
    charFun (gibbsEnergyMeasure β E) t =
      finiteSpectralSurvivalAmplitude (finiteGibbsStateWeight β E) E t := by
  rw [gibbsEnergyMeasure, RHTower.charFun_finiteAtomicObserverSpectrum _ _
    (fun i => (finiteGibbsStateWeight_pos β E i).le)]
  simp only [finiteSpectralSurvivalAmplitude, mul_comm t]

/-- Empirical Gibbs survival fidelity under the uniform centered clock. -/
def gibbsWindowReturnDistribution (β : ℝ) (E : α → ℝ) (T : ℝ) :
    ProbabilityMeasure RHTower.SpectralReturnFidelityInterval :=
  RHTower.centeredSpectralReturnProbabilityMeasure (gibbsEnergyMeasure β E) T

omit [DecidableEq α] in
/-- The window distribution has exactly the finite replica return moments. -/
theorem gibbsWindowReturnDistribution_moment (β : ℝ) (E : α → ℝ) (T : Ioi (0 : ℝ)) (n : ℕ) :
    (∫ x : RHTower.SpectralReturnFidelityInterval, (x : ℝ) ^ n
      ∂(gibbsWindowReturnDistribution β E T : Measure RHTower.SpectralReturnFidelityInterval)) =
      (finiteSpectralSurvivalFidelityMean (finiteGibbsStateWeight β E) E n T).re := by
  rw [gibbsWindowReturnDistribution,
    RHTower.integral_pow_centeredSpectralReturnProbabilityMeasure (gibbsEnergyMeasure β E) n T.2]
  have h : RHTower.spectralReturnMomentMean (gibbsEnergyMeasure β E) n T =
      finiteSpectralSurvivalFidelityMean (finiteGibbsStateWeight β E) E n T := by
    simp [RHTower.spectralReturnMomentMean, finiteSpectralSurvivalFidelityMean,
      finiteSpectralSurvivalFidelity, charFun_gibbsEnergyMeasure]
  rw [← h, RHTower.spectralReturnMomentMean_eq_ofReal, Complex.ofReal_re]

/-- The power-law Gibbs windows converge in distribution. Their common
compact carrier makes the entire law uniquely determined by the replica limits. -/
theorem existsUnique_gibbsPowerTimeReturnDistribution (β τ : ℝ) (E F : α → ℝ)
    (γ : Ioi (0 : ℝ)) :
    ∃! law : ProbabilityMeasure RHTower.SpectralReturnFidelityInterval,
      Tendsto (fun T => gibbsWindowReturnDistribution β (powerTimeSpectrum E F τ γ T) T)
        atTop (𝓝 law) ∧
      ∀ n : ℕ, (∫ x : RHTower.SpectralReturnFidelityInterval, (x : ℝ) ^ n
        ∂(law : Measure RHTower.SpectralReturnFidelityInterval)) =
        (powerTimeReplicaLimit β τ E F γ n).re := by
  let μ := fun T : ℝ => gibbsWindowReturnDistribution β (powerTimeSpectrum E F τ γ T) T
  let I := RHTower.SpectralReturnFidelityInterval
  have hmoment (n : ℕ) : Tendsto (fun T => ∫ x : I, (x : ℝ) ^ n ∂(μ T : Measure I))
      atTop (𝓝 (powerTimeReplicaLimit β τ E F γ n).re) := by
    refine (Complex.continuous_re.continuousAt.tendsto.comp
      (thermalReplicaMean_tendsto_powerTimeSpectrum β τ E F γ n)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (gibbsWindowReturnDistribution_moment β (powerTimeSpectrum E F τ γ T) ⟨T, hT⟩ n).symm
  have hfrequent : ∃ᶠ T : ℝ in atTop, μ T ∈ (Set.univ : Set (ProbabilityMeasure I)) :=
    (Eventually.of_forall fun _ => Set.mem_univ _).frequently
  obtain ⟨law, _, hcluster⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure I))).exists_mapClusterPt_of_frequently
      hfrequent
  have hvalue (n : ℕ) : (∫ x : I, (x : ℝ) ^ n ∂(law : Measure I)) =
      (powerTimeReplicaLimit β τ E F γ n).re := by
    have hc : Continuous (fun ν : ProbabilityMeasure I => ∫ x : I, (x : ℝ) ^ n ∂(ν : Measure I)) :=
      continuous_integral_real_continuousMap (RHTower.spectralReturnMomentContinuousMap n)
    have hcl : MapClusterPt (∫ x : I, (x : ℝ) ^ n ∂(law : Measure I)) atTop
        (fun T : ℝ => ∫ x : I, (x : ℝ) ^ n ∂(μ T : Measure I)) :=
      hcluster.continuousAt_comp hc.continuousAt
    exact eq_of_mapClusterPt_of_tendsto hcl (hmoment n)
  have htend : Tendsto μ atTop (𝓝 law) := by
    apply probabilityMeasure_tendsto_of_integral_pow_tendsto
    intro n
    rw [hvalue n]
    exact hmoment n
  exact ⟨law, ⟨htend, hvalue⟩, fun _ h => tendsto_nhds_unique h.1 htend⟩

#print axioms gibbsWindowReturnDistribution_moment
#print axioms existsUnique_gibbsPowerTimeReturnDistribution

end

end GaloisForLFunctions.HTGeometry.Thermofield
