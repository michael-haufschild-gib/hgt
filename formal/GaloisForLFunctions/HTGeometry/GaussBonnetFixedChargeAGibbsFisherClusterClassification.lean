import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunablePositiveSource

/-! # Exact Fisher cluster interval at the zero-input boundary of actual Gibbs states -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- Actual collision observations entering the Fisher map at a fixed grid and observation offset. -/
def egbFixedChargeAGibbsFisherObservation (n m : ℕ) (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ × ℝ × ℝ :=
  (egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 E,
    egbFixedChargeAGibbsCollisionExcess n (m + 2) 1 E,
    egbFixedChargeAGibbsCollisionExcess n (m + 3) 1 E)

/-- Finite Fisher cluster values approached through genuine Gibbs energies with all three inputs vanishing. -/
def egbFixedChargeAGibbsFisherZeroClusterSet (n m : ℕ) : Set ℝ :=
  {v | ∃ E : ℕ → Fin (2 ^ (n + 3)) → ℝ,
    Tendsto (fun k => egbFixedChargeAGibbsFisherObservation n m (E k)) atTop (nhds (0, 0, 0)) ∧
    Tendsto (fun k => egbFixedChargeAGibbsCollisionFisherValue n m 1 (E k)) atTop (nhds v)}

/-- Every tunable Fisher value is a boundary cluster value along an actual full-support Gibbs sequence. -/
theorem egbFixedChargeAGibbsTunable_fisher_mem_zero_cluster (n m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsTunableFisherCurve t ∈ egbFixedChargeAGibbsFisherZeroClusterSet n m := by
  exact ⟨fun k => egbFixedChargeAGibbsTunableEnergy n k m t,
    egbFixedChargeAGibbsTunable_fisher_inputs_tendsto_zero n m t,
    egbFixedChargeAGibbsTunable_fisher_tendsto_curve n m t⟩

/-- No other finite cluster values can arise through actual Gibbs states. -/
theorem egbFixedChargeAGibbs_fisher_zero_cluster_bounds (n m : ℕ) :
    egbFixedChargeAGibbsFisherZeroClusterSet n m ⊆ Set.Icc 0 (25 / 144 : ℝ) := by
  rintro v ⟨E, _, hv⟩
  exact ⟨ge_of_tendsto hv (Eventually.of_forall fun k =>
    egbFixedChargeAGibbsCollisionFisherValue_nonneg n m 1 (E k)),
    le_of_tendsto hv (Eventually.of_forall fun k =>
      egbFixedChargeAGibbsCollisionFisherValue_upper_bound n m 1 (E k))⟩

/-- The full closed Fisher interval occurs at the zero-input boundary on every fixed grid and observation offset. -/
theorem egbFixedChargeAGibbs_fisher_zero_cluster_classification (n m : ℕ) :
    egbFixedChargeAGibbsFisherZeroClusterSet n m = Set.Icc 0 (25 / 144 : ℝ) := by
  apply Set.Subset.antisymm (egbFixedChargeAGibbs_fisher_zero_cluster_bounds n m)
  intro v hv
  rw [← egbFixedChargeAGibbsTunableFisherCurve_range] at hv
  obtain ⟨t, rfl⟩ := hv
  exact egbFixedChargeAGibbsTunable_fisher_mem_zero_cluster n m t

/-- No continuous value at the origin can extend the Fisher readout on all genuine Gibbs observations. -/
theorem egbFixedChargeAGibbs_fisher_no_continuous_extension (n m : ℕ) (h : ℝ × ℝ × ℝ → ℝ) :
    ¬ (ContinuousAt h (0, 0, 0) ∧
      ∀ E : Fin (2 ^ (n + 3)) → ℝ,
        h (egbFixedChargeAGibbsFisherObservation n m E) = egbFixedChargeAGibbsCollisionFisherValue n m 1 E) := by
  rintro ⟨hc, he⟩
  have hall (t : ℝ) : h (0, 0, 0) = egbFixedChargeAGibbsTunableFisherCurve t := by
    have ho : Tendsto (fun k => egbFixedChargeAGibbsFisherObservation n m
        (egbFixedChargeAGibbsTunableEnergy n k m t)) atTop (nhds (0, 0, 0)) :=
      egbFixedChargeAGibbsTunable_fisher_inputs_tendsto_zero n m t
    have hh := hc.tendsto.comp ho
    change Tendsto (fun k => h (egbFixedChargeAGibbsFisherObservation n m
      (egbFixedChargeAGibbsTunableEnergy n k m t))) atTop (nhds (h (0, 0, 0))) at hh
    simp only [he] at hh
    exact tendsto_nhds_unique hh (egbFixedChargeAGibbsTunable_fisher_tendsto_curve n m t)
  have h0 := hall 0
  have h1 := hall 1
  rw [(egbFixedChargeAGibbsTunableFisherCurve_endpoints).1] at h0
  rw [(egbFixedChargeAGibbsTunableFisherCurve_endpoints).2] at h1
  norm_num [h0] at h1

end
end GaloisForLFunctions.HTGeometry
