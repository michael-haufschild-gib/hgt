import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryPhaseSelection

/-!
# Height-cell domination of translated HCF Plemelj covariance

The compact height-cell boundary trace is a termwise truncation of the full critical-line trace.
Consequently, after subtracting boundary mass from the same translated pole--Gamma lattice, the
infinite Plemelj covariance is no larger than the compact covariance.  Selecting the phase below
its exact height-cell average therefore removes the exterior-cutoff loss completely.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Every compact critical-line HCF trace is bounded by the full trace. -/
theorem criticalLineCriticalFeatureCutoffTrace_le_energyTrace
    (t : ℝ) (cutoff : ℕ) :
    criticalLineCriticalFeatureCutoffTrace t cutoff ≤
      criticalLineCriticalFeatureEnergyTrace t := by
  rw [criticalLineCriticalFeatureCutoffTrace,
    criticalLineCriticalFeatureEnergyTrace]
  exact (criticalLineCriticalFeatureCutoffEnergy_summable t cutoff).tsum_le_tsum
    (fun q => criticalLineCriticalFeatureCutoffEnergy_le t cutoff q)
    (criticalLineCriticalFeatureEnergy_summable t)

/-- The translated source Plemelj covariance is the translated pole--Gamma lattice minus the
full multiplicity-exact critical-line trace. -/
theorem criticalFeatureTranslatedPoleGammaPlemeljCovariance_eq_trace
    (theta : ℝ) (K : Finset ℤ) :
    criticalFeatureTranslatedPoleGammaPlemeljCovariance theta K =
      criticalFeatureTranslatedPoleGammaLatticeBudget theta K -
        ∑ k ∈ K,
          criticalLineCriticalFeatureEnergyTrace ((k : ℝ) + theta) := by
  have hcutoff (cutoff : ℕ) :
      criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff theta K cutoff =
        criticalFeatureTranslatedPoleGammaLatticeBudget theta K -
          ∑ k ∈ K,
            criticalLineCriticalFeatureCutoffTrace ((k : ℝ) + theta) cutoff := by
    rw [criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff]
    apply congrArg
    apply Finset.sum_congr rfl
    intro k hk
    exact (tendsto_criticalFeatureCompactPoleGammaObservable
      ((k : ℝ) + theta) cutoff).limUnder_eq
  have htrace : Tendsto
      (fun cutoff : ℕ =>
        ∑ k ∈ K,
          criticalLineCriticalFeatureCutoffTrace ((k : ℝ) + theta) cutoff)
      atTop
      (nhds (∑ k ∈ K,
        criticalLineCriticalFeatureEnergyTrace ((k : ℝ) + theta))) := by
    apply tendsto_finsetSum K
    intro k hk
    exact tendsto_criticalLineCriticalFeatureCutoffTrace ((k : ℝ) + theta)
  have hcov : Tendsto
      (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff theta K)
      atTop
      (nhds (criticalFeatureTranslatedPoleGammaLatticeBudget theta K -
        ∑ k ∈ K,
          criticalLineCriticalFeatureEnergyTrace ((k : ℝ) + theta))) := by
    apply (tendsto_const_nhds.sub htrace).congr'
    exact Filter.Eventually.of_forall fun cutoff => (hcutoff cutoff).symm
  rw [criticalFeatureTranslatedPoleGammaPlemeljCovariance, hcov.limUnder_eq]

/-- At every height, covariance-minimizing phase makes infinite source covariance no larger than
the exact compact height-cell phase average. -/
theorem criticalFeatureTranslatedPlemeljCovariance_at_sourcePhase_le_phaseAverage
    (n : ℕ) :
    criticalFeatureTranslatedPoleGammaPlemeljCovariance
        (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
        (criticalFeatureCanonicalLatticeWindow n) ≤
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n := by
  let theta := criticalFeatureCompactFiniteLatticeSourceCovariancePhase n
  let K := criticalFeatureCanonicalLatticeWindow n
  have hboundary :
      criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta ≤
        ∑ k ∈ K,
          criticalLineCriticalFeatureEnergyTrace ((k : ℝ) - theta) := by
    have hfinite :
        criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase n theta =
          ∑ k ∈ K,
            criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) n := by
      rw [criticalFeatureCompactFiniteLatticeSourceBoundaryLimitAtPhase]
      exact (tendsto_criticalFeatureTranslatedCompactLatticeBoundaryObservable
        theta K n).limUnder_eq
    rw [hfinite]
    exact Finset.sum_le_sum fun k hk =>
      criticalLineCriticalFeatureCutoffTrace_le_energyTrace ((k : ℝ) - theta) n
  have hpoint :
      criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K ≤
        criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase n theta := by
    rw [criticalFeatureTranslatedPoleGammaPlemeljCovariance_eq_trace,
      criticalFeatureCompactFiniteLatticeSourceCovarianceAtPhase]
    dsimp only [K]
    have hcenters :
        (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          criticalLineCriticalFeatureEnergyTrace ((k : ℝ) + -theta)) =
        ∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          criticalLineCriticalFeatureEnergyTrace ((k : ℝ) - theta) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
    rw [hcenters]
    linarith
  exact hpoint.trans (criticalFeatureCompactFiniteLatticeSourceCovariancePhase_spec n)

end

end RHTower
