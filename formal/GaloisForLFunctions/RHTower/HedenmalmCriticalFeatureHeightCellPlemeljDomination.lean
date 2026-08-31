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

/-- Exact legitimate source-majorization inequality.  At the source-selected phase, the corrected
HCF budget is bounded by the zero-independent height-cell phase average plus only the uniformly
lower-order safe-line prime channel. -/
theorem criticalFeatureTranslatedCorrectedBudget_at_sourcePhase_le_phaseAverage_add_prime
    (n : ℕ) :
    criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
        (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
        (criticalFeatureCanonicalLatticeWindow n) ≤
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n +
        ((criticalFeatureCanonicalLatticeWindow n).card : ℝ) *
          (2 * criticalFeatureVonMangoldtUniformConstant) := by
  let theta := -(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n)
  let K := criticalFeatureCanonicalLatticeWindow n
  have hsplit :=
    criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_eq_sourceCovariance_add_vm theta K
  have hcov : criticalFeatureTranslatedPoleGammaPlemeljCovariance theta K ≤
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n := by
    simpa only [theta, K] using
      criticalFeatureTranslatedPlemeljCovariance_at_sourcePhase_le_phaseAverage n
  have hprimeAbs := abs_criticalFeatureTranslatedVonMangoldtLatticeBudget_le theta K
  have hprime : criticalFeatureTranslatedVonMangoldtLatticeBudget theta K ≤
      (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) :=
    (le_abs_self _).trans hprimeAbs
  rw [hsplit]
  dsimp only [theta, K] at hcov hprime ⊢
  linarith

/-- Every asymptotic ceiling for the exact height-cell source average transfers to the corrected
HCF budget at the source-selected moving phase, with no exterior-cutoff hypothesis. -/
theorem canonical_sourcePhaseCorrectedBudget_ceiling_of_phaseAverage
    {c : ℝ}
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage c) :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
        (-(criticalFeatureCompactFiniteLatticeSourceCovariancePhase n))
        (criticalFeatureCanonicalLatticeWindow n)) c := by
  intro eps heps
  have hsource' := hsource (eps / 2) (half_pos heps)
  have hprime : Tendsto
      (fun n =>
        ((criticalFeatureCanonicalLatticeWindow n).card : ℝ) /
            criticalFeatureCanonicalZeroCount n *
          (2 * criticalFeatureVonMangoldtUniformConstant))
      atTop (nhds 0) := by
    simpa using
      tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount.mul_const
        (2 * criticalFeatureVonMangoldtUniformConstant)
  have hprime' : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalLatticeWindow n).card : ℝ) /
            criticalFeatureCanonicalZeroCount n *
          (2 * criticalFeatureVonMangoldtUniformConstant) < eps / 2 :=
    (tendsto_order.1 hprime).2 _ (half_pos heps)
  filter_upwards [hsource', hprime', eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hsourceN hprimeN hN
  have hbudget :=
    criticalFeatureTranslatedCorrectedBudget_at_sourcePhase_le_phaseAverage_add_prime n
  have hprimeMul :
      ((criticalFeatureCanonicalLatticeWindow n).card : ℝ) *
          (2 * criticalFeatureVonMangoldtUniformConstant) <
        (eps / 2) * criticalFeatureCanonicalZeroCount n := by
    have := (div_lt_iff₀ hN).mp hprimeN
    nlinarith
  nlinarith

end

end RHTower
