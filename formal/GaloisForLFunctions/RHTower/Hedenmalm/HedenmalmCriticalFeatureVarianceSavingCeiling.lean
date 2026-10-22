import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureOffLineAliasBalance
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryCapacityAsymptotic
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

/-!
# Sharp HCF variance-saving ceiling

The compact fixed-period alias has pointwise envelope `37/200` times real-zero mass.
Its variance/envelope saving cannot exceed that envelope. The actual Xi census therefore
caps the saving at `37/100` of the total zero count asymptotically, below the `π/3`
gap between the corpus's two-thirds baseline and three-quarter source ceiling.
This is an upper bound on one mechanism, not a lower bound on the physical covariance.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- A zero-mean alias bounded by its envelope cannot save more than that envelope. -/
theorem hcf_boundary_variance_saving_le_envelope (n : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasRealVariance n /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n ≤
      criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n := by
  let f : ℝ → ℝ := criticalFeatureCompactSourceBoundaryAliasAtPhase n
  let M : ℝ := criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n
  have hM : 0 ≤ M := criticalFeatureCompactSourceBoundaryAliasUpperEnvelope_nonnegative n
  have hf : Continuous f := continuous_criticalFeatureCompactSourceBoundaryAliasAtPhase n
  have hsquare : ∀ theta : ℝ, f theta ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    intro theta
    have h := abs_criticalFeatureCompactSourceBoundaryAliasAtPhase_le_upperEnvelope n theta
    change |f theta| ≤ M at h
    rcases abs_le.mp h with ⟨hlo, hhi⟩
    nlinarith
  have hV : criticalFeatureCompactSourceBoundaryAliasRealVariance n ≤ M ^ (2 : ℕ) := by
    unfold criticalFeatureCompactSourceBoundaryAliasRealVariance
    have h : (∫ theta in (0 : ℝ)..1, f theta ^ (2 : ℕ)) ≤
        ∫ theta in (0 : ℝ)..1, M ^ (2 : ℕ) :=
      intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        ((hf.pow 2).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
        (fun theta _ => hsquare theta)
    simpa only [f, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      one_mul] using h
  by_cases hzero : M = 0
  · have hVnonneg : 0 ≤ criticalFeatureCompactSourceBoundaryAliasRealVariance n := by
      unfold criticalFeatureCompactSourceBoundaryAliasRealVariance
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro theta _
      positivity
    have hVzero : criticalFeatureCompactSourceBoundaryAliasRealVariance n = 0 := by
      rw [hzero] at hV
      nlinarith
    simp [M, hzero, hVzero]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    apply (div_le_iff₀ hMpos).2
    simpa only [pow_two] using hV

/-- The physical real-zero census caps the compact alias envelope. -/
theorem hcf_boundary_alias_envelope_le_critical_count (n : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n ≤
      (37 : ℝ) / 100 * (xiPosCriticalZeroCount ((n : ℝ) + 4) : ℝ) := by
  obtain ⟨Gamma, hGamma, hzero, _⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums n
  have hchi : (∑ gamma ∈ Gamma,
      ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
        SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma) ≤
        ∑ gamma ∈ Gamma, ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := by
    apply Finset.sum_le_sum
    intro gamma _
    exact mul_le_of_le_one_right (Nat.cast_nonneg _)
      (SchwartzMap.realCompactIntervalCutoff_le_one _ _)
  have hcount := realZeroMultiplicity_le_two_mul_xiPosCriticalZeroCount
    ((n : ℝ) + 4) Gamma hGamma
  have hM : criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n =
      (37 : ℝ) / 200 *
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma := by
    rw [criticalFeatureCompactSourceBoundaryAliasUpperEnvelope, hzero]
    simp only [criticalFeatureZeroModeBoundaryCutoffWeight]
    have hsum :
        (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            (2 * Real.pi * SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma)) =
          2 * Real.pi *
            ∑ gamma ∈ Gamma,
              ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
                SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro gamma _
      ring
    rw [hsum]
    field_simp [Real.pi_ne_zero]
  rw [hM]
  calc
    (37 : ℝ) / 200 *
        (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma) ≤
      (37 : ℝ) / 200 *
        (∑ gamma ∈ Gamma, ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hchi (by norm_num)
    _ ≤ (37 : ℝ) / 200 *
        (2 * (xiPosCriticalZeroCount ((n : ℝ) + 4) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hcount (by norm_num)
    _ = (37 : ℝ) / 100 * (xiPosCriticalZeroCount ((n : ℝ) + 4) : ℝ) := by
      ring

theorem hcf_boundary_variance_saving_le_total_count (n : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasRealVariance n /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n ≤
      (37 : ℝ) / 100 * (xiPosZeroCount ((n : ℝ) + 4) : ℝ) := by
  have h1 := hcf_boundary_variance_saving_le_envelope n
  have h2 := hcf_boundary_alias_envelope_le_critical_count n
  have h3 : (xiPosCriticalZeroCount ((n : ℝ) + 4) : ℝ) ≤
      (xiPosZeroCount ((n : ℝ) + 4) : ℝ) := by
    exact_mod_cast xiPosCriticalZeroCount_le ((n : ℝ) + 4)
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num)))

/-- Unconditional cofinal ceiling: the HCF variance saving is at most `37/100` of all zeros. -/
theorem hcf_boundary_variance_saving_asymptotic_upper :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeatureCompactSourceBoundaryAliasRealVariance n /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n)
      (37 / 100) := by
  intro eps heps
  have hlimit : Filter.Tendsto
      (fun n : ℕ => (37 / 100 : ℝ) *
        (criticalFeatureCanonicalZeroCount (n + 4) /
          criticalFeatureCanonicalZeroCount n))
      Filter.atTop (nhds (37 / 100 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_criticalFeatureCanonicalZeroCount_nat_add_div 4))
  have hratio : ∀ᶠ n : ℕ in Filter.atTop,
      (37 / 100 : ℝ) *
          (criticalFeatureCanonicalZeroCount (n + 4) /
            criticalFeatureCanonicalZeroCount n) < 37 / 100 + eps :=
    hlimit.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos, hratio] with n hN hr
  have hcount : (xiPosZeroCount ((n : ℝ) + 4) : ℝ) =
      criticalFeatureCanonicalZeroCount (n + 4) := by
    have hcast : (n : ℝ) + 4 = ((n + 4 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    unfold criticalFeatureCanonicalZeroCount
    exact_mod_cast xiPosZeroCount_eq_xiZeroCount
      (T := ((n + 4 : ℕ) : ℝ)) (by positivity)
  have hfinite := hcf_boundary_variance_saving_le_total_count n
  rw [hcount] at hfinite
  have hratio' : (37 / 100 : ℝ) *
      criticalFeatureCanonicalZeroCount (n + 4) <
        (37 / 100 + eps) * criticalFeatureCanonicalZeroCount n := by
    have hdiv : ((37 / 100 : ℝ) * criticalFeatureCanonicalZeroCount (n + 4)) /
        criticalFeatureCanonicalZeroCount n < 37 / 100 + eps := by
      simpa only [mul_div_assoc] using hr
    exact (div_lt_iff₀ hN).mp hdiv
  exact hfinite.trans hratio'.le

/-- The maximal alias-only saving is below the `π/3` baseline-to-target gap. -/
theorem hcf_boundary_variance_ceiling_strictly_below_baseline_gap :
    (37 / 100 : ℝ) < Real.pi / 3 := by
  have hpi := Real.pi_gt_three
  linarith

end
end RHTower
