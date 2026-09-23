import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryPhaseSelection

/-!
# Boundary-first quantitative HCF alias saving

The compact source boundary alias has exact mean zero.  Its sharp `37/200` periodization ripple
bounds it above by a fixed fraction of the source zero mode.  A minimum-versus-variance inequality
therefore selects a source phase, before positive displacement, with a saving equal to boundary
alias variance divided by that explicit envelope.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- A continuous zero-mean reporter on one cell falls below minus variance over any positive upper
envelope. -/
theorem exists_mem_Icc_le_neg_intervalVariance_div_of_zeroMean
    (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ) (hM : 0 < M)
    (hupper : ∀ θ ∈ Icc (0 : ℝ) 1, f θ ≤ M)
    (hmean : (∫ θ in (0 : ℝ)..1, f θ) = 0) :
    ∃ θ ∈ Icc (0 : ℝ) 1,
      f θ ≤ -(∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ)) / M := by
  obtain ⟨θ₀, hθ₀mem, hmin⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_isMinOn
      (Set.nonempty_Icc.mpr (by norm_num)) hf.continuousOn
  have hfInt : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable _ _
  have hsqInt : IntervalIntegrable (fun θ => (f θ) ^ (2 : ℕ)) volume 0 1 :=
    (hf.pow 2).intervalIntegrable _ _
  have hmajorInt : IntervalIntegrable
      (fun θ => (M + f θ₀) * f θ - f θ₀ * M) volume 0 1 := by
    exact ((continuous_const.mul hf).sub continuous_const).intervalIntegrable _ _
  have hpoint : ∀ θ ∈ Icc (0 : ℝ) 1,
      (f θ) ^ (2 : ℕ) ≤ (M + f θ₀) * f θ - f θ₀ * M := by
    intro θ hθ
    have hlow : f θ₀ ≤ f θ := hmin hθ
    have hhi : f θ ≤ M := hupper θ hθ
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hhi)]
  have hint := intervalIntegral.integral_mono_on (by norm_num)
    hsqInt hmajorInt hpoint
  have hbound :
      (∫ θ in (0 : ℝ)..1, (f θ) ^ (2 : ℕ)) ≤ -f θ₀ * M := by
    have hsplit :
        (∫ θ in (0 : ℝ)..1, (M + f θ₀) * f θ - f θ₀ * M) =
          (∫ θ in (0 : ℝ)..1, (M + f θ₀) * f θ) -
            ∫ θ in (0 : ℝ)..1, f θ₀ * M := by
      simpa only [Pi.sub_apply, Pi.mul_apply] using
        intervalIntegral.integral_sub
          ((continuous_const.mul hf).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
    calc
      (∫ θ in (0 : ℝ)..1, (f θ) ^ (2 : ℕ)) ≤
          ∫ θ in (0 : ℝ)..1, ((M + f θ₀) * f θ - f θ₀ * M) := hint
      _ = -f θ₀ * M := by
        rw [hsplit, intervalIntegral.integral_const_mul, hmean, mul_zero]
        simp [intervalIntegral.integral_const, smul_eq_mul]
  refine ⟨θ₀, hθ₀mem, ?_⟩
  apply (le_div_iff₀ hM).2
  nlinarith

/-- Boundary variance of source alias after the divisor-free limit has been fixed. -/
def criticalFeatureCompactSourceBoundaryAliasRealVariance (cutoff : ℕ) : ℝ :=
  ∫ theta in (0 : ℝ)..1,
    (criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta) ^ (2 : ℕ)

/-- Sharp source envelope inherited from the `37/200` HCF periodization ripple. -/
def criticalFeatureCompactSourceBoundaryAliasUpperEnvelope (cutoff : ℕ) : ℝ :=
  ((37 : ℝ) / 200) / (2 * Real.pi) *
    criticalFeatureCompactZeroModeSourceBoundaryLimit cutoff

/-- Compact source zero mode is nonnegative. -/
theorem criticalFeatureCompactZeroModeSourceBoundaryLimit_nonnegative
    (cutoff : ℕ) :
    0 ≤ criticalFeatureCompactZeroModeSourceBoundaryLimit cutoff := by
  obtain ⟨Gamma, _hGamma, hzero, _hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  rw [hzero]
  apply Finset.sum_nonneg
  intro gamma hgamma
  unfold criticalFeatureZeroModeBoundaryCutoffWeight
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _))

/-- Every boundary alias value is bounded above by the exact source envelope. -/
theorem criticalFeatureCompactSourceBoundaryAliasAtPhase_le_upperEnvelope
    (cutoff : ℕ) (theta : ℝ) :
    criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta ≤
      criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff := by
  obtain ⟨Gamma, _hGamma, hzero, hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  have hformula :
      criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta =
        ∑ gamma ∈ Gamma,
          (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
              (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi) := by
    rw [criticalFeatureCompactSourceBoundaryAliasAtPhase, hfull theta, hzero]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    unfold criticalFeatureFullBoundaryCutoffWeight
      criticalFeatureZeroModeBoundaryCutoffWeight
    ring
  rw [hformula]
  calc
    ∑ gamma ∈ Gamma,
        (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
            (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi) ≤
      ∑ gamma ∈ Gamma,
        (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) * ((37 : ℝ) / 200) := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      apply mul_le_mul_of_nonneg_left
      · exact (le_abs_self _).trans
          (abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le (gamma + theta))
      · exact mul_nonneg (Nat.cast_nonneg _)
          (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _)
    _ = criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff := by
      rw [criticalFeatureCompactSourceBoundaryAliasUpperEnvelope, hzero]
      simp only [criticalFeatureZeroModeBoundaryCutoffWeight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro gamma hgamma
      field_simp [Real.pi_ne_zero]

/-- Boundary alias envelope is nonnegative. -/
theorem criticalFeatureCompactSourceBoundaryAliasUpperEnvelope_nonnegative
    (cutoff : ℕ) :
    0 ≤ criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff := by
  unfold criticalFeatureCompactSourceBoundaryAliasUpperEnvelope
  apply mul_nonneg
  · positivity
  · exact criticalFeatureCompactZeroModeSourceBoundaryLimit_nonnegative cutoff

/-- Boundary-first quantitative phase selection.  Phase is fixed before positive displacement;
the saving is boundary alias variance divided by the explicit `37/200` source envelope. -/
theorem exists_criticalFeatureCompactBoundaryAliasPhase_le_neg_variance_div
    (cutoff : ℕ)
    (henvelope : 0 < criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff) :
    ∃ theta ∈ Icc (0 : ℝ) 1,
      criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta ≤
        -criticalFeatureCompactSourceBoundaryAliasRealVariance cutoff /
          criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff := by
  simpa only [criticalFeatureCompactSourceBoundaryAliasRealVariance] using
    exists_mem_Icc_le_neg_intervalVariance_div_of_zeroMean
      (criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff)
      (continuous_criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff)
      (criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff) henvelope
      (by
        intro theta htheta
        exact criticalFeatureCompactSourceBoundaryAliasAtPhase_le_upperEnvelope cutoff theta)
      (intervalIntegral_criticalFeatureCompactSourceBoundaryAliasAtPhase_eq_zero cutoff)

end

end RHTower
