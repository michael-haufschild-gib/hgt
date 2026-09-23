import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryAliasPositiveSaving
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryCapacity

/-!
# HCF critical/off-line alias balance

The source-selected HCF boundary alias is exactly the critical-line slice of a compactly
weighted complete Xi-ordinate alias. The omitted off-line slice has magnitude at most the
sharp periodization ripple `37/200` times its weighted divisor mass. Thus any variance
saving must be carried by either complete-ordinate discrepancy or off-line mass.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- All Xi-divisor supports that can contribute to the compact HCF cutoff. -/
noncomputable def hcfXiSupportPacket (n : ℕ) : Finset XiDivisorSupport :=
  (xiSupportsUpTo_finite ((n : ℝ) + 3)).toFinset

noncomputable def hcfXiAliasTerm (n : ℕ) (theta : ℝ) (rho : XiDivisorSupport) : ℝ :=
  (xiSupportMultiplicity rho : ℝ) *
    SchwartzMap.realCompactIntervalCutoff (n : ℝ) (rho : ℂ).im *
      (criticalFeatureRealBoundaryPeriodization ((rho : ℂ).im + theta) - 2 * Real.pi)

/-- Complete Xi-ordinate alias, including critical and off-critical supports. -/
noncomputable def hcfXiAllAlias (n : ℕ) (theta : ℝ) : ℝ :=
  ∑ rho ∈ hcfXiSupportPacket n, hcfXiAliasTerm n theta rho

noncomputable def hcfXiLineAlias (n : ℕ) (theta : ℝ) : ℝ :=
  ∑ rho ∈ (hcfXiSupportPacket n).filter (fun rho : XiDivisorSupport => (rho : ℂ).re = 1 / 2),
    hcfXiAliasTerm n theta rho

noncomputable def hcfXiOffAlias (n : ℕ) (theta : ℝ) : ℝ :=
  ∑ rho ∈ (hcfXiSupportPacket n).filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2),
    hcfXiAliasTerm n theta rho

/-- Compactly weighted mass of the off-critical Xi-divisor. -/
noncomputable def hcfXiOffMass (n : ℕ) : ℝ :=
  ∑ rho ∈ (hcfXiSupportPacket n).filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2),
    (xiSupportMultiplicity rho : ℝ) *
      SchwartzMap.realCompactIntervalCutoff (n : ℝ) (rho : ℂ).im

theorem hcfXiAllAlias_eq_line_add_off (n : ℕ) (theta : ℝ) :
    hcfXiAllAlias n theta = hcfXiLineAlias n theta + hcfXiOffAlias n theta := by
  classical
  simp only [hcfXiAllAlias, hcfXiLineAlias, hcfXiOffAlias]
  exact (Finset.sum_filter_add_sum_filter_not
    (hcfXiSupportPacket n) (fun rho : XiDivisorSupport => (rho : ℂ).re = 1 / 2)
    (hcfXiAliasTerm n theta)).symm

theorem hcfXiOffAlias_abs_le (n : ℕ) (theta : ℝ) :
    |hcfXiOffAlias n theta| ≤ (37 : ℝ) / 200 * hcfXiOffMass n := by
  classical
  let S := (hcfXiSupportPacket n).filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2)
  have hpoint (rho : XiDivisorSupport) :
      |hcfXiAliasTerm n theta rho| ≤
        (37 : ℝ) / 200 * ((xiSupportMultiplicity rho : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (n : ℝ) (rho : ℂ).im) := by
    unfold hcfXiAliasTerm
    have hw : 0 ≤ (xiSupportMultiplicity rho : ℝ) *
        SchwartzMap.realCompactIntervalCutoff (n : ℝ) (rho : ℂ).im :=
      mul_nonneg (Nat.cast_nonneg _) (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _)
    rw [← mul_assoc, abs_mul, abs_of_nonneg hw]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left
        (abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le
          ((rho : ℂ).im + theta)) hw)
  calc
    |hcfXiOffAlias n theta| ≤ ∑ rho ∈ S, |hcfXiAliasTerm n theta rho| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ rho ∈ S, (37 : ℝ) / 200 *
        ((xiSupportMultiplicity rho : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (n : ℝ) (rho : ℂ).im) := by
      apply Finset.sum_le_sum
      intro rho _
      exact hpoint rho
    _ = (37 : ℝ) / 200 * hcfXiOffMass n := by
      rw [hcfXiOffMass, ← Finset.mul_sum]

theorem hcfXiLineAlias_abs_le_all_add_off (n : ℕ) (theta : ℝ) :
    |hcfXiLineAlias n theta| ≤
      |hcfXiAllAlias n theta| + (37 : ℝ) / 200 * hcfXiOffMass n := by
  have h := hcfXiAllAlias_eq_line_add_off n theta
  have htri := abs_sub (hcfXiAllAlias n theta) (hcfXiOffAlias n theta)
  rw [sub_eq_iff_eq_add.mpr h] at htri
  exact htri.trans (by
    simpa only [add_comm] using
      (add_le_add_left (hcfXiOffAlias_abs_le n theta)
        |hcfXiAllAlias n theta|))

theorem hcfXiLineAlias_eq_sourceAlias (n : ℕ) (theta : ℝ) :
    hcfXiLineAlias n theta =
      criticalFeatureCompactSourceBoundaryAliasAtPhase n theta := by
  classical
  obtain ⟨Gamma, hGamma, hzero, hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums n
  let g : ℝ → ℝ := fun gamma =>
    (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
      SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma) *
        (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi)
  have hformula : criticalFeatureCompactSourceBoundaryAliasAtPhase n theta =
      ∑ gamma ∈ Gamma, g gamma := by
    rw [criticalFeatureCompactSourceBoundaryAliasAtPhase, hfull theta, hzero]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro gamma _
    unfold g criticalFeatureFullBoundaryCutoffWeight
      criticalFeatureZeroModeBoundaryCutoffWeight
    ring
  have hvanish (gamma : ℝ) (hbig : (n : ℝ) + 3 < |gamma|) : g gamma = 0 := by
    have hnot : gamma ∉ tsupport (SchwartzMap.realCompactIntervalCutoff (n : ℝ)) := by
      rw [SchwartzMap.realCompactIntervalCutoff_tsupport]
      simp only [Set.mem_setOf_eq]
      intro hbound
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      rw [abs_of_nonneg hn] at hbound
      linarith
    have hchi := image_eq_zero_of_notMem_tsupport hnot
    simp [g, hchi]
  have hfilter : (∑ gamma ∈ Gamma, g gamma) =
      ∑ gamma ∈ Gamma.filter (fun gamma => |gamma| ≤ (n : ℝ) + 3), g gamma := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Gamma
      (fun gamma : ℝ => |gamma| ≤ (n : ℝ) + 3) g
    have hrest : (∑ gamma ∈ Gamma.filter
        (fun gamma => ¬ |gamma| ≤ (n : ℝ) + 3), g gamma) = 0 := by
      apply Finset.sum_eq_zero
      intro gamma hgamma
      exact hvanish gamma (lt_of_not_ge (Finset.mem_filter.mp hgamma).2)
    rw [hrest, add_zero] at hsplit
    exact hsplit.symm
  let S := (hcfXiSupportPacket n).filter
    (fun rho : XiDivisorSupport => (rho : ℂ).re = 1 / 2)
  have hbij : (∑ rho ∈ S, hcfXiAliasTerm n theta rho) =
      ∑ gamma ∈ Gamma.filter (fun gamma => |gamma| ≤ (n : ℝ) + 3), g gamma := by
    refine Finset.sum_bij (fun rho _ => (rho : ℂ).im) ?_ ?_ ?_ ?_
    · intro rho hrho
      have hparts := Finset.mem_filter.mp hrho
      have hbound : |(rho : ℂ).im| ≤ (n : ℝ) + 3 := by
        simpa only [hcfXiSupportPacket, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq] using hparts.1
      have hroot : XiC ((rho : ℂ).im : ℂ) = 0 := by
        rw [XiC_ofReal_im_eq_xi_of_re_eq_half hparts.2]
        exact xi_eq_zero_of_mem_divisor_support rho
      apply Finset.mem_filter.mpr
      constructor
      · apply (hGamma _).mpr
        constructor
        · rw [Metric.mem_ball]
          have hstrict : |(rho : ℂ).im| < (n : ℝ) + 4 := by linarith
          simpa only [Complex.dist_eq, sub_zero, norm_real,
            Real.norm_eq_abs] using hstrict
        · exact hroot
      · exact hbound
    · intro rho hrho sigma hsigma hsame
      apply Subtype.ext
      apply Complex.ext
      · exact (Finset.mem_filter.mp hrho).2.trans
          (Finset.mem_filter.mp hsigma).2.symm
      · exact hsame
    · intro gamma hgamma
      have hg := Finset.mem_filter.mp hgamma
      have hroot : XiC (gamma : ℂ) = 0 := ((hGamma gamma).mp hg.1).2
      let z : ℂ := (1 / 2 : ℂ) + (gamma : ℂ) * I
      have hz : xi z = 0 := by simpa only [XiC, z] using hroot
      let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
      have hre : (rho : ℂ).re = 1 / 2 := by simp [rho, z]
      have him : (rho : ℂ).im = gamma := by simp [rho, z]
      refine ⟨rho, ?_, him⟩
      apply Finset.mem_filter.mpr
      constructor
      · rw [hcfXiSupportPacket, Set.Finite.mem_toFinset]
        simpa only [Set.mem_setOf_eq, him] using hg.2
      · exact hre
    · intro rho hrho
      have hre : (rho : ℂ).re = 1 / 2 := (Finset.mem_filter.mp hrho).2
      unfold hcfXiAliasTerm g
      rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat,
        ← analyticOrderAt_XiC_ofReal_im_eq_xi_of_re_eq_half hre]
  rw [hformula, hfilter]
  exact hbij

theorem hcfSourceAlias_abs_le_all_add_off (n : ℕ) (theta : ℝ) :
    |criticalFeatureCompactSourceBoundaryAliasAtPhase n theta| ≤
      |hcfXiAllAlias n theta| + (37 : ℝ) / 200 * hcfXiOffMass n := by
  rw [← hcfXiLineAlias_eq_sourceAlias]
  exact hcfXiLineAlias_abs_le_all_add_off n theta

/-- The actual HCF saving cannot exceed complete-ordinate discrepancy plus off-line mass. -/
theorem hcfVarianceSaving_le_allAlias_add_off (n : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasRealVariance n /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n ≤
      |hcfXiAllAlias n (criticalFeatureCompactBoundaryVarianceSavingPhase n)| +
        (37 : ℝ) / 200 * hcfXiOffMass n := by
  have hphase := criticalFeatureCompactBoundaryVarianceSavingPhase_spec n
  exact hphase.trans
    ((le_abs_self _).trans
      (hcfSourceAlias_abs_le_all_add_off n
        (criticalFeatureCompactBoundaryVarianceSavingPhase n)))

end

end RHTower
