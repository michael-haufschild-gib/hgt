import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureGroundEnergy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewSmoothTestCriterion

/-!
# First-contact boundary roughness of the restricted Weil ground state

Suzuki's continuity theorem and small-aperture positivity imply the known qualitative fact that
failure of RH produces some degenerate aperture.  This module sharpens that statement at the
*least* contact aperture.

If RH fails, the ground-energy path has a first zero.  A genuine nonzero null ground vector exists
in the completed CCM form domain there, but every nonzero literal smooth source compactly
contained in the aperture has strictly positive energy: compact containment lets that source
descend unchanged to an earlier, positive aperture.  Hence the first null ground vector cannot be
represented by the strict smooth interior core.  The closed capstone is an RH-or-boundary-roughness
alternative; it does not prove RH and uses no computation.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) :
    ∃ a : SuzukiPositiveAperture,
      ccmRestrictedWeilGroundEnergy a < 0 := by
  have hnotSource : ¬ SuzukiSmoothTestFormNonnegative :=
    fun hsource => hnot
      (riemannHypothesis_of_suzukiSmoothTestFormNonnegative hsource)
  rw [SuzukiSmoothTestFormNonnegative] at hnotSource
  push Not at hnotSource
  obtain ⟨a, ha, phi, hphiNeg⟩ := hnotSource
  let A : SuzukiPositiveAperture := ⟨a + 1, by linarith⟩
  let phiA : SuzukiSmoothZeroMeanTest A.1 := {
    toFun := phi
    smooth := phi.smooth
    support_subset := by
      intro x hx
      have hx' := phi.support_subset hx
      rw [mem_Icc] at hx' ⊢
      dsimp only [A]
      constructor <;> linarith
    integral_zero := phi.integral_zero }
  have hphiTsupport : tsupport (phiA : ℝ → ℂ) ⊆ Ioo (-A.1) A.1 := by
    have hclosed : tsupport (phiA : ℝ → ℂ) ⊆ Icc (-a) a := by
      apply closure_minimal
      · exact phi.support_subset
      · exact isClosed_Icc
    intro x hx
    have hx' := hclosed hx
    rw [mem_Icc] at hx'
    rw [mem_Ioo]
    dsimp only [A]
    constructor <;> linarith
  let f0 : SuzukiApertureIntervalL2 A.1 :=
    suzukiApertureRestrictL2 A.1
      (suzukiComplexTestL2 phiA phiA.smooth phiA.hasCompactSupport)
  have hf0Mean : suzukiApertureIntervalMean A f0 = 0 := by
    change suzukiApertureIntervalMean A
        (suzukiApertureRestrictL2 A.1
          (suzukiComplexTestL2 phiA phiA.smooth phiA.hasCompactSupport)) = 0
    rw [suzukiApertureIntervalMean_restrict_interiorSmooth
      A phiA phiA.smooth phiA.hasCompactSupport hphiTsupport]
    exact phiA.integral_zero
  let f : SuzukiApertureZeroMean A :=
    ⟨f0, (mem_suzukiApertureZeroMean_iff A f0).2 hf0Mean⟩
  have hwhole : suzukiApertureZeroExtendL2
        (f : SuzukiApertureIntervalL2 A.1) = phiA.toSoninL2 := by
    change suzukiApertureZeroExtendL2 f0 = phiA.toSoninL2
    rw [show f0 = suzukiApertureRestrictL2 A.1
        (suzukiComplexTestL2 phiA phiA.smooth phiA.hasCompactSupport) from rfl,
      suzukiApertureZeroExtendL2_restrict_interiorSmooth
        A phiA phiA.smooth phiA.hasCompactSupport hphiTsupport]
    apply Lp.ext
    exact (suzukiComplexTestL2_coeFn phiA phiA.smooth phiA.hasCompactSupport).trans
      phiA.coeFn_toSoninL2.symm
  let q : CCMArchimedeanFormDomain A :=
    suzukiAperturePrimitiveCCMFormVector A
      (f : SuzukiApertureIntervalL2 A.1)
  have hform : ccmRestrictedWeilSourceQuadratic A q =
      (suzukiScrewSmoothForm phiA phiA).re := by
    rw [← suzukiWeilIntervalForm_self_re_eq_source]
    rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm]
    rw [show q = suzukiAperturePrimitiveCCMFormVector A
        (f : SuzukiApertureIntervalL2 A.1) from rfl]
    rw [ccmRestrictedWeilForm_primitive_eq_screw]
    rw [suzukiScrewZeroMeanOperator,
      inner_suzukiCenteredScrewZeroMeanOperator_eq_intervalForm]
    rw [← suzukiScrewL2Form_zeroExtend_eq_intervalForm_pair]
    rw [hwhole]
    exact congrArg Complex.re (suzukiScrewSmoothForm_eq_l2 phiA phiA).symm
  have hsourceNeg : ccmRestrictedWeilSourceQuadratic A q < 0 := by
    rw [hform]
    exact hphiNeg
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source A q
  refine ⟨A, ?_⟩
  by_contra hground
  have hgroundNonneg : 0 ≤ ccmRestrictedWeilGroundEnergy A := le_of_not_gt hground
  have hmassNonneg : 0 ≤ ‖ccmArchimedeanFormToAperture A q‖ ^ 2 := sq_nonneg _
  have hproductNonneg : 0 ≤ ccmRestrictedWeilGroundEnergy A *
      ‖ccmArchimedeanFormToAperture A q‖ ^ 2 :=
    mul_nonneg hgroundNonneg hmassNonneg
  linarith

/-- Compact containment makes every nonzero smooth interior source strictly positive whenever
all strictly smaller apertures have positive ground energy. -/
theorem ccmSmoothInteriorSource_source_pos_of_smaller_groundEnergy_pos
    (a : SuzukiPositiveAperture)
    (hbefore : ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
      0 < ccmRestrictedWeilGroundEnergy b)
    (u : CCMComplexSmoothInteriorSource a)
    (hu : ccmArchimedeanFormToAperture a u.toCCMFormVector ≠ 0) :
    0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  obtain ⟨b, hba, hsupport⟩ :=
    exists_strict_smaller_aperture_of_compact_tsupport a u
  let ub := u.restrictAperture b hsupport
  have hval : ub.toCCMFormVector.1 = u.toCCMFormVector.1 :=
    u.restrictAperture_toCCMFormVector_val b hsupport
  have hnorm : ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture b ub.toCCMFormVector‖ :=
    norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval.symm
  have hub : ccmArchimedeanFormToAperture b ub.toCCMFormVector ≠ 0 := by
    intro hzero
    apply hu
    rw [← norm_eq_zero, hnorm, hzero, norm_zero]
  have hmass : 0 < ‖ccmArchimedeanFormToAperture b ub.toCCMFormVector‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hub) 2
  have hproduct : 0 < ccmRestrictedWeilGroundEnergy b *
      ‖ccmArchimedeanFormToAperture b ub.toCCMFormVector‖ ^ 2 :=
    mul_pos (hbefore b hba) hmass
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source
    b ub.toCCMFormVector
  have hsource : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic b ub.toCCMFormVector :=
    ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hba.le hval.symm
  rw [hsource]
  exact hproduct.trans_le hfloor

/-- A first contact is boundary-rough when the completed form has a genuine null ground vector,
every smaller aperture is positive, and no strict smooth interior source represents that vector. -/
def CCMFirstContactBoundaryRoughness : Prop :=
  ∃ (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a),
    ccmRestrictedWeilGroundEnergy a = 0 ∧
      (∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        0 < ccmRestrictedWeilGroundEnergy b) ∧
      ccmArchimedeanFormToAperture a q ≠ 0 ∧
      ccmRestrictedWeilSourceQuadratic a q = 0 ∧
      ∀ u : CCMComplexSmoothInteriorSource a, u.toCCMFormVector ≠ q

/-- Closed Route-U alternative: if RH fails, the continuous ground-energy path reaches zero for
the first time through the completion boundary, never through a smooth interior source. -/
theorem riemannHypothesis_or_ccmFirstContactBoundaryRoughness :
    RiemannHypothesis ∨ CCMFirstContactBoundaryRoughness := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    obtain ⟨delta, hdelta, hsmall⟩ :=
      exists_suzukiSmallAperture_ccmGroundEnergy_pos
    let p : SuzukiPositiveAperture := ⟨delta / 2, by linarith⟩
    have hpdelta : p.1 < delta := by
      dsimp only [p]
      linarith
    have hpEnergy : 0 < ccmRestrictedWeilGroundEnergy p := hsmall p hpdelta
    obtain ⟨B, hBEnergy⟩ :=
      exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hRH
    have hpB : p.1 < B.1 := by
      by_contra hnot
      have hBp : B ≤ p := le_of_not_gt hnot
      have hmono : ccmRestrictedWeilGroundEnergy p ≤
          ccmRestrictedWeilGroundEnergy B :=
        antitone_ccmRestrictedWeilGroundEnergy hBp
      linarith
    let apertureAt : ℝ → SuzukiPositiveAperture := fun x =>
      ⟨max p.1 x, p.2.trans_le (le_max_left _ _)⟩
    let energy : ℝ → ℝ := fun x =>
      ccmRestrictedWeilGroundEnergy (apertureAt x)
    have hapertureContinuous : Continuous apertureAt := by
      exact (continuous_const.max continuous_id).subtype_mk _
    have henergyContinuous : Continuous energy :=
      continuous_ccmRestrictedWeilGroundEnergy.comp hapertureContinuous
    have henergy_eq (x : ℝ) (hx : p.1 ≤ x) :
        energy x = ccmRestrictedWeilGroundEnergy ⟨x, p.2.trans_le hx⟩ := by
      simp only [energy, apertureAt, max_eq_right hx]
    let S : Set ℝ := Icc p.1 B.1 ∩ energy ⁻¹' Iic 0
    have hSClosed : IsClosed S :=
      isClosed_Icc.inter (isClosed_Iic.preimage henergyContinuous)
    have hBmem : B.1 ∈ S := by
      refine ⟨right_mem_Icc.mpr hpB.le, ?_⟩
      change energy B.1 ≤ 0
      rw [henergy_eq B.1 hpB.le]
      exact hBEnergy.le
    have hSNonempty : S.Nonempty := ⟨B.1, hBmem⟩
    have hSBdd : BddBelow S := by
      refine ⟨p.1, ?_⟩
      intro x hx
      exact hx.1.1
    let c : ℝ := sInf S
    have hcS : c ∈ S := hSClosed.csInf_mem hSNonempty hSBdd
    have hpc : p.1 ≤ c := hcS.1.1
    have hcB : c ≤ B.1 := hcS.1.2
    have hcEnergyNonpos : energy c ≤ 0 := hcS.2
    have hpEnergyReal : 0 < energy p.1 := by
      rw [henergy_eq p.1 le_rfl]
      exact hpEnergy
    have hpcStrict : p.1 < c := by
      apply hpc.lt_of_ne
      intro hEq
      rw [hEq] at hpEnergyReal
      linarith
    have hcEnergy : energy c = 0 := by
      apply le_antisymm hcEnergyNonpos
      by_contra hnotNonneg
      have hcNeg : energy c < 0 := lt_of_not_ge hnotNonneg
      have hzeroMem : (0 : ℝ) ∈ Icc (energy c) (energy p.1) :=
        ⟨hcNeg.le, hpEnergyReal.le⟩
      obtain ⟨e, heIcc, heZero⟩ :=
        intermediate_value_Icc' hpc henergyContinuous.continuousOn hzeroMem
      have heStrict : e < c := by
        apply heIcc.2.lt_of_ne
        intro hec
        subst e
        linarith
      have heS : e ∈ S := by
        refine ⟨⟨heIcc.1, heIcc.2.trans hcB⟩, ?_⟩
        change energy e ≤ 0
        rw [heZero]
      have hcle : c ≤ e := csInf_le hSBdd heS
      exact (not_lt_of_ge hcle) heStrict
    let C : SuzukiPositiveAperture := ⟨c, p.2.trans hpcStrict⟩
    have hCEnergy : ccmRestrictedWeilGroundEnergy C = 0 := by
      rw [← hcEnergy]
      exact (henergy_eq c hpc).symm
    have hbefore : ∀ b : SuzukiPositiveAperture, b.1 < C.1 →
        0 < ccmRestrictedWeilGroundEnergy b := by
      intro b hbC
      by_cases hbp : b.1 < p.1
      · have hmono : ccmRestrictedWeilGroundEnergy p ≤
            ccmRestrictedWeilGroundEnergy b :=
          antitone_ccmRestrictedWeilGroundEnergy hbp.le
        exact hpEnergy.trans_le hmono
      · have hpb : p.1 ≤ b.1 := le_of_not_gt hbp
        by_contra hbNotPos
        have hbNonpos : ccmRestrictedWeilGroundEnergy b ≤ 0 := le_of_not_gt hbNotPos
        have hbEnergy : energy b.1 = ccmRestrictedWeilGroundEnergy b := by
          simpa only using henergy_eq b.1 hpb
        have hbS : b.1 ∈ S := by
          refine ⟨⟨hpb, hbC.le.trans hcB⟩, ?_⟩
          change energy b.1 ≤ 0
          rw [hbEnergy]
          exact hbNonpos
        have hcb : c ≤ b.1 := csInf_le hSBdd hbS
        exact (not_lt_of_ge hcb) hbC
    obtain ⟨q, hqNonzero, hqGround⟩ := exists_suzukiWeilGroundFormVector C
    have hqNull : ccmRestrictedWeilSourceQuadratic C q = 0 := by
      rw [hqGround, suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy,
        hCEnergy, zero_mul]
    have hsmoothPos : ∀ u : CCMComplexSmoothInteriorSource C,
        ccmArchimedeanFormToAperture C u.toCCMFormVector ≠ 0 →
        0 < ccmRestrictedWeilSourceQuadratic C u.toCCMFormVector :=
      fun u hu =>
        ccmSmoothInteriorSource_source_pos_of_smaller_groundEnergy_pos
          C hbefore u hu
    refine ⟨C, q, hCEnergy, hbefore, ?_, hqNull, ?_⟩
    · intro hzero
      apply hqNonzero
      rw [← norm_eq_zero]
      rw [norm_suzukiWeilIntervalFormEmbedding_eq_physical, hzero]
      simp
    · intro u huq
      have huNonzero : ccmArchimedeanFormToAperture C u.toCCMFormVector ≠ 0 := by
        intro hzero
        apply hqNonzero
        rw [← norm_eq_zero]
        rw [norm_suzukiWeilIntervalFormEmbedding_eq_physical, ← huq, hzero]
        simp
      have huPos := hsmoothPos u huNonzero
      rw [huq, hqNull] at huPos
      exact lt_irrefl 0 huPos

end RHTower
