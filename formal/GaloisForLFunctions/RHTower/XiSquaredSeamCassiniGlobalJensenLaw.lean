import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniPairQuotient
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniJensenSourceLaw

open Complex Real MeasureTheory Metric Set
open scoped ENNReal

namespace RHTower

noncomputable section

theorem xiSquaredSeamCassiniSourceKernel_tsum_eq_jensenExcess
    {r : ℝ} (hr : 0 < r) :
    ∑' c : XiSquaredSeamCassiniZeroCopy,
        xiSquaredSeamCassiniSourcePowerSixtyFourJensenKernel c r =
      ENNReal.ofReal (xiSquaredSeamCassiniJensenExcess r / r ^ 65) := by
  rw [ENNReal.tsum_sigma']
  simp_rw [xiSquaredSeamCassiniSourcePowerSixtyFourJensenKernel,
    tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  let D := MeromorphicOn.divisor xiSquaredSeamCassiniSource (closedBall 0 r)
  let G : ℂ → ℝ≥0∞ := fun u =>
    (analyticOrderAt xiSquaredSeamCassiniSource u).toNat •
      if ‖u‖ ≤ r then ENNReal.ofReal (Real.log (r / ‖u‖) / r ^ 65) else 0
  change (∑' a : XiSquaredSeamCassiniZeroSupport, G a.1) = _
  have han : AnalyticOnNhd ℂ xiSquaredSeamCassiniSource (closedBall 0 r) :=
    fun u _ => differentiable_xiSquaredSeamCassiniSource.analyticAt u
  have hDfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall 0 r)
  have hzero_order_pos (u : ℂ) (hu : xiSquaredSeamCassiniSource u = 0) :
      0 < (analyticOrderAt xiSquaredSeamCassiniSource u).toNat := by
    have horder0 : analyticOrderAt xiSquaredSeamCassiniSource u ≠ 0 := by
      intro horder
      rcases analyticOrderAt_eq_zero.mp horder with hnotan | hne
      · exact hnotan (differentiable_xiSquaredSeamCassiniSource.analyticAt u)
      · exact hne hu
    have hordertop := xiSquaredSeamCassiniSource_order_ne_top u
    by_contra hnot
    have hnat : (analyticOrderAt xiSquaredSeamCassiniSource u).toNat = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rcases ENat.toNat_eq_zero.mp hnat with hzero | htop
    · exact horder0 hzero
    · exact hordertop htop
  have hD_eq_order (u : ℂ) (hu : u ∈ closedBall (0 : ℂ) r) :
      D u = ((analyticOrderAt xiSquaredSeamCassiniSource u).toNat : ℤ) := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hu,
      ← ENat.coe_toNat (xiSquaredSeamCassiniSource_order_ne_top u)]
    simp
  have hD_zero_of_not_mem (u : ℂ) (hu : u ∉ closedBall (0 : ℂ) r) :
      D u = 0 := by
    by_contra h
    exact hu (D.supportWithinDomain (Function.mem_support.mpr h))
  have hGfinite : Function.HasFiniteSupport
      (fun a : XiSquaredSeamCassiniZeroSupport => G a.1) := by
    have hpre : ((fun a : XiSquaredSeamCassiniZeroSupport => (a.1 : ℂ)) ⁻¹'
        D.support).Finite :=
      hDfinite.preimage (fun _ _ _ _ h => Subtype.ext h)
    apply hpre.subset
    intro a ha
    have hle : ‖(a.1 : ℂ)‖ ≤ r := by
      by_contra hnle
      have hgt : r < ‖(a.1 : ℂ)‖ := lt_of_not_ge hnle
      simp [G, not_le.mpr hgt] at ha
    have hamem : (a.1 : ℂ) ∈ closedBall (0 : ℂ) r := by
      simpa [mem_closedBall, dist_zero_right] using hle
    have hDne : D a.1 ≠ 0 := by
      rw [hD_eq_order a.1 hamem]
      exact_mod_cast (hzero_order_pos a.1 a.2).ne'
    exact Function.mem_support.mpr hDne
  rw [tsum_eq_finsum hGfinite]
  change (∑ᶠ b : {u : ℂ // xiSquaredSeamCassiniSource u = 0}, G b.1) = _
  have hcoe :
      (∑ᶠ b : {u : ℂ // xiSquaredSeamCassiniSource u = 0}, G b.1) =
        ∑ᶠ (u : ℂ) (_h : xiSquaredSeamCassiniSource u = 0), G u := by
    simpa only [Set.mem_setOf_eq] using
      (finsum_set_coe_eq_finsum_mem
        (f := G) {u : ℂ | xiSquaredSeamCassiniSource u = 0})
  rw [hcoe]
  let B : ℂ → ℝ := fun u =>
    (D u : ℝ) * Real.log (r * ‖u‖⁻¹) / r ^ 65
  have hpoint (u : ℂ) :
      (∑ᶠ (_h : xiSquaredSeamCassiniSource u = 0), G u) =
        ENNReal.ofReal (B u) := by
    by_cases hzero : xiSquaredSeamCassiniSource u = 0
    · have hu0 : u ≠ 0 := by
        intro hu
        subst u
        exact xiSquaredSeamCassiniSource_zero_ne hzero
      have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      by_cases hle : ‖u‖ ≤ r
      · have humem : u ∈ closedBall (0 : ℂ) r := by
          simpa [mem_closedBall, dist_zero_right] using hle
        have hD := hD_eq_order u humem
        simp only [hzero, finsum_true]
        rw [show G u = (analyticOrderAt xiSquaredSeamCassiniSource u).toNat •
            ENNReal.ofReal (Real.log (r / ‖u‖) / r ^ 65) by
          simp [G, hle]]
        rw [show B u =
            ((analyticOrderAt xiSquaredSeamCassiniSource u).toNat : ℝ) *
              Real.log (r / ‖u‖) / r ^ 65 by
          simp only [B, hD, Int.cast_natCast]
          rw [div_eq_mul_inv]
          ring_nf]
        rw [show ((analyticOrderAt xiSquaredSeamCassiniSource u).toNat : ℝ) *
              Real.log (r / ‖u‖) / r ^ 65 =
            ((analyticOrderAt xiSquaredSeamCassiniSource u).toNat : ℝ) *
              (Real.log (r / ‖u‖) / r ^ 65) by ring]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        simp [nsmul_eq_mul]
      · have hnotmem : u ∉ closedBall (0 : ℂ) r := by
          simpa [mem_closedBall, dist_zero_right] using hle
        have hD0 := hD_zero_of_not_mem u hnotmem
        simp [hzero, G, B, hle, hD0]
    · have hD0 : D u = 0 := by
        by_cases humem : u ∈ closedBall (0 : ℂ) r
        · rw [hD_eq_order u humem]
          have horder : analyticOrderAt xiSquaredSeamCassiniSource u = 0 :=
            analyticOrderAt_eq_zero.mpr (Or.inr hzero)
          rw [horder]
          simp
        · exact hD_zero_of_not_mem u humem
      simp [hzero, B, hD0]
  rw [show (∑ᶠ (u : ℂ) (_h : xiSquaredSeamCassiniSource u = 0), G u) =
      ∑ᶠ u : ℂ, ENNReal.ofReal (B u) by
        apply finsum_congr
        exact hpoint]
  have hBsupport : Function.support B ⊆ D.support := by
    intro u huB
    by_contra huD
    have hD0 : D u = 0 := by simpa [Function.mem_support] using huD
    apply huB
    simp [B, hD0]
  have hBfinite : Function.HasFiniteSupport B :=
    hDfinite.subset hBsupport
  have hBnonneg (u : ℂ) : 0 ≤ B u := by
    by_cases hD0 : D u = 0
    · simp [B, hD0]
    · have humem : u ∈ closedBall (0 : ℂ) r :=
        D.supportWithinDomain (Function.mem_support.mpr hD0)
      have hle : ‖u‖ ≤ r := by
        simpa [mem_closedBall, dist_zero_right] using humem
      have hu0 : u ≠ 0 := by
        intro hu
        subst u
        have hDzero : D 0 = 0 := by
          rw [hD_eq_order 0 (by simp [hr.le])]
          have horder : analyticOrderAt xiSquaredSeamCassiniSource 0 = 0 :=
            analyticOrderAt_eq_zero.mpr
              (Or.inr xiSquaredSeamCassiniSource_zero_ne)
          rw [horder]
          simp
        exact hD0 hDzero
      have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have hlog : 0 ≤ Real.log (r * ‖u‖⁻¹) := by
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, one_le_div hunorm]
        exact hle
      have hDnonneg : 0 ≤ (D u : ℝ) := by
        rw [hD_eq_order u humem]
        positivity
      exact div_nonneg (mul_nonneg hDnonneg hlog) (pow_nonneg hr.le 65)
  rw [finsum_eq_sum_of_support_subset (fun u => ENNReal.ofReal (B u))
    (s := hBfinite.toFinset) (by
      intro u huE
      rw [hBfinite.coe_toFinset, Function.mem_support]
      intro hB0
      exact huE (by simp [hB0]))]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (s := hBfinite.toFinset) (fun u _ => hBnonneg u)]
  congr 1
  rw [xiSquaredSeamCassiniJensenExcess_eq_divisor_finsum hr]
  rw [finsum_eq_sum_of_support_subset
    (fun u : ℂ => (D u : ℝ) * Real.log (r * ‖u‖⁻¹))
    (s := hDfinite.toFinset) (by
      intro u hu
      rw [hDfinite.coe_toFinset, Function.mem_support]
      intro hD0
      exact hu (by simp [hD0]))]
  rw [Finset.sum_div]
  rw [show (∑ i ∈ hBfinite.toFinset, B i) =
      ∑ i ∈ hDfinite.toFinset, B i by
    apply Finset.sum_subset
    · intro u hu
      rw [Set.Finite.mem_toFinset] at hu ⊢
      exact hBsupport hu
    · intro u _ hu
      have hnot : u ∉ Function.support B := by
        simpa only [Set.Finite.mem_toFinset] using hu
      simpa only [Function.mem_support, ne_eq, not_not] using hnot]

/-- Global power-64 radial integral of the actual Cassini-source Jensen excess. -/
def xiSquaredSeamCassiniPowerSixtyFourJensenIntegral : ℝ≥0∞ :=
  ∫⁻ r : ℝ in Ioi 0,
    ENNReal.ofReal (xiSquaredSeamCassiniJensenExcess r / r ^ 65)

/-- The Xi-copy divisor integral is exactly twice the Cassini-source circle integral. -/
theorem xiSquaredSeamPowerSixtyFourJensenDivisorIntegral_eq_two_mul_cassiniIntegral :
    xiSquaredSeamPowerSixtyFourJensenDivisorIntegral =
      2 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral := by
  rw [xiSquaredSeamPowerSixtyFourJensenDivisorIntegral,
    xiSquaredSeamCassiniPowerSixtyFourJensenIntegral]
  calc
    (∫⁻ r : ℝ in Ioi 0,
        ∑' q : XiZeroCopy, xiSquaredSeamPowerSixtyFourJensenKernel q r) =
        ∫⁻ r : ℝ in Ioi 0,
          2 * ENNReal.ofReal
            (xiSquaredSeamCassiniJensenExcess r / r ^ 65) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [xiSquaredSeamPowerSixtyFourJensenKernel_tsum_eq_two_mul_source_tsum,
        xiSquaredSeamCassiniSourceKernel_tsum_eq_jensenExcess hr]
    _ = 2 * ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (xiSquaredSeamCassiniJensenExcess r / r ^ 65) := by
      exact lintegral_const_mul' 2 _ (by norm_num)

theorem xiSquaredSeamPowerSixtyFourHermitianMass_nonneg :
    0 ≤ xiSquaredSeamPowerSixtyFourHermitianMass := by
  rw [xiSquaredSeamPowerSixtyFourHermitianMass]
  exact tsum_nonneg fun _ => norm_nonneg _

/-- Exact global Cassini--Jensen identity: one source sheet carries `1/8192` of the power-64
Hermitian seam mass. -/
theorem xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_eq_hermitianMass :
    xiSquaredSeamCassiniPowerSixtyFourJensenIntegral =
      ENNReal.ofReal (xiSquaredSeamPowerSixtyFourHermitianMass / 8192) := by
  apply (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num)).mp
  calc
    2 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral =
        xiSquaredSeamPowerSixtyFourJensenDivisorIntegral :=
      xiSquaredSeamPowerSixtyFourJensenDivisorIntegral_eq_two_mul_cassiniIntegral.symm
    _ = ENNReal.ofReal (xiSquaredSeamPowerSixtyFourHermitianMass / 4096) :=
      xiSquaredSeamPowerSixtyFourJensenDivisorIntegral_eq_hermitianMass
    _ = 2 * ENNReal.ofReal
        (xiSquaredSeamPowerSixtyFourHermitianMass / 8192) := by
      rw [show xiSquaredSeamPowerSixtyFourHermitianMass / 4096 =
          2 * (xiSquaredSeamPowerSixtyFourHermitianMass / 8192) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_toReal :
    xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal =
      xiSquaredSeamPowerSixtyFourHermitianMass / 8192 := by
  rw [xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_eq_hermitianMass,
    ENNReal.toReal_ofReal]
  exact div_nonneg xiSquaredSeamPowerSixtyFourHermitianMass_nonneg (by norm_num)

/-- Exact Cassini-source expression for the remaining transverse variance.  This identifies the
rightmost open source inequality with vanishing, not mere boundedness, of one nonnegative charge. -/
theorem xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual :
    xiSquaredSeamPowerThirtyTwoTransverseCharge =
      4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal -
        (primeArchShiftedReciprocalMoment 1 63).re / 2 := by
  have hgap := xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect
  rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge] at hgap
  rw [xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_toReal]
  nlinarith

theorem cassiniJensenResidual_nonneg :
    0 ≤ 4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal -
      (primeArchShiftedReciprocalMoment 1 63).re / 2 := by
  rw [← xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual]
  exact tsum_nonneg fun _ => sq_nonneg _

theorem cassiniJensenResidual_eq_zero_iff_riemannHypothesis :
    4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal -
        (primeArchShiftedReciprocalMoment 1 63).re / 2 = 0 ↔
      RiemannHypothesis := by
  rw [← xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual,
    xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis]

/-- Reverse source inequality written entirely as a circle-average law for the unconditional
Cassini entire source. -/
def XiSquaredSeamCassiniJensenDominated : Prop :=
  8192 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal ≤
    (primeArchShiftedReciprocalMoment 1 63).re

/-- Exact RH endpoint for the global Cassini-source Jensen law. -/
theorem xiSquaredSeamCassiniJensenDominated_iff_riemannHypothesis :
    XiSquaredSeamCassiniJensenDominated ↔ RiemannHypothesis := by
  rw [XiSquaredSeamCassiniJensenDominated,
    xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_toReal]
  have hcancel : 8192 *
      (xiSquaredSeamPowerSixtyFourHermitianMass / 8192) =
        xiSquaredSeamPowerSixtyFourHermitianMass := by ring
  rw [hcancel]
  exact xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis

end

end RHTower
