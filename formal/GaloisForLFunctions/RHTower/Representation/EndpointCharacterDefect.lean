import GaloisForLFunctions.HTGeometry.SymmetricCharacters.EndpointCoordinates
import GaloisForLFunctions.RHTower.XiStripEdgeSquaredWeightSum
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit

/-!
# The exact transposition defect of positive endpoint frequencies

Every reciprocal endpoint weight of the Xi divisor has positive real part, unconditionally.
These real parts have the correct total mass. Their second power sum, however, exceeds the
arithmetic endpoint sum rule by the sum of squared imaginary parts. Equality is exactly RH.
Thus real projection supplies positive frequencies but does not supply the required character.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.SymmetricCharacters

theorem xiStripEdgeWeight_re_pos (q : XiZeroCopy) : 0 < (xiStripEdgeWeight q).re :=
  endpointCoordinate_re_pos (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)

/-- The endpoint coordinates recover the critical-line condition without a sign premise. -/
theorem xiStripEdgeWeight_im_eq_zero_iff (q : XiZeroCopy) :
    (xiStripEdgeWeight q).im = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  exact (endpointCoordinate_im_eq_zero_iff (q.1 : ℂ)).trans
    (or_iff_left (xiSupport_im_ne_zero q.1))

theorem summable_xiStripEdgeWeight_re_sq :
    Summable (fun q => (xiStripEdgeWeight q).re ^ 2) := by
  apply Summable.of_norm_bounded hasSum_xiStripEdgeWeight_sq.summable.norm
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_pow]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (xiStripEdgeWeight q).re)
    (Complex.abs_re_le_norm (xiStripEdgeWeight q)) 2

theorem summable_xiStripEdgeWeight_im_sq :
    Summable (fun q => (xiStripEdgeWeight q).im ^ 2) := by
  apply Summable.of_norm_bounded hasSum_xiStripEdgeWeight_sq.summable.norm
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_pow]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (xiStripEdgeWeight q).im)
    (Complex.abs_im_le_norm (xiStripEdgeWeight q)) 2

/-- The total positive color mass, with zero multiplicities counted. -/
def xiEndpointColorMass : ℝ := ∑' q, (xiStripEdgeWeight q).re

/-- The second moment of the positive real-part alphabet. -/
def xiEndpointPositiveSecondMoment : ℝ := ∑' q, (xiStripEdgeWeight q).re ^ 2

/-- The second power sum specified by the completed endpoint jet. -/
def xiEndpointSourceSecondMoment : ℝ :=
  (2 * (completedRiemannZeta₀ 1 ^ 2 - 2 * deriv completedRiemannZeta₀ 1)).re

/-- The exact orientation discarded by real projection of the endpoint alphabet. -/
def xiEndpointOrientationEnergy : ℝ := ∑' q, (xiStripEdgeWeight q).im ^ 2

theorem xiEndpointColorMass_eq : xiEndpointColorMass = poleSharpConstant := by
  rw [xiEndpointColorMass, ← Complex.re_tsum summable_xiStripEdgeWeight]
  simpa only [xiStripEdgeWeight, one_div] using
    tsum_inv_zero_mul_one_sub_zero_re

theorem xiEndpointColorMass_pos : 0 < xiEndpointColorMass := by
  rw [xiEndpointColorMass_eq]
  exact poleSharpConstant_pos

/-- Positive and holomorphic transposition moments differ by an exact nonnegative energy. -/
theorem xiEndpointSecondMoment_gap :
    xiEndpointPositiveSecondMoment - xiEndpointSourceSecondMoment =
      xiEndpointOrientationEnergy := by
  have h : xiEndpointPositiveSecondMoment - xiEndpointOrientationEnergy =
      xiEndpointSourceSecondMoment := by
    calc
      xiEndpointPositiveSecondMoment - xiEndpointOrientationEnergy =
          ∑' q, ((xiStripEdgeWeight q).re ^ 2 - (xiStripEdgeWeight q).im ^ 2) := by
        exact (summable_xiStripEdgeWeight_re_sq.tsum_sub
          summable_xiStripEdgeWeight_im_sq).symm
      _ = ∑' q, (xiStripEdgeWeight q ^ 2).re := by
        apply tsum_congr
        intro q
        simp only [pow_two, Complex.mul_re]
      _ = xiEndpointSourceSecondMoment := by
        rw [← Complex.re_tsum hasSum_xiStripEdgeWeight_sq.summable,
          hasSum_xiStripEdgeWeight_sq.tsum_eq]
        rfl
  linarith

theorem xiEndpointOrientationEnergy_nonneg : 0 ≤ xiEndpointOrientationEnergy :=
  tsum_nonneg fun q => sq_nonneg (xiStripEdgeWeight q).im

/-- The endpoint real-part substitution is exact if and only if RH holds. -/
theorem xiEndpointOrientationEnergy_eq_zero_iff_rh :
    xiEndpointOrientationEnergy = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
    have hterm := summable_xiStripEdgeWeight_im_sq.le_tsum q
      (fun j _ => sq_nonneg (xiStripEdgeWeight j).im)
    change (xiStripEdgeWeight q).im ^ 2 ≤ xiEndpointOrientationEnergy at hterm
    rw [hzero] at hterm
    have him : (xiStripEdgeWeight q).im = 0 := by
      nlinarith only [hterm, sq_nonneg (xiStripEdgeWeight q).im]
    rw [(xiStripEdgeWeight_im_eq_zero_iff q).mp him] at hq
    exact lt_irrefl _ hq
  · intro hRH
    unfold xiEndpointOrientationEnergy
    have hterm (q : XiZeroCopy) : (xiStripEdgeWeight q).im ^ 2 = 0 := by
      rw [(xiStripEdgeWeight_im_eq_zero_iff q).mpr
        (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q), zero_pow (by omega : 2 ≠ 0)]
    simp only [hterm, tsum_zero]

/-- Matching the single transposition moment is already equivalent to RH for this alphabet. -/
theorem xiEndpointSecondMoment_eq_source_iff_rh :
    xiEndpointPositiveSecondMoment = xiEndpointSourceSecondMoment ↔ RiemannHypothesis := by
  rw [← xiEndpointOrientationEnergy_eq_zero_iff_rh, ← xiEndpointSecondMoment_gap,
    sub_eq_zero]

/-- Transposition value of the normalized positive endpoint alphabet. -/
def xiEndpointPositiveTransposition : ℝ :=
  xiEndpointPositiveSecondMoment / xiEndpointColorMass ^ 2

/-- Transposition value prescribed by the arithmetic endpoint jet. -/
def xiEndpointSourceTransposition : ℝ :=
  xiEndpointSourceSecondMoment / xiEndpointColorMass ^ 2

theorem xiEndpointTransposition_gap :
    xiEndpointPositiveTransposition - xiEndpointSourceTransposition =
      xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 := by
  rw [xiEndpointPositiveTransposition, xiEndpointSourceTransposition, ← sub_div,
    xiEndpointSecondMoment_gap]

theorem xiEndpointTransposition_eq_source_iff_rh :
    xiEndpointPositiveTransposition = xiEndpointSourceTransposition ↔ RiemannHypothesis := by
  rw [xiEndpointPositiveTransposition, xiEndpointSourceTransposition,
    div_left_inj' (pow_ne_zero 2 xiEndpointColorMass_pos.ne'),
    xiEndpointSecondMoment_eq_source_iff_rh]

end RHTower
