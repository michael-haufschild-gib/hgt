import GaloisForLFunctions.RHTower.XiGaussianPhaseTail
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization

/-!
# The arithmetic source gap removes a whole band from the phase channel

The optimized fourth reciprocal-trace budget confines every off-critical
copy above a fixed real spectral-square threshold. Every imaginary-channel
atom below that threshold vanishes exactly. Thus the complete phase energy
is a tail at this fixed arithmetic threshold, with every polynomial mixed
term and divisor multiplicity retained.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiGaussianCertifiedPhaseGap : ℝ := xiOrderTwentyThreeOptimizedHeightSq - 1 / 4

theorem xiGaussianCertifiedPhaseGap_eq :
    xiGaussianCertifiedPhaseGap = 430849 / 2000 := by
  unfold xiGaussianCertifiedPhaseGap xiOrderTwentyThreeOptimizedHeightSq
  ring

theorem xiGaussianCertifiedPhaseGap_pos : 0 < xiGaussianCertifiedPhaseGap := by
  rw [xiGaussianCertifiedPhaseGap_eq]
  positivity

/-- Every possible phase-producing copy lies strictly beyond the arithmetic gap. -/
theorem xiSpectralSq_re_gt_certifiedPhaseGap
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    xiGaussianCertifiedPhaseGap < (xiSpectralPoint q.1 ^ 2).re := by
  have hoff : (q.1.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    apply q.property
    rw [xiSpectralPoint_im_eq, h, sub_self]
  have hh := orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine q.1 hoff
  have hi := xiSpectralPoint_im_sq_lt_quarter q.1
  rw [pow_two, Complex.mul_re, xiSpectralPoint_re_eq]
  unfold xiGaussianCertifiedPhaseGap
  nlinarith only [hh, hi]

/-- All actual copies in the certified band are critical-line copies. -/
theorem xiSpectralPoint_im_eq_zero_in_certifiedPhaseBand
    (q : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).re ≤ xiGaussianCertifiedPhaseGap}) :
    (xiSpectralPoint q.1).im = 0 := by
  by_contra h
  exact (not_lt_of_ge q.property) (xiSpectralSq_re_gt_certifiedPhaseGap ⟨q.1, h⟩)

theorem xiGaussianImaginaryChannelAtom_eq_zero_in_certifiedPhaseBand
    (Q : Polynomial ℝ) (t : ℝ)
    (q : {q : XiZeroCopy // (xiSpectralPoint q ^ 2).re ≤ xiGaussianCertifiedPhaseGap}) :
    xiGaussianImaginaryChannelAtom Q t q.1 = 0 :=
  xiGaussianImaginaryChannelAtom_of_real Q t
    ⟨q.1, xiSpectralPoint_im_eq_zero_in_certifiedPhaseBand q⟩

/-- The certified part of the finite head has exactly zero phase energy, at every time. -/
theorem xiGaussianHeadPhaseEnergy_eq_zero_below_certifiedGap
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t})
    (R : {R : ℝ // R ≤ xiGaussianCertifiedPhaseGap}) :
    xiGaussianHeadPhaseEnergy Q t R = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hqR : (xiSpectralPoint q ^ 2).re ≤ (R : ℝ) := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
  exact xiGaussianImaginaryChannelAtom_eq_zero_in_certifiedPhaseBand Q t
    ⟨q, hqR.trans R.property⟩

/-- An arbitrary finite head retains only its exact phase-producing annulus. -/
theorem xiGaussianHeadPhaseEnergy_eq_certifiedAnnulus
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiGaussianHeadPhaseEnergy Q t R =
      ∑ q ∈ (finite_xiHeatShell R).toFinset.filter
        (fun q => xiGaussianCertifiedPhaseGap < (xiSpectralPoint q ^ 2).re),
          xiGaussianImaginaryChannelAtom Q t q := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  have hle : (xiSpectralPoint q ^ 2).re ≤ xiGaussianCertifiedPhaseGap := by
    simpa only [Finset.mem_filter, hq, true_and, not_lt] using hnot
  exact xiGaussianImaginaryChannelAtom_eq_zero_in_certifiedPhaseBand Q t ⟨q, hle⟩

/-- The whole imaginary channel, including the previous finite remainder, is a tail
at the certified arithmetic cutoff. -/
theorem xiGaussianImaginaryChannel_eq_certifiedTail
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q) =
      xiGaussianTailPhaseEnergy Q t xiGaussianCertifiedPhaseGap := by
  have h := xiGaussianTrace_eq_realChannel_sub_head_sub_tailPhase
    Q t xiGaussianCertifiedPhaseGap
  rw [xiGaussianHeadPhaseEnergy_eq_zero_below_certifiedGap Q t
    ⟨xiGaussianCertifiedPhaseGap, le_rfl⟩, sub_zero,
    xiGaussianTrace_eq_realChannel_sub_imaginary] at h
  linarith only [h]

end RHTower
