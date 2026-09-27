import GaloisForLFunctions.RHTower.XiCriticalFourthTraceResidual
import GaloisForLFunctions.RHTower.XiGaussianUniformCutoff

/-!
# A phase gap calibrated by the remaining fourth-trace source budget

An off-critical quartet costs at least a reciprocal fourth-power charge.
Removing an exact finite critical reserve converts that charge into an
adaptive spectral gap. The gap is never below the previously certified one.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiCriticalResidualPhaseGap (F : Finset XiZeroCopy) : ℝ :=
  max xiGaussianCertifiedPhaseGap
    (Real.sqrt ((82 / 21 : ℝ) / xiCriticalFourthTraceResidual F) - 1 / 2)

theorem xiGaussianCertifiedPhaseGap_le_residualPhaseGap (F : Finset XiZeroCopy) :
    xiGaussianCertifiedPhaseGap ≤ xiCriticalResidualPhaseGap F := le_max_left _ _

theorem xiCriticalResidualPhaseGap_pos (F : Finset XiZeroCopy) :
    0 < xiCriticalResidualPhaseGap F :=
  xiGaussianCertifiedPhaseGap_pos.trans_le (xiGaussianCertifiedPhaseGap_le_residualPhaseGap F)

/-- Every off-critical copy forces a positive residual budget and a reciprocal radial charge. -/
theorem xiCriticalFourthTraceResidual_charge (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    0 < xiCriticalFourthTraceResidual F ∧
      (82 / 21 : ℝ) ≤ xiCriticalFourthTraceResidual F * ‖xiSpectralPoint q.1‖ ^ 4 := by
  have hnorm : 0 < ‖xiSpectralPoint q.1‖ ^ 4 :=
    pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)) _
  have hsector := xiFourthTraceAtom_ge_reciprocal_norm_four q.1
  have hquartet := four_mul_xiFourthTraceAtom_le_residual F q
  have hsmall : (82 / 21 : ℝ) / ‖xiSpectralPoint q.1‖ ^ 4 ≤
      xiCriticalFourthTraceResidual F := by
    rw [div_eq_mul_one_div]
    linarith only [hsector, hquartet]
  exact ⟨(div_pos (by positivity) hnorm).trans_le hsmall, (div_le_iff₀ hnorm).mp hsmall⟩

/-- The exact finite critical reserve increases the certified off-critical spectral gap. -/
theorem xiSpectralSq_re_gt_residualPhaseGap (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    xiCriticalResidualPhaseGap F < (xiSpectralPoint q.1 ^ 2).re := by
  obtain ⟨hδ, hcharge⟩ := xiCriticalFourthTraceResidual_charge F q
  have hroot : Real.sqrt ((82 / 21 : ℝ) / xiCriticalFourthTraceResidual F) ≤
      ‖xiSpectralPoint q.1‖ ^ 2 := by
    apply (Real.sqrt_le_left (sq_nonneg _)).mpr
    rw [div_le_iff₀ hδ]
    calc
      _ ≤ xiCriticalFourthTraceResidual F * ‖xiSpectralPoint q.1‖ ^ 4 := hcharge
      _ = (‖xiSpectralPoint q.1‖ ^ 2) ^ 2 * xiCriticalFourthTraceResidual F := by ring
  have hstrip : ‖xiSpectralPoint q.1‖ ^ 2 - 1 / 2 < (xiSpectralPoint q.1 ^ 2).re := by
    have hi := xiSpectralPoint_im_sq_lt_quarter q.1
    rw [Complex.sq_norm, Complex.normSq_apply, pow_two, Complex.mul_re]
    nlinarith only [hi]
  exact max_lt_iff.mpr ⟨xiSpectralSq_re_gt_certifiedPhaseGap q,
    (sub_le_sub_right hroot (1 / 2)).trans_lt hstrip⟩

theorem xiGaussianHeadPhaseEnergy_eq_zero_below_residualGap
    (F : Finset XiZeroCopy) (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianHeadPhaseEnergy Q t (xiCriticalResidualPhaseGap F) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hqR : (xiSpectralPoint q ^ 2).re ≤ xiCriticalResidualPhaseGap F := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
  have hreal : (xiSpectralPoint q).im = 0 := by
    by_contra h
    exact (not_lt_of_ge hqR) (xiSpectralSq_re_gt_residualPhaseGap F ⟨q, h⟩)
  exact xiGaussianImaginaryChannelAtom_of_real Q t ⟨q, hreal⟩

theorem xiGaussianImaginaryChannel_eq_residualTail
    (F : Finset XiZeroCopy) (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q) =
      xiGaussianTailPhaseEnergy Q t (xiCriticalResidualPhaseGap F) := by
  have h := xiGaussianTrace_eq_realChannel_sub_head_sub_tailPhase
    Q t (xiCriticalResidualPhaseGap F)
  rw [xiGaussianHeadPhaseEnergy_eq_zero_below_residualGap, sub_zero,
    xiGaussianTrace_eq_realChannel_sub_imaginary] at h
  linarith only [h]

/-- Complete phase control at the residual-calibrated rate, uniform in all coefficients. -/
theorem xiGaussianImaginaryChannel_le_residual_anchorAt
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
          xiGaussianCoefficientAnchorAt N s * (∑ j ∈ Finset.range N, a j ^ 2) := by
  rw [xiGaussianImaginaryChannel_eq_residualTail F]
  exact (xiGaussianTailPhaseEnergy_le_energy _ t.1 (xiCriticalResidualPhaseGap F)).trans
    (xiGaussianTailEnergy_le_anchorAt N a s t (xiCriticalResidualPhaseGap F))

end RHTower
