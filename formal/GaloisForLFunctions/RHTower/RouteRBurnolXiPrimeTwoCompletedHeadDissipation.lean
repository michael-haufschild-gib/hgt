import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletionNormalDissipation
import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Completion domination of the Route R Burnol head current

The bare fixed-source current

`J(rho) = ‖(1-rho)⁻¹‖² - (log 2)² ‖rho⁻¹‖²`

is strictly positive at every hypothetical right-half Xi divisor.  The exact coefficient-faithful
prime-two completion carries an independent negative horizontal current.  This module proves that
the completion current strictly dominates the entire positive head port at every Xi divisor:

`J(rho) < -A(Im rho)`, hence `A(Im rho) + J(rho) < 0`.

The proof uses only the pre-divisor completion estimate and the source-pure Xi height gap.  It does
not assume head dissipativity, critical-line placement, source-dagger conservation, or RH.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Coefficient-faithful completion current plus the fixed physical divided-shift head current. -/
def burnolXiCompletionDressedHeadCurrent (rho : ℂ) : ℝ :=
  burnolXiCompletionCriticalNormalLogEnergySlope rho.im +
    burnolCartierDividedShiftHeadFlux rho

/-- The source-pure Xi height gap places the entire fixed physical head port below one half.
This estimate is independent of the horizontal position of the divisor. -/
theorem burnolCartierDividedShiftHeadFlux_lt_half_at_xiDivisor
    (rho : XiDivisorSupport) :
    burnolCartierDividedShiftHeadFlux (rho : ℂ) < 1 / 2 := by
  have hheight : (41 / 2 : ℝ) < (rho : ℂ).im ^ 2 :=
    xiDivisorSupport_fortyOne_div_two_lt_im_sq rho
  have hnormSq : 2 < ‖(1 : ℂ) - (rho : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub]
    nlinarith [sq_nonneg (1 - (rho : ℂ).re)]
  have hnormPos : 0 < ‖(1 : ℂ) - (rho : ℂ)‖ := by
    rw [norm_pos_iff]
    intro h
    have him : (rho : ℂ).im = 0 := by
      have := congrArg Complex.im h
      simpa using this.symm
    rw [him] at hheight
    norm_num at hheight
  have hinvSq : ‖((1 : ℂ) - (rho : ℂ))⁻¹‖ ^ 2 < 1 / 2 := by
    rw [norm_inv]
    have hcancel :
        ‖(1 : ℂ) - (rho : ℂ)‖⁻¹ ^ 2 * ‖(1 : ℂ) - (rho : ℂ)‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hnormPos), one_pow]
    nlinarith [hcancel, hnormSq, sq_nonneg ‖(1 : ℂ) - (rho : ℂ)‖⁻¹]
  unfold burnolCartierDividedShiftHeadFlux
  exact (sub_le_self _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_lt hinvSq

/-- **Completion domination.**  At every actual Xi divisor, the negative source-completion
current has strictly more magnitude than the full explicit physical head obstruction. -/
theorem burnolCartierDividedShiftHeadFlux_lt_neg_completionSlope_at_xiDivisor
    (rho : XiDivisorSupport) :
    burnolCartierDividedShiftHeadFlux (rho : ℂ) <
      -burnolXiCompletionCriticalNormalLogEnergySlope (rho : ℂ).im := by
  have hhead := burnolCartierDividedShiftHeadFlux_lt_half_at_xiDivisor rho
  have hcompletion :=
    burnolXiCompletionCriticalNormalLogEnergySlope_lt_neg_half (rho : ℂ).im
  linarith

/-- The coefficient-faithful completion-dressed Route R current is unconditionally negative on
the actual Xi divisor support. -/
theorem burnolXiCompletionDressedHeadCurrent_neg_at_xiDivisor
    (rho : XiDivisorSupport) :
    burnolXiCompletionDressedHeadCurrent (rho : ℂ) < 0 := by
  rw [burnolXiCompletionDressedHeadCurrent]
  have hdom :=
    burnolCartierDividedShiftHeadFlux_lt_neg_completionSlope_at_xiDivisor rho
  linarith

/-- On a hypothetical right-half divisor the bare port and the completed source port have strict,
opposite orientations.  This isolates the remaining comparison: descent must retain the negative
completion budget when landing on the fixed physical port. -/
theorem xiDivisor_burnolCompletionDressed_and_bareHeadCurrents_opposed
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolXiCompletionDressedHeadCurrent (rho : ℂ) < 0 ∧
      0 < burnolCartierDividedShiftHeadFlux (rho : ℂ) := by
  exact ⟨burnolXiCompletionDressedHeadCurrent_neg_at_xiDivisor rho,
    burnolCartierDividedShiftHeadFlux_pos h
      (xiDivisor_re_lt_one_of_half_lt rho h)⟩

end RHTower
