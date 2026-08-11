import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletedHeadDissipation
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Functional-equation partner classification of the Route R Burnol current

For the Xi reflection partner `rho^dagger = 1 - conj rho`, the two reciprocal heads exchange.
This module computes the reflected bare and completion-dressed currents exactly.  Their odd part is
the horizontal coordinate times a strictly positive factor; their bare even part is strictly
positive away from `0` and `1`.

Consequently equality of either current with its functional-equation partner is exactly critical
line placement, and equality at every actual Xi divisor is equivalent to RH.  This is a closed
classification/no-go theorem, not an annihilation producer: functional-equation covariance alone
relates the two partner fibres and cannot identify their scalar currents without supplying the
RH-equivalent horizontal conclusion.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Functional-equation partner `rho^dagger = 1 - conj rho`. -/
def burnolXiReflectionPartner (rho : ℂ) : ℂ := 1 - conj rho

@[simp] theorem burnolXiReflectionPartner_re (rho : ℂ) :
    (burnolXiReflectionPartner rho).re = 1 - rho.re := by
  simp [burnolXiReflectionPartner]

@[simp] theorem burnolXiReflectionPartner_im (rho : ℂ) :
    (burnolXiReflectionPartner rho).im = rho.im := by
  simp [burnolXiReflectionPartner]

@[simp] theorem burnolXiReflectionPartner_involutive (rho : ℂ) :
    burnolXiReflectionPartner (burnolXiReflectionPartner rho) = rho := by
  apply Complex.ext <;> simp [burnolXiReflectionPartner]

/-- Reflection exchanges the two reciprocal heads of the bare current. -/
theorem burnolCartierDividedShiftHeadFlux_reflectionPartner (rho : ℂ) :
    burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) =
      ‖rho⁻¹‖ ^ 2 - (Real.log 2) ^ 2 * ‖((1 : ℂ) - rho)⁻¹‖ ^ 2 := by
  have hforward :
      ‖((1 : ℂ) - burnolXiReflectionPartner rho)⁻¹‖ = ‖rho⁻¹‖ := by
    simp [burnolXiReflectionPartner]
  have hreflected :
      ‖(burnolXiReflectionPartner rho)⁻¹‖ = ‖((1 : ℂ) - rho)⁻¹‖ := by
    rw [norm_inv, norm_inv]
    simpa [burnolXiReflectionPartner] using norm_conj ((1 : ℂ) - rho)
  rw [burnolCartierDividedShiftHeadFlux, hforward, hreflected]

/-- The reflection-even bare current is a positive coefficient times the total reciprocal energy. -/
theorem burnolCartierDividedShiftHeadFlux_add_reflectionPartner (rho : ℂ) :
    burnolCartierDividedShiftHeadFlux rho +
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) =
      (1 - (Real.log 2) ^ 2) *
        (‖((1 : ℂ) - rho)⁻¹‖ ^ 2 + ‖rho⁻¹‖ ^ 2) := by
  rw [burnolCartierDividedShiftHeadFlux,
    burnolCartierDividedShiftHeadFlux_reflectionPartner]
  ring

/-- The reflection-odd bare current is the difference of the two reciprocal energies. -/
theorem burnolCartierDividedShiftHeadFlux_sub_reflectionPartner (rho : ℂ) :
    burnolCartierDividedShiftHeadFlux rho -
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) =
      (1 + (Real.log 2) ^ 2) *
        (‖((1 : ℂ) - rho)⁻¹‖ ^ 2 - ‖rho⁻¹‖ ^ 2) := by
  rw [burnolCartierDividedShiftHeadFlux,
    burnolCartierDividedShiftHeadFlux_reflectionPartner]
  ring

/-- Exact horizontal factorization of the reflection-odd current away from its two poles. -/
theorem burnolCartierDividedShiftHeadFlux_sub_reflectionPartner_eq_horizontal
    {rho : ℂ} (hrho : rho ≠ 0) (hrhoOne : rho ≠ 1) :
    burnolCartierDividedShiftHeadFlux rho -
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) =
      (1 + (Real.log 2) ^ 2) * (2 * rho.re - 1) /
        (‖rho‖ ^ 2 * ‖(1 - rho)‖ ^ 2) := by
  have hnormRho : ‖rho‖ ≠ 0 := norm_ne_zero_iff.mpr hrho
  have hnormOneSub : ‖(1 - rho)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  have hhorizontal : ‖rho‖ ^ 2 - ‖(1 - rho)‖ ^ 2 = 2 * rho.re - 1 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  rw [burnolCartierDividedShiftHeadFlux_sub_reflectionPartner, norm_inv, norm_inv]
  rw [← hhorizontal]
  field_simp [hnormRho, hnormOneSub]
  ring

/-- The bare reflection-pair sum is strictly positive away from the reciprocal poles. -/
theorem burnolCartierDividedShiftHeadFlux_add_reflectionPartner_pos
    {rho : ℂ} (hrho : rho ≠ 0) (hrhoOne : rho ≠ 1) :
    0 < burnolCartierDividedShiftHeadFlux rho +
      burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) := by
  rw [burnolCartierDividedShiftHeadFlux_add_reflectionPartner]
  have hlogPos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogLt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hcoefficient : 0 < 1 - (Real.log 2) ^ 2 := by nlinarith
  have hleft : 0 < ‖((1 : ℂ) - rho)⁻¹‖ ^ 2 := by
    positivity
  have hright : 0 < ‖rho⁻¹‖ ^ 2 := by
    positivity
  positivity

/-- Equality with the functional-equation partner is exactly the critical line. -/
theorem burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff
    {rho : ℂ} (hrho : rho ≠ 0) (hrhoOne : rho ≠ 1) :
    burnolCartierDividedShiftHeadFlux rho =
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) ↔
      rho.re = 1 / 2 := by
  rw [← sub_eq_zero, burnolCartierDividedShiftHeadFlux_sub_reflectionPartner_eq_horizontal
    hrho hrhoOne]
  have hden : ‖rho‖ ^ 2 * ‖(1 - rho)‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hrho))
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)))
  have hcoefficient : 1 + (Real.log 2) ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff, mul_eq_zero, or_iff_right hcoefficient,
    or_iff_left hden]
  constructor <;> intro h <;> linarith

/-- On the open right half of the critical strip, the bare current strictly exceeds its partner. -/
theorem burnolCartierDividedShiftHeadFlux_reflectionPartner_lt
    {rho : ℂ} (hrho : rho ≠ 0) (hrhoOne : rho ≠ 1) (hright : 1 / 2 < rho.re) :
    burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) <
      burnolCartierDividedShiftHeadFlux rho := by
  rw [← sub_pos]
  rw [burnolCartierDividedShiftHeadFlux_sub_reflectionPartner_eq_horizontal hrho hrhoOne]
  have hden : 0 < ‖rho‖ ^ 2 * ‖(1 - rho)‖ ^ 2 := by
    have h0 : 0 < ‖rho‖ := norm_pos_iff.mpr hrho
    have h1 : 0 < ‖(1 : ℂ) - rho‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
    positivity
  have hcoefficient : 0 < 1 + (Real.log 2) ^ 2 := by positivity
  positivity

/-- Completion contributes the same normal current to functional-equation partners, hence cancels
from their odd difference. -/
theorem burnolXiCompletionDressedHeadCurrent_sub_reflectionPartner (rho : ℂ) :
    burnolXiCompletionDressedHeadCurrent rho -
        burnolXiCompletionDressedHeadCurrent (burnolXiReflectionPartner rho) =
      burnolCartierDividedShiftHeadFlux rho -
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner rho) := by
  simp only [burnolXiCompletionDressedHeadCurrent, burnolXiReflectionPartner_im]
  ring

/-- Dressed partner equality is the same bare-current equality. -/
theorem burnolXiCompletionDressedHeadCurrent_eq_reflectionPartner_iff
    {rho : ℂ} (hrho : rho ≠ 0) (hrhoOne : rho ≠ 1) :
    burnolXiCompletionDressedHeadCurrent rho =
        burnolXiCompletionDressedHeadCurrent (burnolXiReflectionPartner rho) ↔
      rho.re = 1 / 2 := by
  rw [← sub_eq_zero, burnolXiCompletionDressedHeadCurrent_sub_reflectionPartner,
    sub_eq_zero]
  exact burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff hrho hrhoOne

private theorem xiDivisorSupport_ne_zero (rho : XiDivisorSupport) : (rho : ℂ) ≠ 0 := by
  intro hzero
  have him := xi_divisor_support_im_ne_zero rho
  apply him
  simpa [hzero]

private theorem xiDivisorSupport_ne_one (rho : XiDivisorSupport) : (rho : ℂ) ≠ 1 := by
  intro hone
  have him := xi_divisor_support_im_ne_zero rho
  apply him
  simpa [hone]

/-- Unconditional Xi-support specialization: bare partner equality is the critical-line condition. -/
theorem xiDivisor_burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff
    (rho : XiDivisorSupport) :
    burnolCartierDividedShiftHeadFlux (rho : ℂ) =
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner (rho : ℂ)) ↔
      (rho : ℂ).re = 1 / 2 :=
  burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff
    (xiDivisorSupport_ne_zero rho) (xiDivisorSupport_ne_one rho)

/-- Unconditional Xi-support specialization for the completion-dressed current. -/
theorem xiDivisor_burnolXiCompletionDressedHeadCurrent_eq_reflectionPartner_iff
    (rho : XiDivisorSupport) :
    burnolXiCompletionDressedHeadCurrent (rho : ℂ) =
        burnolXiCompletionDressedHeadCurrent (burnolXiReflectionPartner (rho : ℂ)) ↔
      (rho : ℂ).re = 1 / 2 :=
  burnolXiCompletionDressedHeadCurrent_eq_reflectionPartner_iff
    (xiDivisorSupport_ne_zero rho) (xiDivisorSupport_ne_one rho)

/-- **Bare-current RH classification.** Global equality with the functional-equation partner is
not a free reflection law: it is exactly RH. -/
theorem riemannHypothesis_iff_forall_xiDivisor_burnolHeadFlux_eq_reflectionPartner :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport,
      burnolCartierDividedShiftHeadFlux (rho : ℂ) =
        burnolCartierDividedShiftHeadFlux (burnolXiReflectionPartner (rho : ℂ)) := by
  constructor
  · intro hRH rho
    exact (xiDivisor_burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (xiDivisor_burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff rho).1 (h rho)

/-- **Dressed-current RH classification.** Completion does not change the reflection-odd
coordinate, so global partner covariance of the dressed scalar is also exactly RH. -/
theorem riemannHypothesis_iff_forall_xiDivisor_burnolDressedHeadCurrent_eq_reflectionPartner :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport,
      burnolXiCompletionDressedHeadCurrent (rho : ℂ) =
        burnolXiCompletionDressedHeadCurrent (burnolXiReflectionPartner (rho : ℂ)) := by
  constructor
  · intro hRH rho
    exact (xiDivisor_burnolXiCompletionDressedHeadCurrent_eq_reflectionPartner_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (xiDivisor_burnolXiCompletionDressedHeadCurrent_eq_reflectionPartner_iff rho).1 (h rho)

end RHTower
