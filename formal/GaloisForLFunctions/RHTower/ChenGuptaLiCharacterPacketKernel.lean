/-
# Chen--Gupta--Li character-packet interval kernel

The interval identity in `ChenGuptaLiCharacterPacketInterval` leaves the
elementary oscillatory kernel

`∫_A^B exp(i tτ) conj(exp(i uτ)) dτ`.

This module computes its diagonal exactly and bounds every distinct-ordinate
pair by the reciprocal gap.  That is the analytic input consumed by the
harmonic separated-row estimate in the next CGL Lemma 9.1 layer.

No RH, GRH, smoothness, separation, large-value, or zero-density premise is
used.  Distinctness is carried by a certified pair datum.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketInterval

open Complex MeasureTheory

noncomputable section

namespace RHTower

/-- Product of two source waves is the difference-frequency wave. -/
theorem cglCharacterPacketWave_mul_conj (t u τ : ℝ) :
    cglCharacterPacketWave t τ * star (cglCharacterPacketWave u τ) =
      Complex.exp ((((t - u) * τ : ℝ) : ℂ) * Complex.I) := by
  unfold cglCharacterPacketWave
  change Complex.exp (((t * τ : ℝ) : ℂ) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp (((u * τ : ℝ) : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Two distinct real ordinates, certified as data so the reciprocal-gap
kernel theorem does not take an external non-equality premise. -/
def CGLDistinctOrdinatePair := {p : ℝ × ℝ // p.1 ≠ p.2}

/-- Off-diagonal interval kernel bound.  It is uniform in the interval
endpoints and follows from the exact complex exponential antiderivative. -/
theorem norm_cglCharacterPacketIntervalKernel_le (A B : ℝ)
    (p : CGLDistinctOrdinatePair) :
    ‖cglCharacterPacketIntervalKernel A B p.1.1 p.1.2‖ ≤ 2 / |p.1.1 - p.1.2| := by
  let c : ℂ := (((p.1.1 - p.1.2 : ℝ) : ℂ) * Complex.I)
  have hc : c ≠ 0 := by
    have hdiff : p.1.1 - p.1.2 ≠ 0 := sub_ne_zero.mpr p.2
    dsimp [c]
    exact mul_ne_zero (ofReal_ne_zero.mpr hdiff) Complex.I_ne_zero
  have hnormc : ‖c‖ = |p.1.1 - p.1.2| := by
    dsimp [c]
    rw [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
  have hnormB : ‖Complex.exp (c * (B : ℂ))‖ = 1 := by
    rw [show c * (B : ℂ) =
      (((p.1.1 - p.1.2) * B : ℝ) : ℂ) * Complex.I by
        dsimp [c]
        push_cast
        ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnormA : ‖Complex.exp (c * (A : ℂ))‖ = 1 := by
    rw [show c * (A : ℂ) =
      (((p.1.1 - p.1.2) * A : ℝ) : ℂ) * Complex.I by
        dsimp [c]
        push_cast
        ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hphase : ∀ τ : ℝ,
      Complex.exp ((((p.1.1 - p.1.2) * τ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (c * (τ : ℂ)) := by
    intro τ
    rw [show c * (τ : ℂ) =
      (((p.1.1 - p.1.2) * τ : ℝ) : ℂ) * Complex.I by
        dsimp [c]
        push_cast
        ring]
  unfold cglCharacterPacketIntervalKernel
  rw [intervalIntegral.integral_congr
    (fun τ _ => cglCharacterPacketWave_mul_conj _ _ _)]
  rw [intervalIntegral.integral_congr (fun τ _ => hphase τ)]
  rw [integral_exp_mul_complex hc, norm_div, hnormc]
  apply div_le_div_of_nonneg_right
  · calc
      ‖Complex.exp (c * (B : ℂ)) - Complex.exp (c * (A : ℂ))‖ ≤
          ‖Complex.exp (c * (B : ℂ))‖ + ‖Complex.exp (c * (A : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [hnormB, hnormA]; norm_num
  · exact (abs_pos.mpr (sub_ne_zero.mpr p.2)).le

/-- The diagonal interval kernel is exactly the signed interval length. -/
theorem cglCharacterPacketIntervalKernel_self (A B t : ℝ) :
    cglCharacterPacketIntervalKernel A B t t = (B - A : ℝ) := by
  unfold cglCharacterPacketIntervalKernel
  rw [intervalIntegral.integral_congr
    (fun τ _ => cglCharacterPacketWave_mul_conj _ _ _)]
  have hzero : ∀ τ : ℝ, Complex.exp ((((t - t) * τ : ℝ) : ℂ) * Complex.I) = 1 := by
    intro τ
    simp
  rw [intervalIntegral.integral_congr (fun τ _ => hzero τ)]
  simp

end RHTower
