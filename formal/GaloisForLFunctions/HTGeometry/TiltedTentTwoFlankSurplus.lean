import GaloisForLFunctions.HTGeometry.TiltedTentRightFlank
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-!
# Bilateral tilted-tent surplus

This module computes the exact bilateral Laplace transform of a triangular tent and proves that
Suzuki's critical tilt-width pair has more continuum flank surplus than a width-two bicausal seam.
-/

/-- Full normalized triangular tent with exponential tilt on its support interval. -/
def tiltedTentFullProfile (beta L x : ℝ) : ℝ :=
  Real.exp (beta * x) * (1 - |x| / L)

private def tiltedTentLeftPrimitive (beta L x : ℝ) : ℝ :=
  Real.exp (beta * x) * ((1 + x / L) / beta - 1 / (L * beta ^ (2 : ℕ)))

private def tiltedTentRightPrimitive (beta L x : ℝ) : ℝ :=
  Real.exp (beta * x) * ((1 - x / L) / beta + 1 / (L * beta ^ (2 : ℕ)))

private lemma hasDerivAt_tiltedTentLeftPrimitive
    {beta L x : ℝ} (hbeta : beta ≠ 0) (hL : L ≠ 0) :
    HasDerivAt (tiltedTentLeftPrimitive beta L)
      (Real.exp (beta * x) * (1 + x / L)) x := by
  convert! ((((hasDerivAt_id x).const_mul beta).exp).mul
    ((((hasDerivAt_const x 1).add ((hasDerivAt_id x).div_const L)).div_const beta).sub
      (hasDerivAt_const x (1 / (L * beta ^ (2 : ℕ)))))) using 1
  all_goals (dsimp; field_simp [hbeta, hL]; ring_nf)

private lemma hasDerivAt_tiltedTentRightPrimitive
    {beta L x : ℝ} (hbeta : beta ≠ 0) (hL : L ≠ 0) :
    HasDerivAt (tiltedTentRightPrimitive beta L)
      (Real.exp (beta * x) * (1 - x / L)) x := by
  convert! ((((hasDerivAt_id x).const_mul beta).exp).mul
    ((((hasDerivAt_const x 1).sub ((hasDerivAt_id x).div_const L)).div_const beta).add
      (hasDerivAt_const x (1 / (L * beta ^ (2 : ℕ)))))) using 1
  all_goals (dsimp; field_simp [hbeta, hL]; ring_nf)

private theorem integral_tiltedTentLeftProfile
    {beta L : ℝ} (hbeta : beta ≠ 0) (hL : L ≠ 0) :
    (∫ x : ℝ in -L..0, Real.exp (beta * x) * (1 + x / L)) =
      (beta * L - 1 + Real.exp (-beta * L)) / (L * beta ^ (2 : ℕ)) := by
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.exp (beta * x) * (1 + x / L)) volume (-L) 0 :=
    (by fun_prop : Continuous
      (fun x : ℝ => Real.exp (beta * x) * (1 + x / L))).intervalIntegrable (-L) 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_tiltedTentLeftPrimitive hbeta hL) hint]
  simp only [tiltedTentLeftPrimitive, mul_zero, Real.exp_zero, zero_div, add_zero, neg_div]
  rw [show beta * -L = -(beta * L) by ring]
  field_simp [hbeta, hL]
  ring

private theorem integral_tiltedTentRightProfile
    {beta L : ℝ} (hbeta : beta ≠ 0) (hL : L ≠ 0) :
    (∫ x : ℝ in 0..L, Real.exp (beta * x) * (1 - x / L)) =
      (Real.exp (beta * L) - beta * L - 1) / (L * beta ^ (2 : ℕ)) := by
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.exp (beta * x) * (1 - x / L)) volume 0 L :=
    (by fun_prop : Continuous
      (fun x : ℝ => Real.exp (beta * x) * (1 - x / L))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_tiltedTentRightPrimitive hbeta hL) hint]
  simp only [tiltedTentRightPrimitive, mul_zero, Real.exp_zero, zero_div, sub_zero]
  field_simp [hbeta, hL]
  ring

/-- Exact bilateral Laplace transform of the triangular tent. -/
theorem integral_tiltedTentFullProfile
    {beta L : ℝ} (hbeta : beta ≠ 0) (hL : 0 < L) :
    (∫ x : ℝ in -L..L, tiltedTentFullProfile beta L x) =
      2 * (Real.cosh (beta * L) - 1) / (L * beta ^ (2 : ℕ)) := by
  have hleft : IntervalIntegrable (tiltedTentFullProfile beta L) volume (-L) 0 := by
    change IntervalIntegrable
      (fun x : ℝ => Real.exp (beta * x) * (1 - |x| / L)) volume (-L) 0
    have hcont : Continuous (fun x : ℝ => Real.exp (beta * x) * (1 - |x| / L)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) (-L) 0
  have hright : IntervalIntegrable (tiltedTentFullProfile beta L) volume 0 L := by
    change IntervalIntegrable
      (fun x : ℝ => Real.exp (beta * x) * (1 - |x| / L)) volume 0 L
    have hcont : Continuous (fun x : ℝ => Real.exp (beta * x) * (1 - |x| / L)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) 0 L
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hleftEq :
      (∫ x : ℝ in -L..0, tiltedTentFullProfile beta L x) =
        ∫ x : ℝ in -L..0, Real.exp (beta * x) * (1 + x / L) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -L ≤ 0)] at hx
    rw [tiltedTentFullProfile, abs_of_nonpos hx.2]
    ring
  have hrightEq :
      (∫ x : ℝ in 0..L, tiltedTentFullProfile beta L x) =
        ∫ x : ℝ in 0..L, Real.exp (beta * x) * (1 - x / L) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hL.le] at hx
    rw [tiltedTentFullProfile, abs_of_nonneg hx.1]
  rw [hleftEq, hrightEq, integral_tiltedTentLeftProfile hbeta hL.ne',
    integral_tiltedTentRightProfile hbeta hL.ne', Real.cosh_eq]
  field_simp [hbeta, hL.ne']
  ring

/-- Continuum two-flank deficit in Suzuki's lag coordinate `t = 2x`. -/
def tiltedTentTwoFlankSurplus (beta L : ℝ) : ℝ :=
  2 * ∫ x : ℝ in -L..L, (1 - tiltedTentFullProfile beta L x)

/-- Universal closed form for the bilateral tilted-tent surplus. -/
theorem tiltedTentTwoFlankSurplus_eq
    {beta L : ℝ} (hbeta : beta ≠ 0) (hL : 0 < L) :
    tiltedTentTwoFlankSurplus beta L =
      4 * L - 4 * (Real.cosh (beta * L) - 1) / (L * beta ^ (2 : ℕ)) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-L) L :=
    intervalIntegrable_const
  have hprofile : IntervalIntegrable (tiltedTentFullProfile beta L) volume (-L) L := by
    change IntervalIntegrable
      (fun x : ℝ => Real.exp (beta * x) * (1 - |x| / L)) volume (-L) L
    have hcont : Continuous (fun x : ℝ => Real.exp (beta * x) * (1 - |x| / L)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) (-L) L
  rw [tiltedTentTwoFlankSurplus, intervalIntegral.integral_sub hconst hprofile,
    intervalIntegral.integral_const, integral_tiltedTentFullProfile hbeta hL]
  simp only [smul_eq_mul, mul_one]
  ring

/-- Exact critical Suzuki value of the continuum two-flank surplus. -/
theorem tiltedTentTwoFlankSurplus_critical_eq :
    tiltedTentTwoFlankSurplus (1 / 2) 2 = 16 - 8 * Real.cosh 1 := by
  rw [tiltedTentTwoFlankSurplus_eq (by norm_num) (by norm_num)]
  norm_num
  ring

/-- Explicit exponential bounds put the critical hyperbolic cosine below `7/4`. -/
theorem cosh_one_lt_seven_div_four : Real.cosh 1 < 7 / 4 := by
  rw [Real.cosh_eq]
  nlinarith [Real.exp_one_lt_d9, Real.exp_neg_one_lt_d9]

/-- Suzuki's complete critical continuum tent has strictly more surplus than a width-two seam. -/
theorem tiltedTentTwoFlankSurplus_critical_gt_two :
    2 < tiltedTentTwoFlankSurplus (1 / 2) 2 := by
  rw [tiltedTentTwoFlankSurplus_critical_eq]
  nlinarith [cosh_one_lt_seven_div_four]

end GaloisForLFunctions.HTGeometry
