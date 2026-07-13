import GaloisForLFunctions.RHTower.XiEndpointCompletedValue
import GaloisForLFunctions.RHTower.XiEndpointQuantitativeNormBudget
import GaloisForLFunctions.RHTower.XiZerosInfinite
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Unconditional completed-value bound for the Xi endpoint budget

The functional equation reflects Mathlib's exact Laurent constant for
`completedRiemannZeta₀` at `1` to the endpoint `0`.  Consequently the completed
Xi endpoint curvature is the explicit source constant

`2 + gamma - log (4 * pi)`.

The elementary bounds `gamma < 2/3`, `exp 1 < 2.72`, and `3 < pi` give the strict
estimate `xiEndpointCompletedCurvature < 1/2`.  This removes the scalar
`xiEndpointCompletedCurvature < 1` hypothesis from the endpoint norm-budget
theorems and yields an unconditional `3/2` Hermitian-mass budget.  No Xi
zero location or RH-equivalent positivity input is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- The exact pole-subtracted completed-zeta value at zero.  This is the value
at one transported by the completed functional equation. -/
theorem completedRiemannZeta₀_zero_eq_eulerMascheroni_log :
    completedRiemannZeta₀ 0 =
      ((Real.eulerMascheroniConstant : ℂ) -
          Complex.log (4 * (Real.pi : ℂ))) / 2 + 1 := by
  rw [← completedRiemannZeta₀_one_sub (0 : ℂ)]
  norm_num [completedRiemannZeta₀_one]

/-- Real form of the exact completed value. -/
theorem completedRiemannZeta₀_zero_re_eq_eulerMascheroni_log :
    (completedRiemannZeta₀ 0).re =
      (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
  rw [completedRiemannZeta₀_zero_eq_eulerMascheroni_log]
  rw [show (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_log (by positivity : 0 ≤ 4 * Real.pi)]
  norm_num

/-- A rational lower bound on the logarithmic term.  The proof factors
`exp (13/6)` as `exp 2 * exp (1/6)`, bounds the first factor by `8` and the
second by `6/5`, and uses `3 < pi`. -/
lemma thirteen_div_six_lt_log_four_mul_pi :
    13 / 6 < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have hexpTwo : Real.exp 2 < 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h : Real.exp 1 < (2.72 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    nlinarith [Real.exp_pos 1]
  have hexpSixth : Real.exp (1 / 6 : ℝ) ≤ 6 / 5 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (x := (1 / 6 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [show (13 / 6 : ℝ) = 2 + 1 / 6 by norm_num, Real.exp_add]
  calc
    Real.exp 2 * Real.exp (1 / 6) < 8 * Real.exp (1 / 6) :=
      mul_lt_mul_of_pos_right hexpTwo (Real.exp_pos _)
    _ ≤ 8 * (6 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpSixth (by norm_num)
    _ < 4 * Real.pi := by nlinarith [Real.pi_gt_three]

/-- The completed endpoint value lies below `1/4`. -/
theorem completedRiemannZeta₀_zero_re_lt_one_fourth :
    (completedRiemannZeta₀ 0).re < 1 / 4 := by
  rw [completedRiemannZeta₀_zero_re_eq_eulerMascheroni_log]
  nlinarith [Real.eulerMascheroniConstant_lt_two_thirds,
    thirteen_div_six_lt_log_four_mul_pi]

/-- Exact source-value formula for the Xi endpoint curvature. -/
theorem xiEndpointCompletedCurvature_eq_eulerMascheroni_log :
    xiEndpointCompletedCurvature =
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  rw [xiEndpointCompletedCurvature_eq_completedRiemannZeta0,
    completedRiemannZeta₀_zero_re_eq_eulerMascheroni_log]
  ring

/-- The endpoint curvature has an unconditional rational upper bound. -/
theorem xiEndpointCompletedCurvature_lt_one_half :
    xiEndpointCompletedCurvature < 1 / 2 := by
  rw [xiEndpointCompletedCurvature_eq_completedRiemannZeta0]
  nlinarith [completedRiemannZeta₀_zero_re_lt_one_fourth]

/-- The endpoint curvature is strictly positive.  This is proved from the internally established
infinite Xi divisor: one zero contributes a strictly positive cross term, and that term is bounded
above by the total endpoint curvature. -/
theorem xiEndpointCompletedCurvature_pos :
    0 < xiEndpointCompletedCurvature := by
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let rho : XiDivisorSupport := ⟨z, hz⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    exact ⟨rho, ⟨0, hn⟩⟩
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have hupper := endpoint_cross_term_re_le_curvature q
  exact (show 0 < 1 / ((q.1 : ℂ).im ^ 2 + 1) by positivity).trans_le
    (hlower.trans hupper)

/-- The scalar source hypothesis required by the source-only endpoint budget is
unconditional. -/
theorem xiEndpointCompletedCurvature_lt_one :
    xiEndpointCompletedCurvature < 1 :=
  xiEndpointCompletedCurvature_lt_one_half.trans (by norm_num)

/-- Unconditional defect-energy estimate in the exact source factor. -/
theorem xiEndpointDefectEnergy_le_unconditional_source_factor :
    xiEndpointReflectionDefectEnergy ≤
      (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
        xiEndpointCompletedCurvature :=
  xiEndpointDefectEnergy_le_source_factor xiEndpointCompletedCurvature_lt_one

/-- The exact source-only multiplier in the endpoint defect estimate is strictly smaller than
one. -/
theorem xiEndpointSourceDefectFactor_lt_one :
    xiEndpointCompletedCurvature /
        (1 - xiEndpointCompletedCurvature) < 1 := by
  have hC := xiEndpointCompletedCurvature_lt_one_half
  rw [div_lt_one (sub_pos.mpr (hC.trans (by norm_num)))]
  linarith

/-- Unconditional Hermitian-mass estimate in the exact source-only factor. -/
theorem xiRawMass_le_unconditional_source_only_factor :
    xiRawReciprocalHermitianMass ≤
      ((2 - xiEndpointCompletedCurvature) /
        (2 * (1 - xiEndpointCompletedCurvature))) *
        xiEndpointCompletedCurvature :=
  xiRawMass_le_source_only_factor xiEndpointCompletedCurvature_lt_one

/-- The exact source factor is at most one, so the reflection-defect energy is
bounded by the endpoint curvature itself. -/
theorem xiEndpointReflectionDefectEnergy_le_endpointCurvature :
    xiEndpointReflectionDefectEnergy ≤ xiEndpointCompletedCurvature := by
  have hden : 0 < 1 - xiEndpointCompletedCurvature :=
    sub_pos.mpr xiEndpointCompletedCurvature_lt_one
  have hratio :
      xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature) ≤ 1 := by
    rw [div_le_iff₀ hden]
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  exact xiEndpointDefectEnergy_le_unconditional_source_factor.trans
    (by simpa using
      mul_le_mul_of_nonneg_right hratio xiEndpointCompletedCurvature_nonneg)

/-- **Strict endpoint reflection contraction.**  The completed source controls the total
transverse reflection defect with a multiplier strictly below one. -/
theorem xiEndpointReflectionDefectEnergy_lt_endpointCurvature :
    xiEndpointReflectionDefectEnergy < xiEndpointCompletedCurvature := by
  calc
    xiEndpointReflectionDefectEnergy ≤
        (xiEndpointCompletedCurvature /
          (1 - xiEndpointCompletedCurvature)) *
            xiEndpointCompletedCurvature :=
      xiEndpointDefectEnergy_le_unconditional_source_factor
    _ < xiEndpointCompletedCurvature := by
      nlinarith [xiEndpointSourceDefectFactor_lt_one,
        xiEndpointCompletedCurvature_pos]

/-- Unconditional `3/2` endpoint norm budget.  The sharp coefficient `1` is
equivalent to RH; the value relation removes the first half of the excess. -/
theorem xiRawReciprocalHermitianMass_le_three_halves_mul_endpointCurvature :
    xiRawReciprocalHermitianMass ≤
      (3 / 2) * xiEndpointCompletedCurvature := by
  have hid := xiEndpointReflectionDefectEnergy_eq_mass_sub_source
  have hdef := xiEndpointReflectionDefectEnergy_le_endpointCurvature
  nlinarith

end

end RHTower
