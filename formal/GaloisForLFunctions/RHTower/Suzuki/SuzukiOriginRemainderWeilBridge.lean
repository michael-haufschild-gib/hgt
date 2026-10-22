import GaloisForLFunctions.RHTower.Suzuki.SuzukiOriginRemainderFirstJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilRemainderRegularity

/-!
# Bridge between Suzuki's two source remainder normalizations

The 2026 origin expansion and the existing restricted-Weil formula use algebraically different
expressions for the same smooth archimedean curvature. This module proves their exact equality on
the positive lag axis, so the removable origin value and first-jet results apply to the actual
localized Weil kernel.
-/

namespace GaloisForLFunctions.RHTower

theorem suzukiWeilRemainderSecondDerivative_eq_originCurvature {t : ℝ} (ht : 0 < t) :
    RHTower.suzukiWeilRemainderSecondDerivative t =
      suzukiOriginRemainderCurvature t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hsinh : Real.sinh t ≠ 0 := (Real.sinh_ne_zero).2 ht0
  have hden : 1 - Real.exp (-(2 * t)) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos ht).ne'
  have hden' : 1 - Real.exp (-(t * 2)) ≠ 0 := by
    convert hden using 1 <;> ring
  have hdiff : Real.exp t - Real.exp (-t) ≠ 0 := by
    intro h
    apply hsinh
    rw [Real.sinh_eq, h]
    norm_num
  have htail :
      Real.exp (t / 2) / (2 * Real.sinh t) =
        Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t))) := by
    rw [Real.sinh_eq]
    field_simp [hden', hdiff]
    rw [mul_sub, mul_one, sub_mul,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring
  have hshift :
      -Real.exp (-(t / 2)) +
          Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t))) =
        Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t))) := by
    field_simp [hden']
    rw [show -(1 - Real.exp (-(t * 2))) + 1 = Real.exp (-(t * 2)) by ring,
      ← Real.exp_add]
    congr 1
    ring
  rw [RHTower.suzukiWeilRemainderSecondDerivative,
    suzukiOriginRemainderCurvature_of_ne ht.ne', abs_of_pos ht,
    screwRegularKernel, Real.cosh_eq, htail]
  linarith

/-- The two source normalizations define the same continuous even remainder kernel on the whole
line, including the removable value `-7/4` at the origin. -/
theorem suzukiWeilRemainderKernel_eq_originCurvature (t : ℝ) :
    RHTower.suzukiWeilRemainderKernel t = suzukiOriginRemainderCurvature t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [RHTower.suzukiWeilRemainderKernel,
      RHTower.suzukiWeilRemainderSecondDerivativeContinuous]
  · calc
      RHTower.suzukiWeilRemainderKernel t =
          RHTower.suzukiWeilRemainderSecondDerivative |t| :=
        RHTower.suzukiWeilRemainderKernel_eq_source_of_ne ht
      _ = suzukiOriginRemainderCurvature |t| :=
        suzukiWeilRemainderSecondDerivative_eq_originCurvature (abs_pos.mpr ht)
      _ = suzukiOriginRemainderCurvature t := by
        rw [suzukiOriginRemainderCurvature_of_ne (abs_ne_zero.mpr ht),
          suzukiOriginRemainderCurvature_of_ne ht]
        simp only [abs_abs]

end GaloisForLFunctions.RHTower
