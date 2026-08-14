import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The binomial resolvent is a first-order perturbation of the identity

For a bounded self-adjoint element `T` and a scale `L` at least `‖T‖`, the continuous functional
calculus of `t ↦ (1 - t/(2L))^{-1/2}` differs from the identity by at most `‖T‖/(2L)`:

`‖(1 - T/(2L))^{-1/2} - 1‖ ≤ ‖T‖ / (2L)`.

The scalar mechanism is exact: with `s = √(1-y)`,

`1/s - 1 = y / (s (1+s))`,  and  `s(1+s) ≥ 1` whenever `|y| ≤ 1/2`.

This is the estimate that puts the prime-normal binomial cross-section within `O(L^{-3/2})` of the
pure half-log corona representative.
-/

open scoped ContinuousFunctionalCalculus

namespace GaloisForLFunctions.HTGeometry

/-- The scalar first-order bound for the inverse square root. -/
theorem abs_inv_sqrt_one_sub_sub_one_le {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |1 / Real.sqrt (1 - y) - 1| ≤ |y| := by
  have hy1 : -(1/2 : ℝ) ≤ y := by
    have := abs_le.mp hy
    linarith [this.1]
  have hy2 : y ≤ 1 / 2 := (abs_le.mp hy).2
  have hpos : (1:ℝ) / 2 ≤ 1 - y := by linarith
  have hspos : 0 < Real.sqrt (1 - y) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt (by linarith)
  have hslow : (1:ℝ) / 2 ≤ Real.sqrt (1 - y) := by
    nlinarith [hsq, hspos, hpos]
  have hprod : (1:ℝ) ≤ Real.sqrt (1 - y) * (1 + Real.sqrt (1 - y)) := by
    nlinarith [hsq, hslow, hspos, hpos]
  have hval : 1 / Real.sqrt (1 - y) - 1
      = y / (Real.sqrt (1 - y) * (1 + Real.sqrt (1 - y))) := by
    field_simp
    nlinarith [hsq]
  rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.sqrt (1 - y)
    * (1 + Real.sqrt (1 - y)))]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg y, hprod]

/-- **The binomial resolvent bound.**  On a scale above the norm, the inverse square root of
`1 - T/(2L)` is within `‖T‖/(2L)` of the identity. -/
theorem norm_cfc_invSqrt_sub_one_le {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] (T : A) {L : ℝ}
    (hL : ‖T‖ ≤ L) (hL0 : 0 < L) :
    ‖cfc (fun t : ℝ => 1 / Real.sqrt (1 - t / (2 * L)) - 1) T‖ ≤ ‖T‖ / (2 * L) := by
  refine norm_cfc_le (by positivity) fun x hx => ?_
  have hxle : ‖x‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hx
  have hxabs : |x| ≤ ‖T‖ := by
    simpa [Real.norm_eq_abs] using hxle
  have hxL : |x / (2 * L)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * L), div_le_div_iff₀ (by positivity)
      (by norm_num)]
    linarith [hxabs, hL]
  have hbound := abs_inv_sqrt_one_sub_sub_one_le hxL
  have habs : |x / (2 * L)| ≤ ‖T‖ / (2 * L) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * L)]
    apply div_le_div_of_nonneg_right hxabs (by positivity)
  simpa [Real.norm_eq_abs] using le_trans hbound habs

end GaloisForLFunctions.HTGeometry
