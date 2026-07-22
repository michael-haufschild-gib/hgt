import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniSource
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Jensen source law in the shift-one Cassini coordinate

This module applies Jensen's formula directly to the new entire Cassini source.  It identifies its
circle-average excess with the exact finite divisor sum on every positive-radius disc and proves
the excess nonnegative.  Together with `XiSquaredSeamCassiniSource`, no branch, zero-exhaustion,
anchor, or multiplicity assumption remains in the analytic source construction.
-/

open Complex Real MeasureTheory Metric Set

namespace RHTower

noncomputable section

/-- Circle-average Jensen excess of the translated squared-coordinate Xi source. -/
def xiSquaredSeamCassiniJensenExcess (r : ℝ) : ℝ :=
  Real.circleAverage (fun u => Real.log ‖xiSquaredSeamCassiniSource u‖) 0 r -
    Real.log ‖xiSquaredSeamCassiniSource 0‖

/-- Exact finite-radius Jensen law for the Cassini source. -/
theorem xiSquaredSeamCassiniJensenExcess_eq_divisor_finsum
    {r : ℝ} (hr : 0 < r) :
    xiSquaredSeamCassiniJensenExcess r =
      ∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor xiSquaredSeamCassiniSource
          (closedBall 0 r)) u : ℝ) * Real.log (r * ‖u‖⁻¹) := by
  have han : AnalyticOnNhd ℂ xiSquaredSeamCassiniSource (closedBall 0 |r|) :=
    fun u _ => differentiable_xiSquaredSeamCassiniSource.analyticAt u
  have hJ := han.circleAverage_log_norm hr.ne'
    xiSquaredSeamCassiniSource_zero_ne
  rw [abs_of_pos hr] at hJ
  rw [xiSquaredSeamCassiniJensenExcess, hJ]
  simp only [zero_sub, norm_neg, add_sub_cancel_right]

/-- Jensen excess is nonnegative at every positive radius. -/
theorem xiSquaredSeamCassiniJensenExcess_nonneg
    {r : ℝ} (hr : 0 < r) :
    0 ≤ xiSquaredSeamCassiniJensenExcess r := by
  rw [xiSquaredSeamCassiniJensenExcess_eq_divisor_finsum hr]
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall (0 : ℂ) r
  · by_cases hu0 : u = 0
    · subst u
      simp
    · have hdiv :
          (MeromorphicOn.divisor xiSquaredSeamCassiniSource (closedBall 0 r)) u =
            ((analyticOrderAt xiSquaredSeamCassiniSource u).toNat : ℤ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
          (fun z _ => differentiable_xiSquaredSeamCassiniSource.analyticAt z) hu,
          ← ENat.coe_toNat (xiSquaredSeamCassiniSource_order_ne_top u)]
        simp
      refine mul_nonneg ?_ ?_
      · rw [hdiv]
        positivity
      · have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hle : ‖u‖ ≤ r := by
          simpa [mem_closedBall, dist_zero_right] using hu
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, one_le_div hunorm]
        exact hle
  · have hdiv :
        (MeromorphicOn.divisor xiSquaredSeamCassiniSource (closedBall 0 r)) u = 0 := by
      by_contra h
      exact hu ((MeromorphicOn.divisor xiSquaredSeamCassiniSource
        (closedBall 0 r)).supportWithinDomain (Function.mem_support.mpr h))
    rw [hdiv]
    simp

end

end RHTower
