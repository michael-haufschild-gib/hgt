import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneRate

/-!
# The main term's bracket costs nothing

The contour's main term is the cutoff's mass times a bracket that would be `2π` at infinite height.
At the balanced height the discrepancy is the rectangle's aspect ratio,
`2(d-c)/T ≤ (1/2)·(1/T)`, and `1/T = exp(-2√(log Z))` is far below the saving
`exp(-√(log Z)/480000)`.

So replacing the bracket by `2π` costs less than the contour bound itself, and the main term of the
smoothed Chebyshev sum is `2π` times the mass, with the same error `Z·exp(-√(log Z)/480000)`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The bracket may be replaced by `2π`.** -/
theorem cheb_main_term_error_le {N H : ℝ} (hN0 : 0 < N) (hH0 : 0 < H)
    (hZ16 : 16 ≤ Real.log (N + H + 1)) :
    ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖
        * |2 * Real.arctan (chebHeightOne (N + H + 1)
              / (chebRightTwo (chebHeightOne (N + H + 1)) - 1))
            - 2 * Real.arctan (chebHeightOne (N + H + 1)
              / (chebLeftTwo (chebHeightOne (N + H + 1)) - 1))
            - 2 * Real.pi|
      ≤ 2 * ((N + H + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + H + 1)) / 480000))) := by
  have hT0 : (0 : ℝ) < chebHeightOne (N + H + 1) := chebHeightOne_pos _
  have hT8 : (8 : ℝ) ≤ Real.log (chebHeightOne (N + H + 1)) := eight_le_log_chebHeightOne hZ16
  have hs4 : (4 : ℝ) ≤ Real.sqrt (Real.log (N + H + 1)) := four_le_sqrt_log hZ16
  -- the bracket's discrepancy
  have habs := abs_bracket_kappa_one_le hT8 hT0
  -- the width is small
  have hwd : chebRightTwo (chebHeightOne (N + H + 1)) - chebLeftTwo (chebHeightOne (N + H + 1))
      ≤ 1 / 4 := by
    refine le_trans (chebRightTwo_sub_chebLeftTwo_le hT8) ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hwd0 : (0 : ℝ) ≤ chebRightTwo (chebHeightOne (N + H + 1))
      - chebLeftTwo (chebHeightOne (N + H + 1)) :=
    le_of_lt (chebRightTwo_sub_chebLeftTwo_pos hT8)
  -- the height's reciprocal is far below the saving
  have hTinv : 1 / chebHeightOne (N + H + 1)
      ≤ 3 * Real.exp (-(Real.sqrt (Real.log (N + H + 1)) / 480000)) := by
    refine le_trans (one_div_chebHeightOne_le_factor (N + H + 1)) ?_
    rw [chebFactorOne]
    have h := Real.exp_le_exp.mpr
      (by linarith : -(Real.sqrt (Real.log (N + H + 1)) / 80000)
        ≤ -(Real.sqrt (Real.log (N + H + 1)) / 480000))
    linarith [h]
  have hE0 : (0 : ℝ) < Real.exp (-(Real.sqrt (Real.log (N + H + 1)) / 480000)) := Real.exp_pos _
  -- the aspect ratio
  have hratio : 2 * ((chebRightTwo (chebHeightOne (N + H + 1))
        - chebLeftTwo (chebHeightOne (N + H + 1))) / chebHeightOne (N + H + 1))
      ≤ 2 * Real.exp (-(Real.sqrt (Real.log (N + H + 1)) / 480000)) := by
    have hdiv : (chebRightTwo (chebHeightOne (N + H + 1))
          - chebLeftTwo (chebHeightOne (N + H + 1))) / chebHeightOne (N + H + 1)
        = (chebRightTwo (chebHeightOne (N + H + 1))
            - chebLeftTwo (chebHeightOne (N + H + 1))) * (1 / chebHeightOne (N + H + 1)) := by
      ring
    rw [hdiv]
    have hmul := mul_le_mul hwd hTinv (one_div_nonneg.mpr hT0.le) (by norm_num)
    linarith [hmul]
  -- the mass
  have hMm := norm_mellin_smoothWeight_one_le hN0.le hH0
  have hMm0 : (0 : ℝ) ≤ ‖mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖ := norm_nonneg _
  have habs0 : (0 : ℝ) ≤ |2 * Real.arctan (chebHeightOne (N + H + 1)
        / (chebRightTwo (chebHeightOne (N + H + 1)) - 1))
      - 2 * Real.arctan (chebHeightOne (N + H + 1)
        / (chebLeftTwo (chebHeightOne (N + H + 1)) - 1))
      - 2 * Real.pi| := abs_nonneg _
  have hZ0 : (0 : ℝ) ≤ N + H + 1 := by linarith
  have hstep := mul_le_mul (le_trans hMm (by linarith)) (le_trans habs hratio) habs0 hZ0
  linarith [hstep]

end RHTower.Sieve
