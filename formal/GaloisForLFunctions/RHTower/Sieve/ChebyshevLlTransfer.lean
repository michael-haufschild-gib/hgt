import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpSelfRateOne
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlRate

/-!
# The two corrections between the contour and `ψ`

Passing from the contour's conclusion to a Chebyshev estimate costs two things: the main term's
bracket is not exactly `2π`, and the smoothed sum is not exactly `ψ`.  Both are of the contour's
own order at the Littlewood balance.

The bracket costs the rectangle's aspect ratio `2(d-c)/T`, and `1/T = exp(-√(c·log Z·log log Z))`
is far below the saving.  The smoothing costs `(H+1)·log(N+H)`, and at the balanced width
`H = N·exp(-√(c·log N·log log N)/12)` this is the saving at half the rate times the polynomial
`log Z`: the shift from `N` to `Z = N + H + 1` at most doubles `√(c·log·log log)`, since
`log Z ≤ 2 log N` and `log log Z ≤ 2 log log N`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The balanced quantity's square root never exceeds the logarithm. -/
theorem sqrt_chebQuadLl_le_log {c N : ℝ} (hc : c ≤ 1) (hN1 : 1 ≤ Real.log N) :
    Real.sqrt (chebQuadLl c N) ≤ Real.log N := by
  have h := chebSavingLl_le_half_log (c := c) hc hN1
  rw [chebSavingLl] at h
  linarith

/-- The smoothing width in exponential form. -/
theorem chebWidthLl_eq (c N : ℝ) :
    chebWidthLl c N = N * Real.exp (-(Real.sqrt (chebQuadLl c N) / 12)) := by
  rw [chebWidthLl, chebRatioLl, chebSavingLl, Real.exp_neg, div_eq_mul_inv]
  congr 3
  ring

/-- **The shift at most doubles the balanced quantity's square root.** -/
theorem sqrt_quad_shift_le {c N : ℝ} (hc0 : 0 ≤ c) (hN3 : 3 ≤ N) (hlogN : 2 ≤ Real.log N) :
    Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) ≤ 2 * Real.sqrt (chebQuadLl c N) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) ≤ chebWidthLl c N := chebWidthLl_nonneg hN0.le
  have hHN : chebWidthLl c N ≤ N := chebWidthLl_le hN0.le
  have hZN2 : N + chebWidthLl c N + 1 ≤ N ^ 2 := by nlinarith [hHN, hN3]
  have hZ0 : (0 : ℝ) < N + chebWidthLl c N + 1 := by linarith
  have hlogZ2 : Real.log (N + chebWidthLl c N + 1) ≤ 2 * Real.log N := by
    have h1 : Real.log (N + chebWidthLl c N + 1) ≤ Real.log (N ^ 2) :=
      Real.log_le_log hZ0 hZN2
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogZ : Real.log N ≤ Real.log (N + chebWidthLl c N + 1) :=
    Real.log_le_log hN0 (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (Real.log N) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLLZ : Real.log (Real.log (N + chebWidthLl c N + 1)) ≤ 2 * Real.log (Real.log N) := by
    have h1 : Real.log (Real.log (N + chebWidthLl c N + 1)) ≤ Real.log (2 * Real.log N) :=
      Real.log_le_log (by linarith) hlogZ2
    rw [Real.log_mul (by norm_num) (by linarith : Real.log N ≠ 0)] at h1
    linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log N) := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hQ : chebQuadLl c (N + chebWidthLl c N + 1) ≤ 4 * chebQuadLl c N := by
    rw [chebQuadLl, chebQuadLl]
    have hprod : Real.log (N + chebWidthLl c N + 1)
          * Real.log (Real.log (N + chebWidthLl c N + 1))
        ≤ (2 * Real.log N) * (2 * Real.log (Real.log N)) := by
      have hLLZ0 : (0 : ℝ) ≤ Real.log (Real.log (N + chebWidthLl c N + 1)) :=
        Real.log_nonneg (by linarith)
      nlinarith [hlogZ2, hLLZ, hLLZ0, hLL0, hlogN]
    nlinarith [hprod, hc0]
  have hroot : Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1))
      ≤ Real.sqrt (4 * chebQuadLl c N) := Real.sqrt_le_sqrt hQ
  have hsplit : Real.sqrt (4 * chebQuadLl c N) = 2 * Real.sqrt (chebQuadLl c N) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  linarith [hroot, hsplit.le, hsplit.ge]

/-- **The smoothing width is below the contour's shape at half the rate.** -/
theorem chebWidthLl_le_shape {c N : ℝ} (hc0 : 0 ≤ c) (hN3 : 3 ≤ N) (hlogN : 2 ≤ Real.log N) :
    chebWidthLl c N
      ≤ (N + chebWidthLl c N + 1)
          * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) ≤ chebWidthLl c N := chebWidthLl_nonneg hN0.le
  have hshift := sqrt_quad_shift_le hc0 hN3 hlogN
  have hexpcmp : Real.exp (-(Real.sqrt (chebQuadLl c N) / 12))
      ≤ Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 : N * Real.exp (-(Real.sqrt (chebQuadLl c N) / 12))
      ≤ N * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) :=
    mul_le_mul_of_nonneg_left hexpcmp hN0.le
  have h2 : N * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24))
      ≤ (N + chebWidthLl c N + 1)
          * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  linarith [chebWidthLl_eq c N, h1, h2]

/-- **The cost of the sharp transfer, against the contour's shape.** -/
theorem cheb_ll_sharp_transfer_cost_le {c N : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1) (hN3 : 3 ≤ N)
    (hlogN : 2 ≤ Real.log N) :
    (chebWidthLl c N + 1) * Real.log (N + chebWidthLl c N)
      ≤ 2 * (Real.log (N + chebWidthLl c N + 1)
          * ((N + chebWidthLl c N + 1)
              * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) ≤ chebWidthLl c N := chebWidthLl_nonneg hN0.le
  have hZ0 : (0 : ℝ) < N + chebWidthLl c N + 1 := by linarith
  have hlogZ : Real.log N ≤ Real.log (N + chebWidthLl c N + 1) :=
    Real.log_le_log hN0 (by linarith)
  have hlogZ2 : (2 : ℝ) ≤ Real.log (N + chebWidthLl c N + 1) := by linarith
  have hHle := chebWidthLl_le_shape hc0 hN3 hlogN
  -- one is below the shape too
  have hsq := sqrt_chebQuadLl_le_log (c := c)
    (N := N + chebWidthLl c N + 1) hc (by linarith)
  have hone : (1 : ℝ) ≤ (N + chebWidthLl c N + 1)
      * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log (N + chebWidthLl c N + 1)
            - Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = (N + chebWidthLl c N + 1)
            * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) := by
          rw [Real.exp_sub, Real.exp_log hZ0, Real.exp_neg, div_eq_mul_inv]
  have hlogle : Real.log (N + chebWidthLl c N)
      ≤ Real.log (N + chebWidthLl c N + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : (0 : ℝ) ≤ Real.log (N + chebWidthLl c N) := Real.log_nonneg (by linarith)
  have hshape0 : (0 : ℝ) ≤ (N + chebWidthLl c N + 1)
      * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24)) := by linarith
  have hprod := mul_le_mul (by linarith : chebWidthLl c N + 1
      ≤ 2 * ((N + chebWidthLl c N + 1)
        * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 24))))
    hlogle hlog0 (by linarith)
  linarith [hprod]

/-- **The bracket may be replaced by `2π`.** -/
theorem cheb_ll_main_term_error_le {c N H : ℝ} (hc0 : 0 < c) (hchalf : c ≤ 1 / 2)
    (hN0 : 0 < N) (hH0 : 0 < H) (hQ : 256 ≤ chebQuadLl c (N + H + 1)) :
    ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖
        * |2 * Real.arctan (chebHeightLl c (N + H + 1)
              / (chebRightTwo (chebHeightLl c (N + H + 1)) - 1))
            - 2 * Real.arctan (chebHeightLl c (N + H + 1)
              / (chebLeftLl c (chebHeightLl c (N + H + 1)) - 1))
            - 2 * Real.pi|
      ≤ 2 * ((N + H + 1)
          * Real.exp (-(Real.sqrt (chebQuadLl c (N + H + 1)) / 24))) := by
  have hT0 : (0 : ℝ) < chebHeightLl c (N + H + 1) := chebHeightLl_pos _ _
  have hT16 : (16 : ℝ) ≤ Real.log (chebHeightLl c (N + H + 1)) :=
    sixteen_le_log_chebHeightLl hQ
  have hT8 : (8 : ℝ) ≤ Real.log (chebHeightLl c (N + H + 1)) := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (chebQuadLl c (N + H + 1)) := Real.sqrt_nonneg _
  -- the bracket's discrepancy
  have habs := abs_bracket_sub_two_pi_le (chebLeftLl_lt_one hc0 hT8)
    (one_lt_chebRightTwo hT8) hT0
  -- the width is at most a quarter
  have hALg := eight_mul_chebDepthLl_le hc0 hchalf hQ
  rw [chebDepthLl] at hALg
  have hwd : chebRightTwo (chebHeightLl c (N + H + 1))
      - chebLeftLl c (chebHeightLl c (N + H + 1)) ≤ 1 / 4 := by
    rw [chebRightTwo_sub_chebLeftLl, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hwd0 : (0 : ℝ) ≤ chebRightTwo (chebHeightLl c (N + H + 1))
      - chebLeftLl c (chebHeightLl c (N + H + 1)) :=
    le_of_lt (chebRightTwo_sub_chebLeftLl_pos hc0 hT8)
  -- the height's reciprocal is far below the saving
  have hTinv : 1 / chebHeightLl c (N + H + 1)
      ≤ 3 * Real.exp (-(Real.sqrt (chebQuadLl c (N + H + 1)) / 24)) := by
    refine le_trans (one_div_chebHeightLl_le_factor c (N + H + 1)) ?_
    rw [chebFactorLl, chebSavingLl]
    have h := Real.exp_le_exp.mpr
      (by linarith : -(Real.sqrt (chebQuadLl c (N + H + 1)) / 2)
        ≤ -(Real.sqrt (chebQuadLl c (N + H + 1)) / 24))
    linarith [h]
  have hE0 : (0 : ℝ) < Real.exp (-(Real.sqrt (chebQuadLl c (N + H + 1)) / 24)) := Real.exp_pos _
  -- the aspect ratio
  have hratio : 2 * ((chebRightTwo (chebHeightLl c (N + H + 1))
        - chebLeftLl c (chebHeightLl c (N + H + 1))) / chebHeightLl c (N + H + 1))
      ≤ 2 * Real.exp (-(Real.sqrt (chebQuadLl c (N + H + 1)) / 24)) := by
    have hdiv : (chebRightTwo (chebHeightLl c (N + H + 1))
          - chebLeftLl c (chebHeightLl c (N + H + 1))) / chebHeightLl c (N + H + 1)
        = (chebRightTwo (chebHeightLl c (N + H + 1))
            - chebLeftLl c (chebHeightLl c (N + H + 1)))
          * (1 / chebHeightLl c (N + H + 1)) := by ring
    rw [hdiv]
    have hmul := mul_le_mul hwd hTinv (one_div_nonneg.mpr hT0.le) (by norm_num)
    linarith [hmul]
  -- the mass
  have hMm := norm_mellin_smoothWeight_one_le hN0.le hH0
  have hMm0 : (0 : ℝ) ≤ ‖mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖ := norm_nonneg _
  have habs0 : (0 : ℝ) ≤ |2 * Real.arctan (chebHeightLl c (N + H + 1)
        / (chebRightTwo (chebHeightLl c (N + H + 1)) - 1))
      - 2 * Real.arctan (chebHeightLl c (N + H + 1)
        / (chebLeftLl c (chebHeightLl c (N + H + 1)) - 1))
      - 2 * Real.pi| := abs_nonneg _
  have hZ0 : (0 : ℝ) ≤ N + H + 1 := by linarith
  have hstep := mul_le_mul (le_trans hMm (by linarith)) (le_trans habs hratio) habs0 hZ0
  linarith [hstep]

end RHTower.Sieve
