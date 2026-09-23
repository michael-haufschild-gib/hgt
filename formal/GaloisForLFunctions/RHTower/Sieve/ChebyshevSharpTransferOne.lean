import GaloisForLFunctions.RHTower.Sieve.ChebyshevMainTermErrorOne

/-!
# The cost of passing to the sharp Chebyshev sum

Replacing the smoothed sum by `ψ(N)` costs `(H+1)·log(N+H)`.  At the balanced width
`H = N·exp(-√(log N)/240000)` that is of the same order as the contour term: the shift from
`√(log N)` to `√(log(N+H+1))` at most doubles the square root — `N+H+1 ≤ N²` gives
`log Z ≤ 2 log N`, hence `√(log Z) ≤ 2√(log N)` — so the window's saving `exp(-√(log N)/240000)`
survives as `exp(-√(log Z)/480000)`.

The logarithm `log(N+H) ≤ log Z = (√(log Z))²` is the polynomial factor, absorbed later.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The square root of four times a logarithm. -/
theorem sqrt_four_mul_log (x : ℝ) :
    Real.sqrt (4 * Real.log x) = 2 * Real.sqrt (Real.log x) := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- **The shift at most doubles the square root.** -/
theorem sqrt_log_shift_le {N : ℝ} (hN3 : 3 ≤ N) (hlogN : 0 ≤ Real.log N)
    (hHN : chebWidthOne N ≤ N) :
    Real.sqrt (Real.log (N + chebWidthOne N + 1)) ≤ 2 * Real.sqrt (Real.log N) := by
  have hZN2 : N + chebWidthOne N + 1 ≤ N ^ (2 : ℕ) := by nlinarith [hHN, hN3]
  have hlogZ2 : Real.log (N + chebWidthOne N + 1) ≤ 2 * Real.log N := by
    have h1 : Real.log (N + chebWidthOne N + 1) ≤ Real.log (N ^ (2 : ℕ)) :=
      Real.log_le_log (by linarith [chebWidthOne_nonneg (show (0:ℝ) ≤ N by linarith)]) hZN2
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  calc Real.sqrt (Real.log (N + chebWidthOne N + 1))
      ≤ Real.sqrt (4 * Real.log N) := Real.sqrt_le_sqrt (by linarith)
    _ = 2 * Real.sqrt (Real.log N) := sqrt_four_mul_log N

/-- **The cost of the sharp transfer, against the contour's shape.** -/
theorem cheb_sharp_transfer_cost_le {N : ℝ} (hN3 : 3 ≤ N) (hlogN : 16 ≤ Real.log N) :
    (chebWidthOne N + 1) * Real.log (N + chebWidthOne N)
      ≤ 2 * (Real.sqrt (Real.log (N + chebWidthOne N + 1)) ^ (2 : ℕ)
          * ((N + chebWidthOne N + 1)
              * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) ≤ chebWidthOne N := chebWidthOne_nonneg hN0.le
  have hHN : chebWidthOne N ≤ N := chebWidthOne_le hN0.le
  have hZ0 : (0 : ℝ) < N + chebWidthOne N + 1 := by linarith
  have hlogZ : (16 : ℝ) ≤ Real.log (N + chebWidthOne N + 1) :=
    le_trans hlogN (Real.log_le_log hN0 (by linarith))
  have hsq : Real.log (N + chebWidthOne N + 1)
      = Real.sqrt (Real.log (N + chebWidthOne N + 1)) ^ (2 : ℕ) :=
    (Real.sq_sqrt (by linarith)).symm
  have hs4 : (4 : ℝ) ≤ Real.sqrt (Real.log (N + chebWidthOne N + 1)) := four_le_sqrt_log hlogZ
  -- the window is below the shape
  have hhalf := sqrt_log_shift_le hN3 (by linarith) hHN
  have hexpcmp : Real.exp (-(Real.sqrt (Real.log N) / 240000))
      ≤ Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hHle : chebWidthOne N
      ≤ (N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by
    have hHeq : chebWidthOne N = N * Real.exp (-(Real.sqrt (Real.log N) / 240000)) :=
      chebWidthOne_eq N
    have h1 : N * Real.exp (-(Real.sqrt (Real.log N) / 240000))
        ≤ N * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
      mul_le_mul_of_nonneg_left hexpcmp hN0.le
    have h2 : N * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))
        ≤ (N + chebWidthOne N + 1)
            * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith [hHeq, h1, h2]
  -- one is below the shape too
  have hone : (1 : ℝ) ≤ (N + chebWidthOne N + 1)
      * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log (N + chebWidthOne N + 1)
            - Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith [hs4, hsq]
      _ = (N + chebWidthOne N + 1)
            * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by
          rw [Real.exp_sub, Real.exp_log hZ0, Real.exp_neg, div_eq_mul_inv]
  -- the logarithm is the polynomial factor
  have hlogle : Real.log (N + chebWidthOne N)
      ≤ Real.sqrt (Real.log (N + chebWidthOne N + 1)) ^ (2 : ℕ) := by
    rw [← hsq]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog0 : (0 : ℝ) ≤ Real.log (N + chebWidthOne N) := Real.log_nonneg (by linarith)
  have hshape0 : (0 : ℝ) ≤ (N + chebWidthOne N + 1)
      * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by linarith
  have hprod := mul_le_mul (by linarith : chebWidthOne N + 1
      ≤ 2 * ((N + chebWidthOne N + 1)
        * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))))
    hlogle hlog0 (by linarith)
  linarith [hprod]

end RHTower.Sieve
