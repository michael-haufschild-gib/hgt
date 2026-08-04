import GaloisForLFunctions.RHTower.Sieve.GrowthSubstitution

/-!
# The edge bounds at the balanced parameter

At `K = contourParam x` the logarithm `log K` lies between `t = (log x)^{1/10}` and `t + 1 ≤ 2t`, so
the closed forms of the two edge bounds become explicit polynomials in `t`.  Against the saving
`exp(-c₀ t/8192)` and the damping `exp(-t/2)` these are harmless; the point of writing them out is
that the final comparison is then between a polynomial and an exponential in the single variable
`t`.
-/

namespace RHTower.Sieve

open Real

/-- `log K` is at most `2t` at the balanced parameter. -/
theorem log_contourParam_le_two {x : ℝ} (hx : 1 ≤ Real.log x) :
    Real.log (contourParam x) ≤ 2 * (Real.log x) ^ ((1 : ℝ) / 10) := by
  have hx0 : (0 : ℝ) ≤ Real.log x := by linarith
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx (by norm_num)
  have h := log_contourParam_le hx0
  linarith

/-- The ninth power of `log K`, at the balanced parameter. -/
theorem log_contourParam_pow_le {x : ℝ} (hx : 1 ≤ Real.log x) :
    (Real.log (contourParam x)) ^ 9 ≤ 512 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 := by
  have hL0 : (0 : ℝ) ≤ Real.log (contourParam x) := by
    have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx (by norm_num)
    linarith [le_log_contourParam x]
  have h := log_contourParam_le_two hx
  calc (Real.log (contourParam x)) ^ 9 ≤ (2 * (Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 := by gcongr
    _ = 512 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 := by ring

/-- **The right-edge bound at the balanced parameter**, as an explicit polynomial in `t`. -/
theorem invZetaRightBound_contourParam_le {x : ℝ} (hx : 1 ≤ Real.log x) :
    invZetaRightBound (contourParam x)
      ≤ Real.exp (22 / 4)
          * (1 + 1024 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 / zeroFreeConst) := by
  have hA0 := zeroFreeConst_pos
  have h9 := log_contourParam_pow_le hx
  rw [invZetaRightBound_eq]
  have hstep : 2 * (Real.log (contourParam x)) ^ 9 / zeroFreeConst
      ≤ 1024 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 / zeroFreeConst := by
    rw [div_le_div_iff₀ hA0 hA0]
    nlinarith [hA0, h9]
  have hexp : (0 : ℝ) ≤ Real.exp (22 / 4) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (by linarith) hexp

/-- **The edge bound at the balanced parameter**, as an explicit polynomial in `t`. -/
theorem invZetaEdgeBound_contourParam_le {x : ℝ} (hx : 1 ≤ Real.log x) :
    invZetaEdgeBound (contourParam x)
      ≤ 2 * Real.exp (22 / 4)
          * (1 + 1024 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 / zeroFreeConst)
          * (5 / 2 + 2 * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have hA0 := zeroFreeConst_pos
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx (by norm_num)
  have hL0 : (0 : ℝ) < Real.log (contourParam x) := by linarith [le_log_contourParam x]
  have h9 := log_contourParam_pow_le hx
  have hL2 := log_contourParam_le_two hx
  refine le_trans (invZetaEdgeBound_le_poly hL0) ?_
  have h1 : 1 + 2 * (Real.log (contourParam x)) ^ 9 / zeroFreeConst
      ≤ 1 + 1024 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 / zeroFreeConst := by
    have hstep : 2 * (Real.log (contourParam x)) ^ 9 / zeroFreeConst
        ≤ 1024 * ((Real.log x) ^ ((1 : ℝ) / 10)) ^ 9 / zeroFreeConst := by
      rw [div_le_div_iff₀ hA0 hA0]
      nlinarith [hA0, h9]
    linarith
  have h2 : 5 / 2 + Real.log (contourParam x)
      ≤ 5 / 2 + 2 * (Real.log x) ^ ((1 : ℝ) / 10) := by linarith
  have h1nn : (0 : ℝ) ≤ 1 + 2 * (Real.log (contourParam x)) ^ 9 / zeroFreeConst := by positivity
  have h2nn : (0 : ℝ) ≤ 5 / 2 + Real.log (contourParam x) := by linarith
  have hc : (0 : ℝ) ≤ 2 * Real.exp (22 / 4) := by positivity
  gcongr

end RHTower.Sieve
