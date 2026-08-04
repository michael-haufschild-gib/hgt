import GaloisForLFunctions.RHTower.Sieve.MoebiusSaving

/-!
# Closed form of the two edge bounds

The edge bounds were produced as reciprocals of exponentials of logarithms.  Both collapse to
products of powers, which is the form in which their growth in `log K` can be read off:

    invZetaRightBound K = e^{22/4}·(1 + 2log⁹K/c₀),
    invZetaEdgeBound  K = 2e^{22/4}·(1 + 2log⁹K/c₀)^{3/4}·(5/2 + log K)^{1/4}.

So the right-edge bound grows like `log⁹K` and the edge bound like `log^{27/4}K·log^{1/4}K = log⁷K`.
-/

namespace RHTower.Sieve

open Real

/-- The reciprocal of the offset, in closed form. -/
theorem one_add_inv_offset (K : ℕ) :
    1 + 1 / (zeroFreeConst / (2 * (Real.log K) ^ 9))
      = 1 + 2 * (Real.log K) ^ 9 / zeroFreeConst := by
  rw [one_div_div]

/-- **The right-edge bound in closed form.** -/
theorem invZetaRightBound_eq (K : ℕ) :
    invZetaRightBound K = Real.exp (22 / 4) * (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) := by
  rw [invZetaRightBound, one_add_inv_offset]

/-- **The edge bound in closed form.**  A product of powers of `log K`. -/
theorem invZetaEdgeBound_eq {K : ℕ} (hlogK : 0 < Real.log K) :
    invZetaEdgeBound K
      = 2 * Real.exp (22 / 4) * (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) ^ ((3 : ℝ) / 4)
          * (5 / 2 + Real.log K) ^ ((1 : ℝ) / 4) := by
  have hA0 := zeroFreeConst_pos
  have hu : (0 : ℝ) < 1 + 2 * (Real.log K) ^ 9 / zeroFreeConst := by positivity
  have hv : (0 : ℝ) < 5 / 2 + Real.log K := by linarith
  rw [invZetaEdgeBound, one_add_inv_offset]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [show -((-22 - 3 * Real.log (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst)
        - Real.log (5 / 2 + Real.log K)) / 4)
      = 22 / 4 + Real.log (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) * ((3 : ℝ) / 4)
        + Real.log (5 / 2 + Real.log K) * ((1 : ℝ) / 4) by ring]
  rw [Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos hu, ← Real.rpow_def_of_pos hv]
  ring

/-!
## A polynomial majorant

For the optimisation only the *order* of the edge bound matters, so the fractional powers may be
discarded: a power `u^θ` with `0 ≤ θ ≤ 1` and `u ≥ 1` is at most `u`.  This replaces `log⁷K` by
`log^{10}K`, which is wasteful and harmless — the competing factor decays faster than any power of
`log K`.
-/

/-- **A polynomial majorant for the edge bound.**  Crude but of the right kind: a polynomial in
`log K`. -/
theorem invZetaEdgeBound_le_poly {K : ℕ} (hlogK : 0 < Real.log K) :
    invZetaEdgeBound K
      ≤ 2 * Real.exp (22 / 4) * (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst)
          * (5 / 2 + Real.log K) := by
  have hA0 := zeroFreeConst_pos
  have hu : (1 : ℝ) ≤ 1 + 2 * (Real.log K) ^ 9 / zeroFreeConst := by
    have : (0 : ℝ) ≤ 2 * (Real.log K) ^ 9 / zeroFreeConst := by positivity
    linarith
  have hv : (1 : ℝ) ≤ 5 / 2 + Real.log K := by linarith
  have hpu : (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) ^ ((3 : ℝ) / 4)
      ≤ 1 + 2 * (Real.log K) ^ 9 / zeroFreeConst := by
    calc (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) ^ ((3 : ℝ) / 4)
        ≤ (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
      _ = 1 + 2 * (Real.log K) ^ 9 / zeroFreeConst := Real.rpow_one _
  have hpv : (5 / 2 + Real.log K) ^ ((1 : ℝ) / 4) ≤ 5 / 2 + Real.log K := by
    calc (5 / 2 + Real.log K) ^ ((1 : ℝ) / 4)
        ≤ (5 / 2 + Real.log K) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
      _ = 5 / 2 + Real.log K := Real.rpow_one _
  rw [invZetaEdgeBound_eq hlogK]
  have hpu0 : (0 : ℝ) ≤ (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) ^ ((3 : ℝ) / 4) := by positivity
  have hpv0 : (0 : ℝ) ≤ (5 / 2 + Real.log K) ^ ((1 : ℝ) / 4) := by positivity
  have hc0 : (0 : ℝ) ≤ 2 * Real.exp (22 / 4) := by positivity
  calc 2 * Real.exp (22 / 4) * (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst) ^ ((3 : ℝ) / 4)
        * (5 / 2 + Real.log K) ^ ((1 : ℝ) / 4)
      ≤ 2 * Real.exp (22 / 4) * (1 + 2 * (Real.log K) ^ 9 / zeroFreeConst)
        * (5 / 2 + Real.log K) := by
        gcongr

end RHTower.Sieve
