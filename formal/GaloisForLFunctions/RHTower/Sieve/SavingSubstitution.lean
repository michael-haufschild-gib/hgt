import GaloisForLFunctions.RHTower.Sieve.ContourParameterChoice
import GaloisForLFunctions.RHTower.Sieve.MoebiusSaving

/-!
# Substituting the balanced parameter

With `K = contourParam x` the left-edge power becomes an explicit decay, and the growth carried by
the right edge becomes an explicit — and smaller — increase.  Both comparisons rest on the size of
the zero-free constant, which is far below `1`: the crude bound `zeroFreeConst ≤ 1` is enough for
the horizontal edges, but the truncation error needs `zeroFreeConst ≤ 1/2` to leave a strictly
negative exponent.
-/

namespace RHTower.Sieve

open Real

/-- The zero-free constant is at most `1/2`.  In fact it is `(e^{-11/2}/128)^(4 : ℕ)`, but the crude
bound is what the comparisons need. -/
theorem zeroFreeConst_le_half : zeroFreeConst ≤ 1 / 2 := by
  rw [zeroFreeConst]
  have hprod : (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have h1 : Real.exp (-22 / 4) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  have h1' : (0 : ℝ) < Real.exp (-22 / 4) := Real.exp_pos _
  have hbase : Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64
      ≤ 1 / 128 := by
    rw [mul_assoc, hprod, div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  have hnn : (0 : ℝ) ≤ Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4)
      * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64 := by positivity
  calc (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)
      ≤ (1 / 128 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hnn hbase 4
    _ ≤ 1 / 2 := by norm_num

/-- **The left-edge power at the balanced parameter.**  Any quantity at least `x` raised to the left
abscissa is at most itself times the explicit saving. -/
theorem rpow_leftAbscissa_le_saving {x y : ℝ} (hx : 1 ≤ Real.log x) (hy0 : 0 < y)
    (hxy : Real.log x ≤ Real.log y) :
    y ^ leftAbscissa (contourParam x)
      ≤ y * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) := by
  have hA0 := zeroFreeConst_pos
  have hL0 : 0 < Real.log (contourParam x) := by
    have h1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) :=
      Real.one_le_rpow hx (by norm_num)
    have h2 := le_log_contourParam x
    linarith
  have hδ0 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) := by positivity
  rw [rpow_leftAbscissa hy0]
  refine mul_le_mul_of_nonneg_left ?_ hy0.le
  refine Real.exp_le_exp.2 ?_
  have hbase := le_saving_exponent hx
  have hmono : zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) * Real.log x
      ≤ zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) * Real.log y :=
    mul_le_mul_of_nonneg_left hxy hδ0.le
  rw [neg_mul]
  linarith

end RHTower.Sieve
