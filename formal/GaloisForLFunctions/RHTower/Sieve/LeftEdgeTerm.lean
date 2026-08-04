import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundDiag
import GaloisForLFunctions.RHTower.Sieve.SavingSubstitution

/-!
# The left-edge term at the balanced parameter

The left-edge term of the contour bound has two pieces, `(2N)^{c(K)}` divided by the abscissa and
the tail constant times `(2N+1)^{c(K)}`.  Both are of the same size and both carry the saving, so
the whole term collapses to the trivial size `2N+1` times `exp(-c₀ t/8192)`.

The division by the abscissa costs a factor `2`: `c(K) ≥ 1/2` holds as soon as `log(2N) ≥ 1`,
because `log K ≥ (log 2N)^{1/10} ≥ 1` and `c₀ ≤ 1/2`.
-/

namespace RHTower.Sieve

open Real

/-- The left abscissa is at least `1/2` at the balanced parameter. -/
theorem half_le_leftAbscissa_contourParam {x : ℝ} (hx : 1 ≤ Real.log x) :
    (1 : ℝ) / 2 ≤ leftAbscissa (contourParam x) := by
  have hA0 := zeroFreeConst_pos
  have hA2 := zeroFreeConst_le_half
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx (by norm_num)
  have hL1 : (1 : ℝ) ≤ Real.log (contourParam x) := le_trans ht1 (le_log_contourParam x)
  have hL9 : (1 : ℝ) ≤ (Real.log (contourParam x)) ^ 9 := one_le_pow₀ hL1
  have hquot : zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hA2, hA0, hL9]
  rw [leftAbscissa]
  linarith

/-- **The left-edge term collapses to the trivial size times the saving.** -/
theorem leftEdge_term_le {x C M : ℝ} (hx : 1 ≤ Real.log x) (hx0 : 0 < x)
    (hC : 0 ≤ C) (hM : 0 ≤ M) {y : ℝ} (hy0 : 0 < y) (hxy : Real.log x ≤ Real.log y)
    (hxy' : x ≤ y) :
    M * (2 * (x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x))
        + 2 * (C * y ^ leftAbscissa (contourParam x)))
      ≤ M * ((4 + 2 * C) * y
          * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192))) := by
  set S : ℝ := Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) with hSdef
  have hS0 : (0 : ℝ) < S := Real.exp_pos _
  have hc : (1 : ℝ) / 2 ≤ leftAbscissa (contourParam x) := half_le_leftAbscissa_contourParam hx
  have hcpos : (0 : ℝ) < leftAbscissa (contourParam x) := by linarith
  have hxle : x ^ leftAbscissa (contourParam x) ≤ x * S :=
    rpow_leftAbscissa_le_saving hx hx0 le_rfl
  have hyle : y ^ leftAbscissa (contourParam x) ≤ y * S :=
    rpow_leftAbscissa_le_saving hx hy0 hxy
  have hxpow0 : (0 : ℝ) ≤ x ^ leftAbscissa (contourParam x) :=
    (Real.rpow_pos_of_pos hx0 _).le
  have hyS0 : (0 : ℝ) ≤ y * S := (mul_pos hy0 hS0).le
  have hxy2 : x * S ≤ y * S := mul_le_mul_of_nonneg_right hxy' hS0.le
  have hdiv : x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x)
      ≤ 2 * (y * S) := by
    rw [div_le_iff₀ hcpos]
    have hkey : 0 ≤ (y * S) * (2 * leftAbscissa (contourParam x) - 1) :=
      mul_nonneg hyS0 (by linarith)
    nlinarith [hkey, hxle, hxy2]
  have hCy : C * y ^ leftAbscissa (contourParam x) ≤ C * (y * S) :=
    mul_le_mul_of_nonneg_left hyle hC
  refine mul_le_mul_of_nonneg_left ?_ hM
  nlinarith [hdiv, hCy]

end RHTower.Sieve
