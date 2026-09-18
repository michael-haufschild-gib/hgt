import GaloisForLFunctions.RHTower.EisensteinTruncatedRowSum
import GaloisForLFunctions.RHTower.EisensteinLineModelBounds

/-!
# A majorant for the real truncated row sum on the fundamental domain

For a real parameter `a > 1/2`, `Y ≥ 1` and `z ∈ 𝒟`, the real truncated row sum
`R_a(z) = Σ_v [Im(γ_v z) ≤ Y] Im(γ_v z)^{½+a}` is, by the truncation identity at the real
parameter, `2 ‖Λ^Y E_a(z) + B(a) [y>Y] y^{½−a}‖ / ‖A(a)‖`.  Hence it is bounded by a constant for
`y ≤ Y`, and by `rowDecayConst a · y^{½−a}` for `y > Y` (the tail `e^{−2πy}` is absorbed by a power
through `x^k / k! ≤ e^x`).  These are the bounds that make the unfolded integrand integrable.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open scoped MatrixGroups

namespace RHTower

noncomputable section

theorem half_lt_im_of_mem_fd' {z : ℍ} (hz : z ∈ fd) : 1 / 2 < z.im := by
  have h1 := hz.1
  rw [Complex.normSq_apply] at h1
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1
  have h2 := hz.2
  rw [abs_le] at h2
  nlinarith [z.im_pos, h2.1, h2.2]

/-! ## The real truncated row sum -/

/-- The real truncated row sum `Σ_v [Im(γ_v z) ≤ Y] Im(γ_v z)^a`. -/
def realTruncatedRowSum (a Y : ℝ) (z : ℍ) : ℝ :=
  ∑' w : gammaSet 1 1 0, (if rowHeight w z ≤ Y then rowHeight w z ^ a else 0)

theorem realTruncated_term_nonneg (a Y : ℝ) (z : ℍ) (w : gammaSet 1 1 0) :
    0 ≤ (if rowHeight w z ≤ Y then rowHeight w z ^ a else 0) := by
  split_ifs
  · exact Real.rpow_nonneg (rowHeight_pos w z).le a
  · exact le_rfl

theorem realTruncatedRowSum_nonneg (a Y : ℝ) (z : ℍ) : 0 ≤ realTruncatedRowSum a Y z :=
  tsum_nonneg (realTruncated_term_nonneg a Y z)

theorem summable_realTruncated_term {a : ℝ} (ha : 1 < a) (Y : ℝ) (z : ℍ) :
    Summable (fun w : gammaSet 1 1 0 => if rowHeight w z ≤ Y then rowHeight w z ^ a else 0) := by
  have h := (summable_rowHeight_cpow (s := (a : ℂ)) (by simpa using ha) z).norm
  refine Summable.of_nonneg_of_le (realTruncated_term_nonneg a Y z) (fun w => ?_) h
  split_ifs
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (rowHeight_pos w z), Complex.ofReal_re]
  · positivity

theorem truncatedRowSum_ofReal (a Y : ℝ) (z : ℍ) :
    truncatedRowSum (a : ℂ) Y z = ((realTruncatedRowSum a Y z : ℝ) : ℂ) := by
  unfold truncatedRowSum realTruncatedRowSum
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun w => ?_
  split_ifs
  · exact (Complex.ofReal_cpow (rowHeight_pos w z).le a).symm
  · simp

theorem norm_truncatedRowSum_ofReal (a Y : ℝ) (z : ℍ) :
    ‖truncatedRowSum (a : ℂ) Y z‖ = realTruncatedRowSum a Y z := by
  rw [truncatedRowSum_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realTruncatedRowSum_nonneg a Y z)]

/-! ## Bounds on the truncated line model at a real parameter -/

theorem msA_ofReal_ne_zero {a : ℝ} (ha : 1 / 2 < a) : msA (a : ℂ) ≠ 0 := by
  unfold msA reflectedCompletedLambda
  apply mul_ne_zero
  · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

/-- The bound of the line model on `𝒟 ∩ {y ≤ Y}` at a real parameter. -/
def rowBoundedConst (a Y : ℝ) : ℝ :=
  ‖msB (a : ℂ)‖ * (1 / 2 : ℝ) ^ (1 / 2 - a) + ‖msA (a : ℂ)‖ * Y ^ (1 / 2 + a) + tailConst (a : ℂ)

theorem rowBoundedConst_nonneg (a : ℝ) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ rowBoundedConst a Y := by
  unfold rowBoundedConst
  have h1 := tailConst_nonneg (a : ℂ)
  have h2 : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 - a) := Real.rpow_nonneg (by norm_num) _
  have h3 : 0 ≤ Y ^ (1 / 2 + a) := Real.rpow_nonneg hY _
  have h4 := norm_nonneg (msB (a : ℂ))
  have h5 := norm_nonneg (msA (a : ℂ))
  nlinarith [mul_nonneg h4 h2, mul_nonneg h5 h3]

theorem norm_truncatedLineModel_le_of_le {a Y : ℝ} (ha : 1 / 2 < a) {z : ℍ} (hz : z ∈ fd)
    (hzY : z.im ≤ Y) :
    ‖truncatedLineModel (a : ℂ) Y z‖ ≤ rowBoundedConst a Y := by
  unfold truncatedLineModel
  rw [if_neg (not_lt.mpr hzY), sub_zero]
  have hy := half_lt_im_of_mem_fd' hz
  refine (norm_eisensteinLineModel_le (a : ℂ) hy.le).trans ?_
  rw [Complex.ofReal_re]
  unfold rowBoundedConst
  have h1 : z.im ^ (1 / 2 - a) ≤ (1 / 2 : ℝ) ^ (1 / 2 - a) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hy.le (by linarith)
  have h2 : z.im ^ (1 / 2 + a) ≤ Y ^ (1 / 2 + a) :=
    Real.rpow_le_rpow z.im_pos.le hzY (by linarith)
  have h3 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])
  have hT := tailConst_nonneg (a : ℂ)
  have hB := norm_nonneg (msB (a : ℂ))
  have hA := norm_nonneg (msA (a : ℂ))
  nlinarith [mul_le_mul_of_nonneg_left h1 hB, mul_le_mul_of_nonneg_left h2 hA,
    mul_le_mul_of_nonneg_left h3 hT]

theorem norm_truncatedLineModel_le_of_gt {a Y : ℝ} {z : ℍ} (hz : z ∈ fd) (hzY : Y < z.im) :
    ‖truncatedLineModel (a : ℂ) Y z‖ ≤ tailConst (a : ℂ) * Real.exp (-(2 * Real.pi * z.im)) := by
  unfold truncatedLineModel
  rw [if_pos hzY]
  unfold eisensteinLineModel d4BMCompletedEisensteinCuspLeg
  rw [add_sub_cancel_left]
  exact norm_cuspTailPart_le_exp (a : ℂ) z.re (half_lt_im_of_mem_fd' hz).le

/-! ## Absorbing the exponential into a power -/

theorem exp_neg_le_factorial_div_pow {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.exp (-(2 * Real.pi * y)) ≤ (k.factorial : ℝ) / (2 * Real.pi) ^ k * y ^ (-(k : ℝ)) := by
  have h := Real.pow_div_factorial_le_exp (2 * Real.pi * y) (by positivity) k
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpos : 0 < (2 * Real.pi * y) ^ k := by positivity
  have h' : (2 * Real.pi * y) ^ k ≤ Real.exp (2 * Real.pi * y) * (k.factorial : ℝ) := by
    rwa [div_le_iff₀ hk] at h
  rw [Real.exp_neg, Real.rpow_neg hy.le, Real.rpow_natCast]
  have hexp : 0 < Real.exp (2 * Real.pi * y) := Real.exp_pos _
  have heq : (k.factorial : ℝ) / (2 * Real.pi) ^ k * (y ^ k)⁻¹ =
      (k.factorial : ℝ) / (2 * Real.pi * y) ^ k := by
    rw [mul_pow]; field_simp; ring
  rw [heq, inv_le_iff_one_le_mul₀' hexp, ← mul_div_assoc, le_div_iff₀ hpos, one_mul]
  exact h'

theorem exp_neg_le_rpow_of_one_le {y a : ℝ} (hy : 1 ≤ y) :
    Real.exp (-(2 * Real.pi * y)) ≤
      ((⌈a⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈a⌉₊) * y ^ (1 / 2 - a) := by
  have h := exp_neg_le_factorial_div_pow (by linarith : 0 < y) ⌈a⌉₊
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hy
  have := Nat.le_ceil a
  linarith

/-! ## The majorant -/

/-- The decay constant of the real truncated row sum above height `Y`. -/
def rowDecayConst (a : ℝ) : ℝ :=
  2 * (tailConst (a : ℂ) * ((⌈a⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈a⌉₊) + ‖msB (a : ℂ)‖) /
    ‖msA (a : ℂ)‖

theorem rowDecayConst_nonneg (a : ℝ) : 0 ≤ rowDecayConst a := by
  unfold rowDecayConst
  have := tailConst_nonneg (a : ℂ)
  positivity

/-- The truncation identity solved for the real row sum. -/
theorem realTruncatedRowSum_eq {a Y : ℝ} (ha : 1 / 2 < a) (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    realTruncatedRowSum (1 / 2 + a) Y z =
      2 * ‖truncatedLineModel (a : ℂ) Y z +
        msB (a : ℂ) * (if Y < z.im then (z.im : ℂ) ^ (1 / 2 - (a : ℂ)) else 0)‖ / ‖msA (a : ℂ)‖ := by
  have h := truncatedLineModel_eq_truncatedRowSum (u := (a : ℂ)) (by simpa using ha) hz hY
  have hA := msA_ofReal_ne_zero ha
  have hsum : truncatedRowSum (1 / 2 + (a : ℂ)) Y z =
      ((realTruncatedRowSum (1 / 2 + a) Y z : ℝ) : ℂ) := by
    have := truncatedRowSum_ofReal (1 / 2 + a) Y z
    push_cast at this
    exact this
  have hval : ((realTruncatedRowSum (1 / 2 + a) Y z : ℝ) : ℂ) =
      2 * (truncatedLineModel (a : ℂ) Y z +
        msB (a : ℂ) * (if Y < z.im then (z.im : ℂ) ^ (1 / 2 - (a : ℂ)) else 0)) / msA (a : ℂ) := by
    rw [← hsum]
    rw [eq_div_iff hA]
    linear_combination -2 * h
  have hnn := realTruncatedRowSum_nonneg (1 / 2 + a) Y z
  calc realTruncatedRowSum (1 / 2 + a) Y z
      = ‖((realTruncatedRowSum (1 / 2 + a) Y z : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    _ = _ := by
        rw [hval, norm_div, norm_mul]
        norm_num

/-- **Bounded below height `Y`.** -/
theorem realTruncatedRowSum_le_of_le {a Y : ℝ} (ha : 1 / 2 < a) (hY : 1 ≤ Y) {z : ℍ}
    (hz : z ∈ fd) (hzY : z.im ≤ Y) :
    realTruncatedRowSum (1 / 2 + a) Y z ≤ 2 * rowBoundedConst a Y / ‖msA (a : ℂ)‖ := by
  rw [realTruncatedRowSum_eq ha hY hz, if_neg (not_lt.mpr hzY), mul_zero, add_zero]
  have hA : 0 < ‖msA (a : ℂ)‖ := norm_pos_iff.mpr (msA_ofReal_ne_zero ha)
  apply div_le_div_of_nonneg_right _ hA.le
  have := norm_truncatedLineModel_le_of_le ha hz hzY
  linarith

/-- **Decay above height `Y`.** -/
theorem realTruncatedRowSum_le_of_gt {a Y : ℝ} (ha : 1 / 2 < a) (hY : 1 ≤ Y) {z : ℍ}
    (hz : z ∈ fd) (hzY : Y < z.im) :
    realTruncatedRowSum (1 / 2 + a) Y z ≤ rowDecayConst a * z.im ^ (1 / 2 - a) := by
  rw [realTruncatedRowSum_eq ha hY hz, if_pos hzY]
  have hA : 0 < ‖msA (a : ℂ)‖ := norm_pos_iff.mpr (msA_ofReal_ne_zero ha)
  have hy1 : 1 ≤ z.im := by linarith
  have h1 := norm_truncatedLineModel_le_of_gt (a := a) hz hzY
  have h2 : ‖msB (a : ℂ) * (z.im : ℂ) ^ (1 / 2 - (a : ℂ))‖ = ‖msB (a : ℂ)‖ * z.im ^ (1 / 2 - a) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
    congr 2
    simp
  have h3 := exp_neg_le_rpow_of_one_le (a := a) hy1
  have hT := tailConst_nonneg (a : ℂ)
  have hpow : 0 ≤ z.im ^ (1 / 2 - a) := Real.rpow_nonneg z.im_pos.le _
  unfold rowDecayConst
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hA.le
  calc 2 * ‖truncatedLineModel (a : ℂ) Y z + msB (a : ℂ) * (z.im : ℂ) ^ (1 / 2 - (a : ℂ))‖
      ≤ 2 * (‖truncatedLineModel (a : ℂ) Y z‖ + ‖msB (a : ℂ) * (z.im : ℂ) ^ (1 / 2 - (a : ℂ))‖) := by
        gcongr; exact norm_add_le _ _
    _ ≤ 2 * (tailConst (a : ℂ) * (((⌈a⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈a⌉₊) * z.im ^ (1 / 2 - a)) +
          ‖msB (a : ℂ)‖ * z.im ^ (1 / 2 - a)) := by
        rw [h2]
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h3 hT)
    _ = 2 * (tailConst (a : ℂ) * ((⌈a⌉₊.factorial : ℝ) / (2 * Real.pi) ^ ⌈a⌉₊) + ‖msB (a : ℂ)‖) *
          z.im ^ (1 / 2 - a) := by ring

end

end RHTower
