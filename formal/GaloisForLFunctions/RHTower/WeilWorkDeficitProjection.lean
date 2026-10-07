import GaloisForLFunctions.RHTower.WeilWorkDeficitSquareMoment
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# Critical-line projection of the actual zero Fourier multiplier

Line conjugation cancels the first horizontal variation. The remaining quadratic error is
controlled by the unconditional full-copy square moment, on the linear height scale.
-/

open Complex Set Filter
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

private def projectionCharacter (k : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (((k * (q.1 : ℂ).im : ℝ) : ℂ) * I)

private theorem norm_projectionCharacter (k : ℝ) (q : XiZeroCopy) :
    ‖projectionCharacter k q‖ = 1 := by
  simp [projectionCharacter, Complex.norm_exp]

private theorem projection_lineConj_re (q : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
  rw [xiZero_lineConj_eq]
  simp

private theorem projection_lineConj_im (q : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).im = (q.1 : ℂ).im := by
  rw [xiZero_lineConj_eq]
  simp

private theorem sum_projection_lineConj (T : ℝ) (f : XiZeroCopy → ℂ) :
    (∑ q ∈ (finite_deficitWindow T).toFinset, f (xiZeroCopyLineConjEquiv q)) =
      ∑ q ∈ (finite_deficitWindow T).toFinset, f q := by
  classical
  apply Finset.sum_equiv xiZeroCopyLineConjEquiv
  · intro q
    simp only [Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq,
      projection_lineConj_im]
  · intro q _
    rfl

private theorem paired_multiplier (k : ℝ) (q : XiZeroCopy) :
    (Real.exp (-(2 - (q.1 : ℂ).re) * |k|) : ℂ) * projectionCharacter k q +
      (Real.exp (-(2 - ((xiZeroCopyLineConjEquiv q).1 : ℂ).re) * |k|) : ℂ) *
        projectionCharacter k (xiZeroCopyLineConjEquiv q) =
    2 * (Real.exp (-(3 / 2) * |k|) : ℂ) *
      (Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) : ℂ) * projectionCharacter k q := by
  have hc : projectionCharacter k (xiZeroCopyLineConjEquiv q) = projectionCharacter k q := by
    simp only [projectionCharacter, projection_lineConj_im]
  rw [projection_lineConj_re, hc, Real.cosh_eq]
  have h1 : -(2 - (q.1 : ℂ).re) * |k| =
      -(3 / 2) * |k| + ((q.1 : ℂ).re - 1 / 2) * |k| := by ring
  have h2 : -(2 - (1 - (q.1 : ℂ).re)) * |k| =
      -(3 / 2) * |k| + -(((q.1 : ℂ).re - 1 / 2) * |k|) := by ring
  rw [h1, h2, Real.exp_add, Real.exp_add]
  push_cast
  ring

private theorem cosh_copy_sub_one_le (k : ℝ) (q : XiZeroCopy) :
    |Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) - 1| ≤
      (k ^ 2 / 2 * Real.cosh (|k| / 2)) * ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hδ : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : abs (((q.1 : ℂ).re - 1 / 2) * |k|) ≤ |k| / 2 := by
    rw [abs_mul, abs_abs]
    nlinarith [abs_nonneg k]
  have hc : Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) ≤ Real.cosh (|k| / 2) := by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg (by positivity : 0 ≤ |k| / 2)]
  have hs := HTGeometry.cosh_sub_one_le (abs_nonneg (((q.1 : ℂ).re - 1 / 2) * |k|))
  rw [Real.cosh_abs, sq_abs] at hs
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))]
  calc
    _ ≤ (((q.1 : ℂ).re - 1 / 2) * |k|) ^ 2 / 2 *
        Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) := hs
    _ ≤ (((q.1 : ℂ).re - 1 / 2) * |k|) ^ 2 / 2 * Real.cosh (|k| / 2) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [mul_pow, sq_abs]; ring

/-- Difference between the true zero multiplier at abscissa two and its critical projection. -/
def deficitZeroProjectionError (k T : ℝ) : ℂ :=
  (∑ q ∈ (finite_deficitWindow T).toFinset,
    (Real.exp (-(2 - (q.1 : ℂ).re) * |k|) : ℂ) *
      Complex.exp (((k * (q.1 : ℂ).im : ℝ) : ℂ) * I)) -
  (Real.exp (-(3 / 2) * |k|) : ℂ) *
    ∑ q ∈ (finite_deficitWindow T).toFinset,
      Complex.exp (((k * (q.1 : ℂ).im : ℝ) : ℂ) * I)

/-- A finite-height bound retaining every multiplicity copy. -/
theorem norm_deficitZeroProjectionError_le (k T : ℝ) :
    ‖deficitZeroProjectionError k T‖ ≤
      Real.exp (-(3 / 2) * |k|) * (k ^ 2 / 2 * Real.cosh (|k| / 2)) *
        deficitSquareCount T := by
  classical
  let F := (finite_deficitWindow T).toFinset
  let a : ℝ := Real.exp (-(3 / 2) * |k|)
  let f : XiZeroCopy → ℂ := fun q =>
    (Real.exp (-(2 - (q.1 : ℂ).re) * |k|) : ℂ) * projectionCharacter k q
  have hpair : (∑ q ∈ F, f q) + (∑ q ∈ F, f q) =
      2 * (a : ℂ) * ∑ q ∈ F,
        (Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) : ℂ) * projectionCharacter k q := by
    conv_lhs => rhs; rw [← sum_projection_lineConj T f]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    simpa only [f, a, mul_assoc] using paired_multiplier k q
  have heq : deficitZeroProjectionError k T = (a : ℂ) * ∑ q ∈ F,
      ((Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) : ℂ) - 1) * projectionCharacter k q := by
    have hsum : (∑ q ∈ F, f q) = (a : ℂ) * ∑ q ∈ F,
        (Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) : ℂ) * projectionCharacter k q := by
      linear_combination (1 / 2 : ℂ) * hpair
    change (∑ q ∈ F, f q) - (a : ℂ) * (∑ q ∈ F, projectionCharacter k q) = _
    rw [hsum, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hnorm : ‖∑ q ∈ F,
      ((Real.cosh (((q.1 : ℂ).re - 1 / 2) * |k|) : ℂ) - 1) * projectionCharacter k q‖ ≤
      (k ^ 2 / 2 * Real.cosh (|k| / 2)) * deficitSquareCount T := by
    apply (norm_sum_le F _).trans
    rw [deficitSquareCount, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    rw [norm_mul, norm_projectionCharacter, mul_one, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact cosh_copy_sub_one_le k q
  exact (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le).trans_eq (by ring)

/-- At each fixed frequency, horizontal projection costs sublinear mass. -/
theorem tendsto_norm_deficitZeroProjectionError_div (k : ℝ) :
    Tendsto (fun T : ℝ => ‖deficitZeroProjectionError k T‖ / T) atTop (𝓝 0) := by
  have h := tendsto_deficitSquareCount_div.const_mul
    (Real.exp (-(3 / 2) * |k|) * (k ^ 2 / 2 * Real.cosh (|k| / 2)))
  rw [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact div_nonneg (norm_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (norm_deficitZeroProjectionError_le k T) (show 0 ≤ T by linarith)

theorem tendsto_deficitZeroProjectionError_div (k : ℝ) :
    Tendsto (fun T : ℝ => deficitZeroProjectionError k T / (T : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_norm_deficitZeroProjectionError_div k).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < T)]

end RHTower.WeilSpectral
end
