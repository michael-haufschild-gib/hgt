import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileLimit

/-! Every quadratic form has a scalar envelope determined by its diagonal coefficient. -/

open MeasureTheory ProbabilityTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilJointQuadratic (a b d : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  a * z 0 ^ 2 + 2 * b * z 0 * z 1 + d * z 1 ^ 2

theorem continuous_finiteWeilJointQuadratic (a b d : ℝ) :
    Continuous (finiteWeilJointQuadratic a b d) := by
  unfold finiteWeilJointQuadratic
  fun_prop

theorem finiteWeilJointQuadratic_diagonal (a b d x : ℝ) :
    finiteWeilJointQuadratic a b d (finiteWeilDiagonalPoint x) = (a + 2 * b + d) * x ^ 2 := by
  change a * x ^ 2 + 2 * b * x * x + d * x ^ 2 = _
  ring

theorem finiteWeilJointQuadratic_radial (c : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    finiteWeilJointQuadratic c 0 c z = c * ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  unfold finiteWeilJointQuadratic
  ring

theorem finiteWeilJointQuadratic_transverse (c : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    finiteWeilJointQuadratic c (-c) c z = c * (z 0 - z 1) ^ 2 := by
  unfold finiteWeilJointQuadratic
  ring

theorem finiteWeil_quadratic_transverse_envelope (a b d x e : ℝ) {ε : ℝ}
    (hε : 0 < ε) (he : |e| ≤ 2) :
    a * x ^ 2 + 2 * b * x * (x + e) + d * (x + e) ^ 2 ≤
      (a + 2 * b + d + ε) * x ^ 2 + 4 * (b + d) ^ 2 / ε + 4 * |d| := by
  have he2 : e ^ 2 ≤ 4 := by nlinarith only [sq_abs e, abs_nonneg e, he]
  have hY := div_nonneg (sq_nonneg (ε * x - (b + d) * e)) hε.le
  have hId : (ε * x - (b + d) * e) ^ 2 / ε =
      ε * x ^ 2 - 2 * (b + d) * x * e + ((b + d) ^ 2 / ε) * e ^ 2 := by
    field_simp
    ring
  rw [hId] at hY
  have hB := mul_le_mul_of_nonneg_left he2 (div_nonneg (sq_nonneg (b + d)) hε.le)
  have hD := mul_le_mul_of_nonneg_right (le_abs_self d) (sq_nonneg e)
  have hD' := mul_le_mul_of_nonneg_left he2 (abs_nonneg d)
  rw [show 4 * (b + d) ^ 2 / ε = 4 * ((b + d) ^ 2 / ε) by ring]
  nlinarith only [hY, hB, hD, hD']

theorem finiteWeilCanonicalFluctuationPoint_transverse_bound (r t : ℕ) (i : Fin (r + 1)) :
    |finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 1 -
      finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 0| ≤ 2 := by
  have hs : (1 : ℝ) ≤ Real.sqrt (r + 1 : ℕ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (r + 1 : ℕ) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
    simpa only [Real.sqrt_one] using h
  have heq : finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 1 -
      finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 0 =
      finiteWeilCanonicalFluctuationResidualValue r (2 * (r + 1) ^ 2 + t) i /
        Real.sqrt (r + 1 : ℕ) := by
    change _ / _ - _ / _ = _
    rw [← sub_div]
    rfl
  rw [heq, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (r + 1 : ℕ))).mpr
  linarith only [finiteWeilCanonicalFluctuationResidualValue_quadratic_bound r t i, hs]

theorem finiteWeilCanonicalJointQuantile_quadratic_envelope (r t : ℕ) (a b d : ℝ)
    {ε : ℝ} (hε : 0 < ε) (u : {u : ℝ // u ∈ Ioo 0 1}) :
    Real.exp (finiteWeilJointQuadratic a b d
      (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u.val)) ≤
      Real.exp (4 * (b + d) ^ 2 / ε + 4 * |d|) * Real.exp ((a + 2 * b + d + ε) *
        quantile (finiteWeilCanonicalProjectedProbabilityLaw r
          (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ) u.val ^ 2) := by
  obtain ⟨i, hi, hq⟩ := finiteWeilCanonicalJointQuantile_at_level r (2 * (r + 1) ^ 2 + t) u
  rw [hi, hq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := finiteWeil_quadratic_transverse_envelope a b d
    (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 0)
    (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 1 -
      finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t) i 0)
    hε (finiteWeilCanonicalFluctuationPoint_transverse_bound r t i)
  simp only [add_sub_cancel] at h
  unfold finiteWeilJointQuadratic
  linarith only [h]

end RHTower
