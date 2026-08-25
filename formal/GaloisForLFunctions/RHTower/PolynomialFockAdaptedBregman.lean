import GaloisForLFunctions.RHTower.PolynomialFockLocalBregman

namespace RHTower

noncomputable section

/-- Reciprocal square root of the tangent-Gaussian curvature coefficient. -/
def polynomialFockTangentRadius (m x : ℝ) : ℝ :=
  (Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)))⁻¹

theorem polynomialFockTangentRadius_sq
    {m x : ℝ} (hm : 0 < m) :
    polynomialFockTangentRadius m x ^ 2 =
      (m * (1 + x ^ 2) ^ (m / 2 - 1))⁻¹ := by
  have hc : 0 ≤ m * (1 + x ^ 2) ^ (m / 2 - 1) := by positivity
  unfold polynomialFockTangentRadius
  rw [inv_pow, Real.sq_sqrt hc]

theorem polynomialFockTangentRadius_pos
    {m x : ℝ} (hm : 0 < m) : 0 < polynomialFockTangentRadius m x := by
  unfold polynomialFockTangentRadius
  positivity

theorem polynomialFockTangentRadius_le_half
    {m x : ℝ} (hm : 4 ≤ m) : polynomialFockTangentRadius m x ≤ 1 / 2 := by
  have hA : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hexp : 0 ≤ m / 2 - 1 := by linarith
  have hpow : 1 ≤ (1 + x ^ 2) ^ (m / 2 - 1) := Real.one_le_rpow hA hexp
  have hc : 4 ≤ m * (1 + x ^ 2) ^ (m / 2 - 1) := by nlinarith
  have hsqrt : 2 ≤ Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)) := by
    have := Real.sqrt_le_sqrt hc
    norm_num at this ⊢
    exact this
  unfold polynomialFockTangentRadius
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) hsqrt

/-- Uniform tangent-gauge oscillation on the exact curvature-scale disk. -/
theorem polynomialFockPotential_bregman_upper_tangentRadius
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) {w : ℂ}
    (hw : ‖w‖ ≤ polynomialFockTangentRadius m x) :
    polynomialFockPotential m ‖(x : ℂ) + w‖ - polynomialFockPotential m x -
        polynomialFockRadialSlope m x * w.re ≤
      polynomialFockLocalBregmanConstant m / m := by
  have hm0 : 0 < m := by linarith
  have hunit : ‖w‖ ≤ 1 := by
    calc
      ‖w‖ ≤ polynomialFockTangentRadius m x := hw
      _ ≤ 1 / 2 := polynomialFockTangentRadius_le_half hm
      _ ≤ 1 := by norm_num
  have hlocal := polynomialFockPotential_bregman_upper_unit hm hx w hunit
  have hsquare : ‖w‖ ^ 2 ≤ polynomialFockTangentRadius m x ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (polynomialFockTangentRadius_pos hm0).le).2 hw
  rw [polynomialFockTangentRadius_sq hm0] at hsquare
  let A : ℝ := 1 + x ^ 2
  let α : ℝ := m / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hAp : 0 < A ^ (α - 1) := Real.rpow_pos_of_pos hA _
  have hscaled : A ^ (α - 1) * ‖w‖ ^ 2 ≤ 1 / m := by
    calc
      A ^ (α - 1) * ‖w‖ ^ 2 ≤
          A ^ (α - 1) * (m * A ^ (α - 1))⁻¹ :=
        mul_le_mul_of_nonneg_left (by simpa [A, α] using hsquare) hAp.le
      _ = 1 / m := by field_simp
  have hC := (polynomialFockLocalBregmanConstant_pos hm).le
  have hbreg :
      polynomialFockPotential m ‖(x : ℂ) + w‖ - polynomialFockPotential m x -
          polynomialFockRadialSlope m x * w.re ≤
        polynomialFockLocalBregmanConstant m *
          ((1 + x ^ 2) ^ (m / 2 - 1) * ‖w‖ ^ 2) := by
    linarith
  calc
    polynomialFockPotential m ‖(x : ℂ) + w‖ - polynomialFockPotential m x -
          polynomialFockRadialSlope m x * w.re ≤
        polynomialFockLocalBregmanConstant m *
          (A ^ (α - 1) * ‖w‖ ^ 2) := by simpa [A, α] using hbreg
    _ ≤ polynomialFockLocalBregmanConstant m * (1 / m) :=
      mul_le_mul_of_nonneg_left hscaled hC
    _ = polynomialFockLocalBregmanConstant m / m := by ring

end

end RHTower
