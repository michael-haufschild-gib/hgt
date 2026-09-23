import GaloisForLFunctions.RHTower.PolynomialFockNormalizedTangentResponse

namespace RHTower

noncomputable section

theorem normSq_polynomialMomentFockTangentVector_lower
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) :
    Real.pi * polynomialFockTangentRadius m x ^ (2 : ℕ) *
        Real.exp (-(2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m))) ≤
      ‖polynomialMomentFockTangentVector m (by linarith) x‖ ^ (2 : ℕ) := by
  let hm2 : 2 ≤ m := by linarith
  let d : MomentFockData := polynomialMomentFockData m hm2
  let v : MomentFock := polynomialMomentFockTangentVector m hm2 x
  let K : ℝ := ‖momentFockKernel d (x : ℂ)‖
  let V : ℝ := ‖v‖
  let A : ℝ := Real.pi * polynomialFockTangentRadius m x ^ (2 : ℕ)
  let E : ℝ := Real.exp (2 * polynomialFockPotential m x +
    2 * (polynomialFockLocalBregmanConstant m / m))
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos Real.pi_pos
      (sq_pos_of_pos (polynomialFockTangentRadius_pos (by linarith)))
  have hE : 0 < E := by dsimp [E]; positivity
  have heval := norm_momentFockEvaluation_apply_le d (x : ℂ) v
  have hbase := polynomialMomentFockEvaluation_tangentVector_base m hm2 x
  have hone : (1 : ℝ) ≤ K * V := by
    change ‖polynomialMomentFockEvaluation m hm2 (x : ℂ) v‖ ≤ K * V at heval
    rw [hbase, norm_one] at heval
    exact heval
  have hKVnonneg : 0 ≤ K * V := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have honeSq : (1 : ℝ) ≤ K ^ (2 : ℕ) * V ^ (2 : ℕ) := by nlinarith [sq_nonneg (K * V)]
  have hkernel := normSq_polynomialMomentFockKernel_upper hm hx
  have hKupper : K ^ (2 : ℕ) ≤ E / A := by
    simpa [K, E, A, d, hm2] using hkernel
  have hchain : (1 : ℝ) ≤ (E / A) * V ^ (2 : ℕ) :=
    honeSq.trans (mul_le_mul_of_nonneg_right hKupper (sq_nonneg V))
  have hAE : A ≤ E * V ^ (2 : ℕ) := by
    calc
      A = 1 * A := by ring
      _ ≤ ((E / A) * V ^ (2 : ℕ)) * A :=
        mul_le_mul_of_nonneg_right hchain hA.le
      _ = E * V ^ (2 : ℕ) := by field_simp [hA.ne']
  change A * Real.exp (-(2 * polynomialFockPotential m x +
      2 * (polynomialFockLocalBregmanConstant m / m))) ≤ V ^ (2 : ℕ)
  rw [Real.exp_neg]
  change A / E ≤ V ^ (2 : ℕ)
  exact (div_le_iff₀ hE).2 (by simpa [mul_comm] using hAE)

theorem normSq_polynomialMomentFockTangentVector_upper_radius
    {m x : ℝ} (hm : 2 ≤ m) :
    ‖polynomialMomentFockTangentVector m hm x‖ ^ (2 : ℕ) ≤
      Real.pi * polynomialFockTangentRadius m x ^ (2 : ℕ) *
        Real.exp (-2 * polynomialFockPotential m x) := by
  have h := normSq_polynomialMomentFockTangentVector_le m hm x
  rw [polynomialFockTangentRadius_sq (by linarith : 0 < m)]
  calc
    ‖polynomialMomentFockTangentVector m hm x‖ ^ (2 : ℕ)
        ≤ Real.exp (-2 * polynomialFockPotential m x) *
          (Real.pi / (m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1))) := h
    _ = Real.pi * (m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1))⁻¹ *
        Real.exp (-2 * polynomialFockPotential m x) := by ring

end

end RHTower

