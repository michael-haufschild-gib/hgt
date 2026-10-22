import GaloisForLFunctions.RHTower.PolynomialFockNormalizedTangentResponse

/-!
# Two-sided norm comparison for polynomial Fock tangent vectors

In the degree-`m` polynomial moment Fock space with potential `φ_m(r) = (1 + r²)^(m/2)`, the
tangent exponential `v_x` at a real point `x` takes value one at `x`. Its squared norm is
comparable to the area of the tangent ball times the weight: with tangent radius
`r_m(x) = (m (1 + x²)^(m/2 - 1))^(-1/2)`,
`π r_m(x)² e^{-2 φ_m(x) - 2C/m} ≤ ‖v_x‖² ≤ π r_m(x)² e^{-2 φ_m(x)}`, where `C` is the local Bregman
constant.

## Main results

- `normSq_polynomialMomentFockTangentVector_lower`: the lower bound, for `m ≥ 4` and `x ≥ 0`.
- `normSq_polynomialMomentFockTangentVector_upper_radius`: the upper bound, for `m ≥ 2`.

## Hypotheses

Both results are unconditional; the parameter ranges are `4 ≤ m`, `0 ≤ x` for the lower bound and
`2 ≤ m` for the upper bound.
-/

namespace RHTower

noncomputable section

/-- Assuming `4 ≤ m` and `0 ≤ x`, `π r_m(x)² e^{-(2 φ_m(x) + 2C/m)} ≤ ‖v_x‖²`, from `v_x(x) = 1` and
the upper bound on the reproducing kernel norm at `x`. -/
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

/-- For `2 ≤ m`, `‖v_x‖² ≤ π r_m(x)² e^{-2 φ_m(x)}`, with `r_m` the tangent radius. -/
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

