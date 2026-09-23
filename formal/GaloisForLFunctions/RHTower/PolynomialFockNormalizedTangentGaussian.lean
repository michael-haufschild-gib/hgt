import GaloisForLFunctions.RHTower.PolynomialFockTangentNormComparison

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The weighted density of the normalized tangent vector is the raw tangent density divided by
its exact coefficient-space norm squared. -/
theorem polynomialMomentFockWeightedNormSq_normalizedTangentVector
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) (z : ℂ) :
    polynomialMomentFockWeightedNormSq m hm
        (polynomialMomentFockNormalizedTangentVector m hm x) z =
      polynomialFockTangentDensity m x z /
        ‖polynomialMomentFockTangentVector m hm x‖ ^ (2 : ℕ) := by
  let v : MomentFock := polynomialMomentFockTangentVector m hm x
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr
    (polynomialMomentFockTangentVector_ne_zero_of_two_le m hm x)
  rw [polynomialMomentFockWeightedNormSq,
    polynomialMomentFockNormalizedTangentVector]
  rw [polynomialMomentFockFunction_eq_evaluation, map_smul,
    ← polynomialMomentFockFunction_eq_evaluation]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hv]
  rw [div_eq_mul_inv]
  change (‖v‖⁻¹ *
      ‖polynomialMomentFockFunction m hm v z‖) ^ (2 : ℕ) *
        Real.exp (-2 * polynomialFockPotential m ‖z‖) = _
  rw [← polynomialMomentFockWeightedNormSq_tangentVector m hm x z]
  unfold polynomialMomentFockWeightedNormSq
  dsimp [v] at hv ⊢
  field_simp [hv.ne']

/-- Uniform curvature-scale Gaussian localization of normalized tangent vectors.  The loss is the
fixed local Bregman factor, while spatial decay occurs at the exact polynomial-Fock curvature. -/
theorem polynomialMomentFockWeightedNormSq_normalizedTangentVector_le_gaussian
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (z : ℂ) :
    polynomialMomentFockWeightedNormSq m (by linarith)
        (polynomialMomentFockNormalizedTangentVector m (by linarith) x) z ≤
      (m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1) / Real.pi) *
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        Real.exp (-(m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1) *
          ‖z - (x : ℂ)‖ ^ (2 : ℕ))) := by
  let hm2 : 2 ≤ m := by linarith
  let v : MomentFock := polynomialMomentFockTangentVector m hm2 x
  let N : ℝ := ‖v‖ ^ (2 : ℕ)
  let c : ℝ := m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)
  let C : ℝ := polynomialFockLocalBregmanConstant m / m
  let E : ℝ := Real.exp (-2 * polynomialFockPotential m x)
  let G : ℝ := Real.exp (-(c * ‖z - (x : ℂ)‖ ^ (2 : ℕ)))
  let B : ℝ := (c / Real.pi) * Real.exp (2 * C)
  have hc : 0 < c := by dsimp [c]; positivity
  have hN : 0 < N := by
    dsimp [N, v]
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (polynomialMomentFockTangentVector_ne_zero_of_two_le m hm2 x))
  have hraw : polynomialFockTangentDensity m x z ≤ E * G := by
    simpa [E, G, c] using polynomialFockTangentDensity_le_gaussian hm2 z
  have hnorm := normSq_polynomialMomentFockTangentVector_lower hm hx
  rw [polynomialFockTangentRadius_sq (by linarith : 0 < m)] at hnorm
  have hnorm' :
      Real.pi * c⁻¹ * Real.exp (-(2 * polynomialFockPotential m x + 2 * C)) ≤ N := by
    simpa [c, C, N, v, hm2] using hnorm
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBL :
      B * (Real.pi * c⁻¹ *
        Real.exp (-(2 * polynomialFockPotential m x + 2 * C))) = E := by
    dsimp [B, E]
    rw [Real.exp_neg, Real.exp_add]
    field_simp [hc.ne', Real.pi_ne_zero]
    rw [← Real.exp_add]
    simp
  have hEN : E ≤ B * N := by
    rw [← hBL]
    exact mul_le_mul_of_nonneg_left hnorm' hB
  rw [polynomialMomentFockWeightedNormSq_normalizedTangentVector]
  change polynomialFockTangentDensity m x z / N ≤ B * G
  calc
    polynomialFockTangentDensity m x z / N ≤ (E * G) / N :=
      div_le_div_of_nonneg_right hraw hN.le
    _ = G * (E / N) := by ring
    _ ≤ G * B := by
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hN).2 hEN) (by positivity)
    _ = B * G := by ring

end

end RHTower
