import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelPolynomialActions

/-!
# Complete polynomial kernel of collision Hankel sections

A coefficient vector is null exactly when its polynomial vanishes at each
active collision atom. No condition is imposed at a vanished spectral sector.
This includes the empty matrix and all equilibrium and pure-mode cases.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem weighted_square_zero (c a z : ℝ) (hc : c ≠ 0) :
    c * a * z ^ (2 : ℕ) = 0 ↔ a = 0 ∨ z = 0 := by
  simp only [mul_eq_zero, hc, false_or, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]

/-- The full Hankel kernel is exactly the coefficient polynomials vanishing at every active collision node. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_kernel_iff_roots (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (v : Fin d → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).mulVec v = 0 ↔
      (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨
        (_root_.HTGeometry.finiteHankelNullPolynomial v).eval (4 / 9) = 0) ∧
      (egbFixedChargeAGibbsFastModeEnergy n β E = 0 ∨
        (_root_.HTGeometry.finiteHankelNullPolynomial v).eval (1 / 36) = 0) := by
  have hr : (4 / 9 : ℝ) ^ (o + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs : (1 / 36 : ℝ) ^ (o + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  constructor
  · intro hv
    have hq := egbFixedChargeAGibbsCollisionHankelMatrix_quadratic_polynomial n o d β E v
    rw [hv, dotProduct_zero] at hq
    have hAr : 0 ≤ ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
        ((_root_.HTGeometry.finiteHankelNullPolynomial v).eval (4 / 9)) ^ (2 : ℕ) := by positivity
    have hBs : 0 ≤ ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
        ((_root_.HTGeometry.finiteHankelNullPolynomial v).eval (1 / 36)) ^ (2 : ℕ) := by positivity
    have ha0 : ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
        ((_root_.HTGeometry.finiteHankelNullPolynomial v).eval (4 / 9)) ^ (2 : ℕ) = 0 := by linarith
    have hb0 : ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
        ((_root_.HTGeometry.finiteHankelNullPolynomial v).eval (1 / 36)) ^ (2 : ℕ) = 0 := by linarith
    exact ⟨(weighted_square_zero _ _ _ hr).mp ha0, (weighted_square_zero _ _ _ hs).mp hb0⟩
  · rintro ⟨ha, hb⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      funext i <;> rw [egbFixedChargeAGibbsCollisionHankelMatrix_mulVec_polynomial] <;>
      rw [ha, hb] <;> simp

end
end GaloisForLFunctions.HTGeometry
