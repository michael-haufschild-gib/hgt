import GaloisForLFunctions.RHTower.PolynomialFockSharpPhaseTransition

namespace RHTower

noncomputable section

/-- Exact measure weight converting raw polynomial-Fock evaluation into normalized-kernel
evaluation at a positive-real atom. -/
def polynomialFockExactToeplitzAtomScale
    (m : ℝ) (hm : 4 ≤ m) (x : ℝ) : ℝ :=
  Real.exp (2 * polynomialFockPotential m x) /
    ‖momentFockKernel (polynomialMomentFockData m (by linarith)) (x : ℂ)‖ ^ (2 : ℕ)

theorem polynomialFockExactToeplitzAtomScale_pos
    {m : ℝ} (hm : 4 ≤ m) (x : ℝ) :
    0 < polynomialFockExactToeplitzAtomScale m hm x := by
  rw [polynomialFockExactToeplitzAtomScale]
  exact div_pos (Real.exp_pos _)
    (sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero _ _)))

theorem polynomialFockExactToeplitzAtomScale_le
    {m x : ℝ} (hm : 4 ≤ m) :
    polynomialFockExactToeplitzAtomScale m hm x ≤
      Real.pi * polynomialFockTangentRadius m x ^ (2 : ℕ) := by
  let E : ℝ := Real.exp (2 * polynomialFockPotential m x)
  let c : ℝ := m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)
  let K : ℝ := ‖momentFockKernel
    (polynomialMomentFockData m (by linarith)) (x : ℂ)‖ ^ (2 : ℕ)
  have hm0 : 0 < m := by linarith
  have hE : 0 < E := by dsimp [E]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := by
    dsimp [K]
    exact sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero _ _))
  have hdiag : E * (c / Real.pi) ≤ K := by
    simpa [E, c, K] using normSq_polynomialMomentFockKernel_lower (m := m)
      (by linarith : 2 ≤ m) x
  have hL : 0 < E * (c / Real.pi) := mul_pos hE (div_pos hc Real.pi_pos)
  have hinv : K⁻¹ ≤ (E * (c / Real.pi))⁻¹ := inv_anti₀ hL hdiag
  have hmul := mul_le_mul_of_nonneg_left hinv hE.le
  rw [polynomialFockExactToeplitzAtomScale, div_eq_mul_inv]
  change E * K⁻¹ ≤ Real.pi * polynomialFockTangentRadius m x ^ (2 : ℕ)
  apply hmul.trans_eq
  rw [polynomialFockTangentRadius_sq hm0]
  dsimp [E, c]
  field_simp

theorem polynomialFockExactToeplitzAtomScale_lower
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    Real.pi * Real.exp (-2 * (polynomialFockLocalBregmanConstant m / m)) *
        polynomialFockInnerWindowFactor m ^ (2 : ℕ) * criticalPrimeFockRadius m x ^ (2 : ℕ) ≤
      polynomialFockExactToeplitzAtomScale m hm x := by
  let E : ℝ := Real.exp (2 * polynomialFockPotential m x)
  let A : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m))
  let r : ℝ := polynomialFockTangentRadius m x
  let K : ℝ := ‖momentFockKernel
    (polynomialMomentFockData m (by linarith)) (x : ℂ)‖ ^ (2 : ℕ)
  have hm0 : 0 < m := by linarith
  have hE : 0 < E := by dsimp [E]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hr : 0 < r := by dsimp [r]; exact polynomialFockTangentRadius_pos hm0
  have hK : 0 < K := by
    dsimp [K]
    exact sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero _ _))
  have hdiag : K ≤ E * A / (Real.pi * r ^ (2 : ℕ)) := by
    have h := normSq_polynomialMomentFockKernel_upper hm (le_trans zero_le_one hx)
    simpa [E, A, r, K, add_assoc, ← Real.exp_add] using h
  have hU : 0 < E * A / (Real.pi * r ^ (2 : ℕ)) := by positivity
  have hinv : (E * A / (Real.pi * r ^ (2 : ℕ)))⁻¹ ≤ K⁻¹ := inv_anti₀ hK hdiag
  have hmul := mul_le_mul_of_nonneg_left hinv hE.le
  have hscale : polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x ≤ r := by
    simpa [r] using scaledCriticalPrimeFockRadius_le_tangentRadius hm hx
  have hscaleSq : polynomialFockInnerWindowFactor m ^ (2 : ℕ) *
      criticalPrimeFockRadius m x ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
    nlinarith [sq_le_sq₀
      (mul_nonneg (polynomialFockInnerWindowFactor_pos hm).le
        (criticalPrimeFockRadius_pos (by linarith)).le) hr.le |>.2 hscale]
  have hAinv : Real.exp (-2 * (polynomialFockLocalBregmanConstant m / m)) = A⁻¹ := by
    dsimp [A]
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hAinv]
  rw [polynomialFockExactToeplitzAtomScale, div_eq_mul_inv]
  change Real.pi * A⁻¹ * polynomialFockInnerWindowFactor m ^ (2 : ℕ) *
      criticalPrimeFockRadius m x ^ (2 : ℕ) ≤ E * K⁻¹
  apply le_trans ?_ hmul
  have hleft : Real.pi * A⁻¹ * polynomialFockInnerWindowFactor m ^ (2 : ℕ) *
      criticalPrimeFockRadius m x ^ (2 : ℕ) ≤ Real.pi * A⁻¹ * r ^ (2 : ℕ) := by
    have hcoef : 0 ≤ Real.pi * A⁻¹ := mul_nonneg Real.pi_pos.le (inv_nonneg.mpr hA.le)
    nlinarith
  apply hleft.trans_eq
  dsimp [E, A]
  field_simp

end

end RHTower
