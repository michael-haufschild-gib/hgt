import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Self-adjoint Rayleigh bounds -/

namespace AffineExpanders

/-- For self-adjoint operators, an inner product bound implies an operator norm bound.
    If `∀ x, |⟨Ax, x⟩| ≤ c · ‖x‖²`, then `‖A‖ ≤ c`.
    Proof via polarization identity + parallelogram law. -/
lemma sa_opNorm_le_of_inner_le {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT_sa : IsSelfAdjoint T) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, |@inner ℝ _ _ (T x) x| ≤ c * ‖x‖ ^ 2) :
    ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  by_cases hx : x = 0
  · simp [hx]
  by_cases hTx : T x = 0
  · simp [hTx]; positivity
  -- Self-adjointness: ⟨Ty, x⟩ = ⟨Tx, y⟩
  have hT_sym : ∀ u v : EuclideanSpace ℝ (Fin n),
      @inner ℝ _ _ (T u) v = @inner ℝ _ _ u (T v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT_sa
  have hTx_pos : (0 : ℝ) < ‖T x‖ := norm_pos_iff.mpr hTx
  -- Choose y = (‖x‖/‖Tx‖) • Tx so that ‖y‖ = ‖x‖
  set y := (‖x‖ / ‖T x‖) • T x
  have hy_norm : ‖y‖ = ‖x‖ := by
    simp only [y, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) hTx_pos.le)]
    exact div_mul_cancel₀ _ (ne_of_gt hTx_pos)
  -- ⟨Tx, y⟩ = ‖x‖ · ‖Tx‖
  have hTxy : @inner ℝ _ _ (T x) y = ‖x‖ * ‖T x‖ := by
    simp only [y, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  -- Polarization: ⟨T(x+y), x+y⟩ - ⟨T(x-y), x-y⟩ = 4⟨Tx, y⟩
  have h_polar : @inner ℝ _ _ (T (x + y)) (x + y) - @inner ℝ _ _ (T (x - y)) (x - y) =
      4 * @inner ℝ _ _ (T x) y := by
    have hsym : @inner ℝ _ _ (T y) x = @inner ℝ _ _ (T x) y := by
      rw [hT_sym y x, real_inner_comm]
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    linarith
  -- Bound: 4⟨Tx,y⟩ ≤ |⟨T(x+y),x+y⟩| + |⟨T(x-y),x-y⟩| ≤ c(‖x+y‖² + ‖x-y‖²)
  have h_bound : 4 * (‖x‖ * ‖T x‖) ≤ c * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by
    calc 4 * (‖x‖ * ‖T x‖)
        = 4 * @inner ℝ _ _ (T x) y := by rw [hTxy]
      _ = @inner ℝ _ _ (T (x + y)) (x + y) -
            @inner ℝ _ _ (T (x - y)) (x - y) := by linarith [h_polar]
      _ ≤ |@inner ℝ _ _ (T (x + y)) (x + y)| +
            |@inner ℝ _ _ (T (x - y)) (x - y)| := by
          linarith [le_abs_self (@inner ℝ _ _ (T (x + y)) (x + y)),
                    neg_abs_le (@inner ℝ _ _ (T (x - y)) (x - y))]
      _ ≤ c * ‖x + y‖ ^ 2 + c * ‖x - y‖ ^ 2 := by linarith [h (x + y), h (x - y)]
      _ = c * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by ring
  -- Parallelogram: ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)
  have h_para : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have := parallelogram_law_with_norm (𝕜 := ℝ) x y
    nlinarith [sq (‖x + y‖), sq (‖x - y‖), sq ‖x‖, sq ‖y‖]
  rw [h_para, hy_norm] at h_bound
  -- h_bound : 4 * (‖x‖ * ‖T x‖) ≤ c * (2 * (‖x‖ ^ 2 + ‖x‖ ^ 2)) = 4c‖x‖²
  have hx_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have h_ineq : ‖x‖ * ‖T x‖ ≤ ‖x‖ * (c * ‖x‖) := by nlinarith
  exact le_of_mul_le_mul_left h_ineq hx_pos

end AffineExpanders
