import GaloisForLFunctions.HTGeometry.DiagonalQuadraticForm

/-!
# The negative diagonal has a uniform margin

The perturbation criterion needs the limiting form bounded above by `-δ‖x‖²`, not merely strictly
negative.  For a diagonal with all coefficients at most `-δ` the margin follows once the squared
supremum norm is bounded by the sum of squared coordinate moduli.

That bound needs no attainment of the supremum: each coordinate is bounded by the square root of the
sum, so the supremum is too.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- **The squared supremum norm is at most the sum of squared coordinate moduli.** -/
theorem sq_pi_norm_le_sum_sq {n : ℕ} (x : Fin n → ℂ) :
    ‖x‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 := by
  classical
  have hnn : (0 : ℝ) ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
    intro j
    have hj : ‖x j‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2)
        (fun k _ => by positivity) (Finset.mem_univ j)
    calc ‖x j‖ = Real.sqrt (‖x j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ k, ‖x k‖ ^ 2) := Real.sqrt_le_sqrt hj
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ j, ‖x j‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg x) hle 2
    _ = ∑ j, ‖x j‖ ^ 2 := Real.sq_sqrt hnn

/-- **The negative diagonal has the uniform margin the perturbation criterion needs.** -/
theorem re_quadForm_diagonal_le_margin {n : ℕ} (c : Fin n → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ j, c j ≤ -δ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re
      ≤ -δ * ‖x‖ ^ 2 := by
  classical
  rw [re_quadForm_diagonal]
  have h1 : ∑ j, c j * ‖x j‖ ^ 2 ≤ ∑ j, (-δ) * ‖x j‖ ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right (hc j) (by positivity)
  rw [← Finset.mul_sum] at h1
  have h2 : -δ * ∑ j, ‖x j‖ ^ 2 ≤ -δ * ‖x‖ ^ 2 := by
    have hnonpos : -δ ≤ 0 := by linarith
    exact mul_le_mul_of_nonpos_left (sq_pi_norm_le_sum_sq x) hnonpos
  linarith

end

end GaloisForLFunctions.HTGeometry
