import GaloisForLFunctions.HTGeometry.ChamberLawExtremes

/-!
# The margin on the negative coordinate subspace

In a mixed chamber the coefficient diagonal is not negative definite on the whole space, but it is
on the vectors supported in the negative coordinates: there each term carries the margin, and the
terms at nonnegative coefficients vanish because the vector does.

That subspace has dimension the chamber grading, so it is the negative-definite subspace witnessing
the lower bound in a mixed chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

noncomputable section

open scoped Classical

/-- Vectors supported in the negative coordinates of a coefficient vector. -/
def negSupported {d : ℕ} (c : Fin d → ℝ) : Submodule ℂ (Fin d → ℂ) where
  carrier := {x | ∀ j, ¬ (c j < 0) → x j = 0}
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  zero_mem' := by
    intro j _
    rfl
  smul_mem' := by
    intro r x hx j hj
    simp [hx j hj]

@[simp]
theorem mem_negSupported {d : ℕ} (c : Fin d → ℝ) (x : Fin d → ℂ) :
    x ∈ negSupported c ↔ ∀ j, ¬ (c j < 0) → x j = 0 := Iff.rfl

/-- **The margin holds on the negative coordinate subspace.**  For a vector supported in the negative
coordinates, the coefficient diagonal form carries the margin of the negative coefficients. -/
theorem re_quadForm_diagonal_le_margin_on_negSupported {d : ℕ} (c : Fin d → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (x : Fin d → ℂ) (hx : x ∈ negSupported c) :
    (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re
      ≤ -δ * ‖x‖ ^ 2 := by
  classical
  rw [re_quadForm_diagonal]
  have hterm : ∀ j, c j * ‖x j‖ ^ 2 ≤ (-δ) * ‖x j‖ ^ 2 := by
    intro j
    by_cases hj : c j < 0
    · exact mul_le_mul_of_nonneg_right (hc j hj) (by positivity)
    · rw [(mem_negSupported c x).1 hx j hj]
      simp
  have h1 : ∑ j, c j * ‖x j‖ ^ 2 ≤ ∑ j, (-δ) * ‖x j‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => hterm j
  rw [← Finset.mul_sum] at h1
  have h2 : -δ * ∑ j, ‖x j‖ ^ 2 ≤ -δ * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonpos_left (sq_pi_norm_le_sum_sq x) (by linarith)
  linarith

/-- **A mixed chamber is negative definite on its negative coordinates.**  If the Gram deviates from
the coefficient diagonal by less than the margin, it is negative definite there. -/
theorem negDef_on_negSupported_of_perturbed {d : ℕ} (c : Fin d → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hc : ∀ j, c j < 0 → c j ≤ -δ)
    (G : Matrix (Fin d) (Fin d) ℂ)
    (hpert : ∀ x : Fin d → ℂ,
      |(star x ⬝ᵥ G.mulVec x).re
        - (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re|
        ≤ (δ / 2) * ‖x‖ ^ 2) :
    ∀ x ∈ negSupported c, x ≠ 0 → (star x ⬝ᵥ G.mulVec x).re < 0 := by
  intro x hx hxne
  have hmargin := re_quadForm_diagonal_le_margin_on_negSupported c hδ.le hc x hx
  have hp := hpert x
  have hupper := (abs_le.1 hp).2
  have hnn : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  have hpos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.2 hxne
    positivity
  nlinarith [hmargin, hupper, hpos, hδ]

end

end GaloisForLFunctions.HTGeometry
