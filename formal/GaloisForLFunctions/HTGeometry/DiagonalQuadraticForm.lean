import GaloisForLFunctions.HTGeometry.EntrywiseQuadraticBound

/-!
# The quadratic form of a real diagonal matrix

The limit of the scaled Gram matrix is the diagonal of the atom coefficients.  Its Hermitian
quadratic form is the coefficient-weighted sum of the squared coordinate moduli, so the form is
negative definite exactly when all coefficients are negative.

Reading the form in this explicit shape is what lets the negative definiteness margin be exhibited
coordinatewise.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- **The diagonal quadratic form is the weighted sum of squared moduli.** -/
theorem quadForm_diagonal_eq {n : ℕ} (c : Fin n → ℝ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x
      = ((∑ j, c j * ‖x j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]
  have hstar : (star x) j = (starRingEnd ℂ) (x j) := rfl
  rw [hstar]
  rw [show ((c j : ℝ) : ℂ) * x j = x j * ((c j : ℝ) : ℂ) from mul_comm _ _]
  rw [← mul_assoc]
  rw [mul_comm ((starRingEnd ℂ) (x j)) (x j)]
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The real part of the diagonal form is the weighted sum of squared moduli. -/
theorem re_quadForm_diagonal {n : ℕ} (c : Fin n → ℝ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re
      = ∑ j, c j * ‖x j‖ ^ (2 : ℕ) := by
  rw [quadForm_diagonal_eq]
  exact Complex.ofReal_re _

/-- **A negative diagonal is negative definite.**  If every coefficient is negative the form is
strictly negative on nonzero vectors. -/
theorem re_quadForm_diagonal_neg {n : ℕ} (c : Fin n → ℝ) (hc : ∀ j, c j < 0)
    (x : Fin n → ℂ) (hx : x ≠ 0) :
    (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re < 0 := by
  classical
  rw [re_quadForm_diagonal]
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  have hpos : 0 < ‖x j₀‖ ^ (2 : ℕ) := by
    have : 0 < ‖x j₀‖ := norm_pos_iff.2 hj₀
    positivity
  have hterm : ∀ j, c j * ‖x j‖ ^ (2 : ℕ) ≤ 0 := by
    intro j
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hc j)) (by positivity)
  have hj0 : c j₀ * ‖x j₀‖ ^ (2 : ℕ) < 0 := mul_neg_of_neg_of_pos (hc j₀) hpos
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => c j * ‖x j‖ ^ (2 : ℕ))
    (Finset.mem_univ j₀)
  have hrest : ∑ j ∈ Finset.univ.erase j₀, c j * ‖x j‖ ^ (2 : ℕ) ≤ 0 :=
    Finset.sum_nonpos fun j _ => hterm j
  rw [← hsplit]
  linarith

end

end GaloisForLFunctions.HTGeometry
