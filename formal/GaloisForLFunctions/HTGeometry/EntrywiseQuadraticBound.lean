import GaloisForLFunctions.HTGeometry.ScaledAtomicDistinctNodes

/-!
# Entrywise bounds control the quadratic form

The Krein index limit produces entrywise estimates on the scaled Gram matrix, while the negative
definiteness criterion consumes a quadratic modulus.  On a finite index the two are equivalent up to
the dimension: each entry contributes at most its modulus times the square of the supremum norm.

So an entrywise bound of size `M` gives a quadratic modulus of `M n²`, which is all the perturbation
argument needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- **An entrywise bound bounds the quadratic form.**  On a finite index the modulus of the
Hermitian quadratic form is at most the entrywise bound times the squared dimension times the
squared supremum norm. -/
theorem norm_quadForm_le_of_entries {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hE : ∀ j k, ‖E j k‖ ≤ M) (x : Fin n → ℂ) :
    ‖star x ⬝ᵥ E.mulVec x‖ ≤ M * n ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) := by
  classical
  have hexp : star x ⬝ᵥ E.mulVec x = ∑ j, ∑ k, (starRingEnd ℂ) (x j) * (E j k * x k) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rfl
  rw [hexp]
  have hxle : ∀ j, ‖x j‖ ≤ ‖x‖ := fun j => norm_le_pi_norm x j
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  calc ‖∑ j, ∑ k, (starRingEnd ℂ) (x j) * (E j k * x k)‖
      ≤ ∑ j, ‖∑ k, (starRingEnd ℂ) (x j) * (E j k * x k)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, M * ‖x‖ ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        have h1 : ‖x j‖ * (‖E j k‖ * ‖x k‖) ≤ ‖x‖ * (M * ‖x‖) := by
          apply mul_le_mul (hxle j) _ (by positivity) hnn
          exact mul_le_mul (hE j k) (hxle k) (norm_nonneg _) hM
        calc ‖x j‖ * (‖E j k‖ * ‖x k‖) ≤ ‖x‖ * (M * ‖x‖) := h1
          _ = M * ‖x‖ ^ (2 : ℕ) := by ring
    _ = M * n ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

end

end GaloisForLFunctions.HTGeometry
