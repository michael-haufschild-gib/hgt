import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClipping
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Symmetric clipping preserves inertia

A positive cutoff changes eigenvalue magnitudes but neither signs nor zero
modes. Hence bounded spectral regularization preserves all three inertia
indices, including negative directions of an indefinite form.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
open HTGeometry
noncomputable section

theorem clip_pos_iff (c : ℝ≥0) (hc : 0 < c) (x : ℝ) : 0 < clip c x ↔ 0 < x := by
  have hc' : (0 : ℝ) < c := hc
  simp only [clip, lt_max_iff, lt_min_iff,
    not_lt.mpr (neg_nonpos.mpr c.coe_nonneg), false_or, hc', and_true]

theorem clip_neg_iff (c : ℝ≥0) (hc : 0 < c) (x : ℝ) : clip c x < 0 ↔ x < 0 := by
  have hc' : (0 : ℝ) < c := hc
  simp only [clip, max_lt_iff, min_lt_iff, neg_neg_iff_pos, hc', true_and,
    not_lt.mpr c.coe_nonneg, or_false]

theorem clip_zero_iff (c : ℝ≥0) (hc : 0 < c) (x : ℝ) : clip c x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have hn := (clip_neg_iff c hc x).mpr hx
      linarith only [h, hn]
    · exact hx
    · have hp := (clip_pos_iff c hc x).mpr hx
      linarith only [h, hp]
  · rintro rfl
    exact clip_of_abs_le c (by simpa only [abs_zero] using c.coe_nonneg)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matrix_in_eigenbasis {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * matrix hA c *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) =
        diagonal (fun i => (clip c (hA.eigenvalues i) : ℂ)) := by
  simp only [matrix, specMap, Unitary.conjStarAlgAut_apply,
    ← star_eq_conjTranspose, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  rfl

/-- Positive, negative, and null indices all survive a positive symmetric cutoff. -/
theorem matrix_inertia {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) :
    hermPosIndex (matrix hA c) = hermPosIndex A ∧
      hermNegIndex (matrix hA c) = hermNegIndex A ∧
      hermNullIndex (matrix hA c) = hermNullIndex A := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [← posIndex_conjugate (matrix hA c) (isUnit_eigenvectorUnitary hA),
      matrix_in_eigenbasis, posIndex_diagonal, posIndex_eq_card_pos_eigenvalues hA]
    simp only [clip_pos_iff c hc]
  · rw [← negIndex_conjugate (matrix hA c) (isUnit_eigenvectorUnitary hA),
      matrix_in_eigenbasis, negIndex_diagonal, negIndex_eq_card_neg_eigenvalues hA]
    simp only [clip_neg_iff c hc]
  · rw [← nullIndex_conjugate (matrix hA c) (isUnit_eigenvectorUnitary hA),
      matrix_in_eigenbasis, nullIndex_diagonal, nullIndex_eq_card_zero_eigenvalues hA]
    simp only [clip_zero_iff c hc]

#print axioms matrix_inertia

end
end GaloisForLFunctions.HilbertMetric.SymmetricClipping
