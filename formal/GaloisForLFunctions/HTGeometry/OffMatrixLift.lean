import GaloisForLFunctions.HTGeometry.StaticLocalExactReturnReflectionLaw

/-!
# Matrix lifts on the complement of a qubit cut

An arbitrary matrix on the complement of a cut embeds into the full configuration matrix by acting
identically on the cut coordinates.  The lift preserves products, adjoints, identities, unitarity,
and separation across the cut.

Consequently, an arbitrary unitary prefix lying wholly on the complement side can be stripped from
both a target and an approximant without changing operator-norm error or destroying the four-point
factorization obstruction.  No prefix dimension or prefix circuit synthesis cost appears.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Lift a matrix on the complement of `A` by the identity on `A`. -/
def offMatrixLift (A : Finset Q) (B : Matrix (Off A) (Off A) ℂ) :
    Matrix (Config Q) (Config Q) ℂ :=
  fun x y => if (splitConfig A x).1 = (splitConfig A y).1
    then B (splitConfig A x).2 (splitConfig A y).2 else 0

omit [Fintype Q] in
theorem offMatrixLift_separates (A : Finset Q) (B : Matrix (Off A) (Off A) ℂ) :
    SeparatesAcross A (offMatrixLift A B) := by
  refine ⟨1, B, fun x y => ?_⟩
  simp only [offMatrixLift, one_apply]
  split_ifs <;> simp

@[simp] theorem offMatrixLift_one (A : Finset Q) :
    offMatrixLift A (1 : Matrix (Off A) (Off A) ℂ) = 1 := by
  ext x y
  simp only [offMatrixLift, one_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · have hsplit : (splitConfig A x).1 ≠ (splitConfig A y).1 ∨
        (splitConfig A x).2 ≠ (splitConfig A y).2 := by
      by_contra h
      push Not at h
      exact hxy ((splitConfig A).injective (Prod.ext h.1 h.2))
    rcases hsplit with h | h <;> simp [h, hxy]

omit [Fintype Q] in
@[simp] theorem offMatrixLift_conjTranspose (A : Finset Q)
    (B : Matrix (Off A) (Off A) ℂ) :
    offMatrixLift A Bᴴ = (offMatrixLift A B)ᴴ := by
  ext x y
  simp only [offMatrixLift, Matrix.conjTranspose_apply]
  by_cases h : (splitConfig A x).1 = (splitConfig A y).1
  · rw [if_pos h, if_pos h.symm]
  · have hs : (splitConfig A y).1 ≠ (splitConfig A x).1 := by
      simpa [eq_comm] using h
    rw [if_neg h, if_neg hs]
    simp

@[simp] theorem offMatrixLift_mul (A : Finset Q)
    (B C : Matrix (Off A) (Off A) ℂ) :
    offMatrixLift A (B * C) = offMatrixLift A B * offMatrixLift A C := by
  ext x y
  rw [Matrix.mul_apply]
  symm
  calc
    (∑ z : Config Q, offMatrixLift A B x z * offMatrixLift A C z y) =
        ∑ p : On A × Off A,
          offMatrixLift A B x ((splitConfig A).symm p) *
            offMatrixLift A C ((splitConfig A).symm p) y := by
      apply Fintype.sum_equiv (splitConfig A)
      intro z
      simp
    _ = offMatrixLift A (B * C) x y := by
      rw [Fintype.sum_prod_type]
      by_cases h : (splitConfig A x).1 = (splitConfig A y).1
      · simp [offMatrixLift, h, Matrix.mul_apply]
      · simp [offMatrixLift, h]

/-- The complement lift of a unitary matrix is unitary. -/
theorem offMatrixLift_unitary (A : Finset Q) {B : Matrix (Off A) (Off A) ℂ}
    (hB : B ∈ Matrix.unitaryGroup (Off A) ℂ) :
    offMatrixLift A B ∈ Matrix.unitaryGroup (Config Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hB ⊢
  rw [Matrix.star_eq_conjTranspose] at hB ⊢
  rw [← offMatrixLift_conjTranspose, ← offMatrixLift_mul, hB, offMatrixLift_one]

/-- Left-stripping a complement unitary preserves finite-matrix operator-norm distance exactly. -/
theorem prefixStrip_distance_eq (A : Finset Q)
    {B : Matrix (Off A) (Off A) ℂ} (hB : B ∈ Matrix.unitaryGroup (Off A) ℂ)
    (W U : Matrix (Config Q) (Config Q) ℂ) :
    ‖(offMatrixLift A B)ᴴ * W - (offMatrixLift A B)ᴴ * U‖ = ‖W - U‖ := by
  have hLift := offMatrixLift_unitary A hB
  have hStar : (offMatrixLift A B)ᴴ ∈ Matrix.unitaryGroup (Config Q) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hLift
  rw [← Matrix.mul_sub]
  exact CStarRing.norm_mem_unitary_mul (W - U) hStar

/-- Left-stripping a complement matrix preserves separation across the cut. -/
theorem prefixStrip_separates (A : Finset Q)
    {B : Matrix (Off A) (Off A) ℂ}
    {W : Matrix (Config Q) (Config Q) ℂ}
    (hW : SeparatesAcross A W) :
    SeparatesAcross A ((offMatrixLift A B)ᴴ * W) := by
  exact SeparatesAcross.mul (offMatrixLift_separates A B).conjTranspose hW

/-- A complement unitary cancels exactly from a factored target. -/
theorem prefixStrip_mul_self (A : Finset Q)
    {B : Matrix (Off A) (Off A) ℂ} (hB : B ∈ Matrix.unitaryGroup (Off A) ℂ)
    (D : Matrix (Config Q) (Config Q) ℂ) :
    (offMatrixLift A B)ᴴ * (offMatrixLift A B * D) = D := by
  have hLift := offMatrixLift_unitary A hB
  have hleft : (offMatrixLift A B)ᴴ * offMatrixLift A B = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Unitary.mem_iff.mp hLift).1
  rw [← Matrix.mul_assoc, hleft, one_mul]

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
