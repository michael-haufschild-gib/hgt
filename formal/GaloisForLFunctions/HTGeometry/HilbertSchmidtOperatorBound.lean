import GaloisForLFunctions.HTGeometry.KroneckerAmplification

/-!
# Hilbert–Schmidt norms against the operator norm

The Hilbert–Schmidt norm of a matrix is the Euclidean norm of its entry vector.  Multiplying by a
matrix on either side changes it by at most the operator norm of that matrix, because the columns
(respectively the rows) transform by the corresponding linear map.  Conjugating by a unitary is
therefore isometric, and two unitary conjugations of one observable differ by at most twice the
distance of the unitaries times the Hilbert–Schmidt norm of the observable.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The entry vector of a matrix. -/
def matVec (X : Matrix d d ℂ) : EuclideanSpace ℂ (d × d) :=
  (EuclideanSpace.equiv _ ℂ).symm fun p => X p.1 p.2

omit [DecidableEq d] in
omit [Fintype d] in
@[simp] theorem matVec_sub (X Y : Matrix d d ℂ) : matVec (X - Y) = matVec X - matVec Y := rfl

/-- The Hilbert–Schmidt norm of a matrix. -/
def hsNorm (X : Matrix d d ℂ) : ℝ := ‖matVec X‖

omit [DecidableEq d] in
theorem hsNorm_nonneg (X : Matrix d d ℂ) : 0 ≤ hsNorm X := norm_nonneg _

omit [DecidableEq d] in
theorem hsNorm_sq (X : Matrix d d ℂ) : hsNorm X ^ (2 : ℕ) = ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℕ) := by
  rw [hsNorm, matVec, norm_sq_euclideanOfFun, Fintype.sum_prod_type]

omit [DecidableEq d] in
/-- The Hilbert–Schmidt norm, computed column by column. -/
theorem hsNorm_sq_eq_sum_col (X : Matrix d d ℂ) :
    hsNorm X ^ (2 : ℕ) = ∑ j, ‖(EuclideanSpace.equiv d ℂ).symm fun i => X i j‖ ^ (2 : ℕ) := by
  rw [hsNorm_sq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (norm_sq_euclideanOfFun _).symm

omit [DecidableEq d] in
theorem hsNorm_sub_le (X Y Z : Matrix d d ℂ) :
    hsNorm (X - Z) ≤ hsNorm (X - Y) + hsNorm (Y - Z) := by
  have hsplit : X - Z = (X - Y) + (Y - Z) := by abel
  rw [hsNorm, hsNorm, hsNorm, hsplit]
  have hadd : matVec ((X - Y) + (Y - Z)) = matVec (X - Y) + matVec (Y - Z) := rfl
  rw [hadd]
  exact norm_add_le _ _

/-- **Left multiplication.**  The Hilbert–Schmidt norm grows by at most the operator norm. -/
theorem hsNorm_mul_le (A X : Matrix d d ℂ) : hsNorm (A * X) ≤ ‖A‖ * hsNorm X := by
  have hcol : ∀ j : d, ((EuclideanSpace.equiv d ℂ).symm fun i => (A * X) i j)
      = (EuclideanSpace.equiv d ℂ).symm (A *ᵥ fun i => X i j) := by
    intro j
    rfl
  have hbound : hsNorm (A * X) ^ (2 : ℕ) ≤ (‖A‖ * hsNorm X) ^ (2 : ℕ) := by
    rw [hsNorm_sq_eq_sum_col, mul_pow, hsNorm_sq_eq_sum_col, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcol j]
    have hstep := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv d ℂ).symm fun i => X i j)
    calc ‖(EuclideanSpace.equiv d ℂ).symm (A *ᵥ fun i => X i j)‖ ^ (2 : ℕ)
        ≤ (‖A‖ * ‖(EuclideanSpace.equiv d ℂ).symm fun i => X i j‖) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hstep 2
      _ = ‖A‖ ^ (2 : ℕ) * ‖(EuclideanSpace.equiv d ℂ).symm fun i => X i j‖ ^ (2 : ℕ) := by ring
  have hsqrt := Real.sqrt_le_sqrt hbound
  rwa [Real.sqrt_sq (hsNorm_nonneg _),
    Real.sqrt_sq (mul_nonneg (norm_nonneg A) (hsNorm_nonneg X))] at hsqrt

omit [DecidableEq d] in
theorem hsNorm_conjTranspose (X : Matrix d d ℂ) : hsNorm Xᴴ = hsNorm X := by
  have hsq : hsNorm Xᴴ ^ (2 : ℕ) = hsNorm X ^ (2 : ℕ) := by
    rw [hsNorm_sq, hsNorm_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, norm_star]
  have h1 := hsNorm_nonneg Xᴴ
  have h2 := hsNorm_nonneg X
  nlinarith [hsq]

/-- **Right multiplication.**  The Hilbert–Schmidt norm grows by at most the operator norm. -/
theorem hsNorm_mul_le' (X A : Matrix d d ℂ) : hsNorm (X * A) ≤ hsNorm X * ‖A‖ := by
  have hstar : hsNorm (X * A) = hsNorm (Aᴴ * Xᴴ) := by
    rw [← Matrix.conjTranspose_mul, hsNorm_conjTranspose]
  rw [hstar]
  calc hsNorm (Aᴴ * Xᴴ) ≤ ‖Aᴴ‖ * hsNorm Xᴴ := hsNorm_mul_le _ _
    _ = hsNorm X * ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose, hsNorm_conjTranspose, mul_comm]

/-- **Conjugation stability in Hilbert–Schmidt norm.** -/
theorem hsNorm_conjugation_sub_le [Nonempty d] {U V : Matrix d d ℂ}
    (hU : U ∈ unitary (Matrix d d ℂ))
    (hV : V ∈ unitary (Matrix d d ℂ)) (X : Matrix d d ℂ) :
    hsNorm (U * X * star U - V * X * star V) ≤ 2 * ‖U - V‖ * hsNorm X := by
  have hsplit : U * X * star U - V * X * star V
      = (U - V) * X * star U + V * X * (star U - star V) := by
    noncomm_ring
  have hU1 : ‖U‖ = 1 := CStarRing.norm_coe_unitary ⟨U, hU⟩
  have hV1 : ‖V‖ = 1 := CStarRing.norm_coe_unitary ⟨V, hV⟩
  have hstarU1 : ‖star U‖ = 1 := by rw [norm_star]; exact hU1
  have hfirst : hsNorm ((U - V) * X * star U) ≤ ‖U - V‖ * hsNorm X := by
    calc hsNorm ((U - V) * X * star U) ≤ hsNorm ((U - V) * X) * ‖star U‖ := hsNorm_mul_le' _ _
      _ = hsNorm ((U - V) * X) := by rw [hstarU1, mul_one]
      _ ≤ ‖U - V‖ * hsNorm X := hsNorm_mul_le _ _
  have hsecond : hsNorm (V * X * (star U - star V)) ≤ ‖U - V‖ * hsNorm X := by
    have hstarsub : ‖star U - star V‖ = ‖U - V‖ := by
      rw [← star_sub, norm_star]
    calc hsNorm (V * X * (star U - star V)) ≤ hsNorm (V * X) * ‖star U - star V‖ :=
          hsNorm_mul_le' _ _
      _ ≤ (‖V‖ * hsNorm X) * ‖star U - star V‖ := by
          exact mul_le_mul_of_nonneg_right (hsNorm_mul_le _ _) (norm_nonneg _)
      _ = ‖U - V‖ * hsNorm X := by rw [hV1, one_mul, hstarsub, mul_comm]
  have hadd : hsNorm ((U - V) * X * star U + V * X * (star U - star V))
      ≤ hsNorm ((U - V) * X * star U) + hsNorm (V * X * (star U - star V)) := by
    have h0 : hsNorm ((U - V) * X * star U + V * X * (star U - star V))
        = ‖matVec ((U - V) * X * star U) + matVec (V * X * (star U - star V))‖ := rfl
    rw [h0, hsNorm, hsNorm]
    exact norm_add_le _ _
  rw [hsplit]
  calc hsNorm ((U - V) * X * star U + V * X * (star U - star V))
      ≤ hsNorm ((U - V) * X * star U) + hsNorm (V * X * (star U - star V)) := hadd
    _ ≤ ‖U - V‖ * hsNorm X + ‖U - V‖ * hsNorm X := add_le_add hfirst hsecond
    _ = 2 * ‖U - V‖ * hsNorm X := by ring

end

end GaloisForLFunctions.HTGeometry
