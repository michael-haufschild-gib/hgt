import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovMonomialPermutations
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovDirectionalFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.CoordinatePermutationVolume

/-!
# Symmetry of affine moment frames under horizontal permutations

Grouping the horizontal shear coefficients into one vector makes their
symmetry explicit. The polynomial moment action determines its matrix, so
permuting the physical horizontal variables conjugates that matrix by the
induced permutation of all monomial coordinates. Cube-overlap volume is
unchanged after permuting both centers.
-/

open MeasureTheory Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The induced permutation of monomial coordinates for a horizontal variable permutation. -/
abbrev horizontalIndexPermutation (r k : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :=
  axisIndexPermutation r k (horizontalVariablePermutation r σ)

theorem coordinatePermutation_horizontalMoment (r k : ℕ) (σ : Equiv.Perm (Fin (r + 1)))
    (u : Fin (r + 1) → ℝ) (z : ℝ) :
    coordinatePermutation (horizontalIndexPermutation r k σ) (horizontalMoment r k u z) =
      horizontalMoment r k (fun i => u (σ.symm i)) z := by
  funext a
  rw [coordinatePermutation_apply]
  exact horizontalMoment_permutation r k σ u z a

/-- Affine moment matrix with the complete horizontal coefficient vector as one parameter. -/
def vectorAffineMatrix (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ :=
  directionalAffineMatrix r k (δ 0) (fun i => δ i.succ) t

/-- The actual centered moment action of the complete horizontal linear form. -/
theorem vectorAffineMatrix_moment (r k : ℕ) (δ u : Fin (r + 1) → ℝ) (t z : ℝ) :
    vectorAffineMatrix r k δ t *ᵥ horizontalMoment r k u z =
      horizontalMoment r k u (z + ∑ i, δ i * u i + t) - horizontalMoment r k 0 t := by
  simpa only [vectorAffineMatrix, horizontalMoment_eq, Fin.sum_univ_succ,
    Pi.zero_apply, Pi.zero_def, add_assoc] using
    directionalAffine_moment r k (δ 0) (fun i => δ i.succ) (fun i => u i.succ) t (u 0) z

theorem det_vectorAffineMatrix (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    (vectorAffineMatrix r k δ t).det = 1 := det_directionalAffineMatrix r k _ _ t

/-- Relabeling horizontal coefficients is simultaneous row and column permutation of the moment matrix. -/
theorem vectorAffineMatrix_permutation (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (σ : Equiv.Perm (Fin (r + 1))) :
    vectorAffineMatrix r k (fun i => δ (σ.symm i)) t =
      (vectorAffineMatrix r k δ t).submatrix
        (horizontalIndexPermutation r k σ) (horizontalIndexPermutation r k σ) := by
  have hm (u : Fin (r + 1) → ℝ) (z : ℝ) :
      (vectorAffineMatrix r k δ t).submatrix
          (horizontalIndexPermutation r k σ) (horizontalIndexPermutation r k σ) *ᵥ horizontalMoment r k u z =
        vectorAffineMatrix r k (fun i => δ (σ.symm i)) t *ᵥ horizontalMoment r k u z := by
    have hu : coordinatePermutation (horizontalIndexPermutation r k σ)
        (horizontalMoment r k (fun i => u (σ i)) z) = horizontalMoment r k u z := by
      rw [coordinatePermutation_horizontalMoment]
      simp only [σ.apply_symm_apply]
    have hs : (∑ i, δ i * u (σ i)) = ∑ i, δ (σ.symm i) * u i := by
      simpa only [σ.apply_symm_apply] using
        (Equiv.sum_comp σ.symm (fun i => δ i * u (σ i))).symm
    calc
      _ = (vectorAffineMatrix r k δ t).submatrix
          (horizontalIndexPermutation r k σ) (horizontalIndexPermutation r k σ) *ᵥ
          coordinatePermutation (horizontalIndexPermutation r k σ)
            (horizontalMoment r k (fun i => u (σ i)) z) := by rw [hu]
      _ = coordinatePermutation (horizontalIndexPermutation r k σ)
          (vectorAffineMatrix r k δ t *ᵥ horizontalMoment r k (fun i => u (σ i)) z) :=
        submatrix_mulVec_coordinatePermutation _ _ _
      _ = coordinatePermutation (horizontalIndexPermutation r k σ)
          (horizontalMoment r k (fun i => u (σ i)) (z + ∑ i, δ i * u (σ i) + t) -
            horizontalMoment r k 0 t) := by rw [vectorAffineMatrix_moment]
      _ = horizontalMoment r k u (z + ∑ i, δ i * u (σ i) + t) - horizontalMoment r k 0 t := by
        rw [coordinatePermutation_sub, coordinatePermutation_horizontalMoment,
          coordinatePermutation_horizontalMoment]
        simp only [σ.apply_symm_apply, Pi.zero_apply, Pi.zero_def]
      _ = _ := by rw [vectorAffineMatrix_moment, hs]
  apply matrix_eq_of_affineAxisMoment_eq
  intro y x z
  simpa only [horizontalMoment_eq, Fin.cons_zero, Fin.cons_succ] using (hm (Fin.cons x y) z).symm

/-- Coordinate-cube overlap for the complete horizontal direction vector. -/
def vectorAffineOverlap (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (a b : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  matrixUnitOverlap (vectorAffineMatrix r k δ t) a b

/-- Horizontal relabeling preserves overlap volume when both cube centers are relabeled as well. -/
theorem volume_vectorAffineOverlap_permutation (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (σ : Equiv.Perm (Fin (r + 1))) (a b : AffineAxisSpace r k) :
    volume (vectorAffineOverlap r k (fun i => δ (σ.symm i)) t
      (coordinatePermutation (horizontalIndexPermutation r k σ) a)
      (coordinatePermutation (horizontalIndexPermutation r k σ) b)) =
        volume (vectorAffineOverlap r k δ t a b) := by
  unfold vectorAffineOverlap
  rw [vectorAffineMatrix_permutation r k δ t σ, volume_matrixUnitOverlap_submatrix]

#print axioms coordinatePermutation_horizontalMoment
#print axioms vectorAffineMatrix_moment
#print axioms det_vectorAffineMatrix
#print axioms vectorAffineMatrix_permutation
#print axioms volume_vectorAffineOverlap_permutation

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
