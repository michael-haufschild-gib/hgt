import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineAxisFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisExponent
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineBinaryOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockSelection
import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedMatrixPolynomialDecay

/-!
# Translation-uniform sharp-power bounds for coordinate-direction frames

Select the balanced minor in every binary chain and then assemble the
selections by homogeneous degree. Translation contributes only below the
degree diagonal. The resulting determinant has exactly the full proposed
power, independently of vertical shift and of both coordinate-cube centers.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Balanced selections in all chains give the complete exponent, uniformly in vertical translation. -/
theorem exists_affineAxis_determinant_certificate (r k : ℕ) :
    ∃ s : AffineAxisIndex r k → AffineAxisIndex r k ⊕ AffineAxisIndex r k,
      ∃ c : ℝ, c ≠ 0 ∧ ∀ θ t : ℝ,
        (selectedMatrix (affineAxisMatrix r k θ t) s).det = c * θ ^ axisExponent r k := by
  classical
  have hs (d : Fin k) (a : HomogeneousChain r (d.val + 1)) :=
    exists_shear_determinant_certificate (chainDegree a + 1)
  choose s c hc hd using hs
  refine ⟨blockSelector (fun d => blockSelector (s d)), ∏ d, ∏ a, c d a, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro d _
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => hc d a)
  · intro θ t
    rw [det_selectedMatrix_of_lower _ (affineAxisMatrix_lower r k θ t)]
    simp only [affineAxisMatrix_diagonalBlock, homogeneousAxisShearMatrix,
      det_selectedMatrix_blockDiagonal, hd, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    change (∑ d : Fin k, homogeneousAxisExponent r (d.val + 1)) = axisExponent r k
    exact Fin.sum_univ_eq_sum_range (fun d : ℕ => homogeneousAxisExponent r (d + 1)) k

/-- Overlap of independently centered cubes for the genuine affine moment matrix. -/
def affineAxisOverlap (r k : ℕ) (θ t : ℝ) (a b : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  matrixUnitOverlap (affineAxisMatrix r k θ t) a b

/-- The proposed power bounds real overlap volume uniformly over shift and centers. -/
theorem exists_regularized_affineAxis_volume_upper (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ t : ℝ) (a b : AffineAxisSpace r k),
      (1 + |θ|) ^ axisExponent r k * (volume (affineAxisOverlap r k θ t a b)).toReal ≤ C := by
  obtain ⟨s, c, hc, hd⟩ := exists_affineAxis_determinant_certificate r k
  exact exists_regularized_matrixUnitOverlap_bound (affineAxisMatrix r k) (axisExponent r k) s c hc hd

/-- Every coordinate-direction affine moment frame has the proposed dimension-degree decay power. -/
theorem exists_uniform_affineAxis_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ t : ℝ) (a b : AffineAxisSpace r k),
      volume (affineAxisOverlap r k θ t a b) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  obtain ⟨s, c, hc, hd⟩ := exists_affineAxis_determinant_certificate r k
  exact exists_matrixUnitOverlap_decay (affineAxisMatrix r k) (axisExponent r k) s c hc hd

/-- Actual affine image intersections have the same volume as the corresponding inverse-image overlap. -/
theorem volume_cube_inter_affineAxis_image (r k : ℕ) (θ t : ℝ) (a b : AffineAxisSpace r k) :
    volume (centeredCube a 1 ∩ (Matrix.toLin' (affineAxisMatrix r k θ t)) '' centeredCube b 1) =
      volume (affineAxisOverlap r k θ t b a) := by
  simpa only [affineAxisOverlap, det_affineAxisMatrix, abs_one, ENNReal.ofReal_one, one_mul] using
    volume_cube_inter_matrix_image (affineAxisMatrix r k θ t) a b

/-- The same bound holds for intersections with actual affine images of coordinate cubes. -/
theorem exists_uniform_affineAxis_image_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ t : ℝ) (a b : AffineAxisSpace r k),
      volume (centeredCube a 1 ∩ (Matrix.toLin' (affineAxisMatrix r k θ t)) '' centeredCube b 1) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_affineAxis_overlap_decay r k
  refine ⟨C, hC, fun θ t a b => ?_⟩
  rw [volume_cube_inter_affineAxis_image]
  exact h θ t b a

#print axioms exists_affineAxis_determinant_certificate
#print axioms exists_regularized_affineAxis_volume_upper
#print axioms exists_uniform_affineAxis_overlap_decay
#print axioms volume_cube_inter_affineAxis_image
#print axioms exists_uniform_affineAxis_image_overlap_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
