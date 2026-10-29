import GaloisForLFunctions.HTGeometry.LoopEisenstein.SimpleRankOneEmbeddings
import GaloisForLFunctions.RHTower.RealPrincipalSeriesKTypes

/-!
# Triangular rigidity of real rotations

The stabilizer of the upper-half-plane point `i` has rotation matrix form.
Its triangular matrices are exactly the two scalar signs; the negative
sign is realized by the actual unit-circle rotation map.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

open GaloisForLFunctions.RHTower

noncomputable section

/-- An upper triangular real rotation is one of the two scalar signs. -/
theorem rotation_upperTriangular_eq_sign (g : SL2 ℝ)
    (hg : g ∈ upperHalfPlaneStabilizer) (hc : g 1 0 = 0) :
    g = 1 ∨ g = sl2Diagonal (-1 : ℝˣ) := by
  let k : upperHalfPlaneStabilizer := ⟨g, hg⟩
  have hr := upperHalfPlaneStabilizer_matrix_relations k
  change g 1 0 = -g 0 1 ∧ g 1 1 = g 0 0 at hr
  have hb : g 0 1 = 0 := by linarith only [hr.1, hc]
  have hs := realSphericalM_diagonal_square (⟨k, hc⟩ : realSphericalM)
  change g 0 0 ^ 2 = 1 at hs
  have hf : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hf with ha | ha
  · left
    have ha' : g 0 0 = 1 := by linarith only [ha]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hr.2, ha', hb, hc]
  · right
    have ha' : g 0 0 = -1 := by linarith only [ha]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2Diagonal, hr.2, ha', hb, hc]

/-- The negative scalar matrix is an actual rotation. -/
theorem sl2Diagonal_neg_one_mem_rotation :
    sl2Diagonal (-1 : ℝˣ) ∈ upperHalfPlaneStabilizer := by
  have he : sl2Diagonal (-1 : ℝˣ) =
      (realCircleToSphericalK (-1) : SL2R) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Diagonal, realCircleToSphericalK, realCircleRotation]
  rw [he]
  exact (realCircleToSphericalK (-1)).property

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
