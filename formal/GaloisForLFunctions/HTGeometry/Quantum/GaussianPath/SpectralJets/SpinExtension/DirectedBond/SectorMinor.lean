import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Independent response matrices on complementary spin sectors -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- Even and odd bond readings may have different old response matrices.
Subtracting the first block-column from the second separates their determinants. -/
theorem sector_minor (A B : Matrix I I R) :
    (fromBlocks A A B (-B)).det = (-2:R)^(Fintype.card I)*A.det*B.det := by
  let T := fromBlocks (1 : Matrix I I R) (-1 : Matrix I I R) (0 : Matrix I I R) (1 : Matrix I I R)
  have hT : T.det=1 := by simp [T,det_fromBlocks_zero₂₁]
  have hmul : fromBlocks A A B (-B)*T = fromBlocks A 0 B ((-2:R) • B) := by
    rw [show fromBlocks A A B (-B)*T = _ from fromBlocks_multiply ..]
    simp only [mul_one,mul_neg,mul_zero,add_zero,neg_add_cancel,neg_smul,two_smul,neg_add_rev]
  rw [←mul_one (fromBlocks A A B (-B)).det,←hT,←det_mul,hmul,det_fromBlocks_zero₁₂,det_smul]
  ring

#print axioms sector_minor
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
