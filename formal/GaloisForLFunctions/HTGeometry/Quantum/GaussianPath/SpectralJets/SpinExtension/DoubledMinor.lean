import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Doubling independent spectral responses by both signs of an added spin -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- Each old row occurs with equal and opposite weights on the two new sectors. -/
theorem doubled_response_det (A : Matrix I I R) :
    (fromBlocks A A A (-A)).det = (-2:R)^(Fintype.card I)*A.det^2 := by
  let T := fromBlocks (1 : Matrix I I R) (-1 : Matrix I I R) (0 : Matrix I I R) (1 : Matrix I I R)
  have hT : T.det=1 := by simp [T,det_fromBlocks_zero₂₁]
  have hmul : fromBlocks A A A (-A)*T = fromBlocks A 0 A ((-2:R) • A) := by
    rw [show fromBlocks A A A (-A)*T = _ from fromBlocks_multiply ..]
    simp only [mul_one,mul_neg,mul_zero,add_zero,neg_add_cancel,neg_smul,two_smul,neg_add_rev]
  rw [←mul_one (fromBlocks A A A (-A)).det,←hT,←det_mul,hmul,det_fromBlocks_zero₁₂,det_smul]
  ring

end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
