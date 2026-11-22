import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # First variation of the spectral determinant across a large spin splitting -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
private abbrev M (I R : Type*) := Matrix I I R

/-- After subtracting a spin eigenvalue and multiplying the opposite-sector rows by
the inverse splitting u, the characteristic matrix has a regular limit at u=0. -/
def splitDet (A W V : M I R) (b u : R) : R :=
  (fromBlocks A (-W) (-(u • V)) (b • (1 : M I R) + u • A)).det

/-- A triangular column operation leaves the determinant unchanged and pushes
the lower-left block to second order in u. -/
theorem splitDet_normal_form (A W V : M I R) (b c u : R) (h : b*c=1) :
    splitDet A W V b u =
      (fromBlocks (A-(c*u) • (W*V)) (-W) ((c*u^2) • (A*V)) (b • 1 + u • A)).det := by
  let B := b • (1 : M I R) + u • A
  let F := fromBlocks A (-W) (-(u • V)) B
  let T := fromBlocks (1 : M I R) (0 : M I R) ((c*u) • V) (1 : M I R)
  have hT : T.det = 1 := by simp [T,det_fromBlocks_zero₁₂]
  have hB : B*((c*u) • V) = u • V + (c*u^2) • (A*V) := by
    simp only [B,add_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,one_mul]
    rw [show c*u*b=b*c*u by ring,h,one_mul,show c*u*u=c*u^2 by ring]
  have hF : F*T = fromBlocks (A-(c*u) • (W*V)) (-W) ((c*u^2) • (A*V)) B := by
    rw [show F*T = _ from fromBlocks_multiply ..]
    simp only [mul_one,mul_zero,zero_add,neg_mul,Matrix.mul_smul,hB,neg_add_cancel_left,sub_eq_add_neg]
  change F.det = _
  rw [←mul_one F.det,←hT,←Matrix.det_mul,hF]

/-- Over first-order scalar jets only the product WV contributes to the effective
sector Hamiltonian. This retains the order of the two transverse operators. -/
theorem splitDet_square_zero (A W V : M I R) (b c u : R) (h : b*c=1) (hu : u^2=0) :
    splitDet A W V b u = (A-(c*u) • (W*V)).det * (b • 1+u • A).det := by
  rw [splitDet_normal_form A W V b c u h,hu,mul_zero,zero_smul,det_fromBlocks_zero₂₁]

#print axioms splitDet_square_zero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
