import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-! Explicit determinant-one eigenframes for real two-by-two matrices with
reciprocal distinct eigenvalues. -/

open Matrix
open scoped MatrixGroups
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRealEigenbasis

def diagonalElement (l μ : ℝ) (hp : l*μ=1) : SL(2, ℝ) :=
  ⟨!![l,0;0,μ], by
    rw [Matrix.det_fin_two]
    change l*μ-0*0=1
    simpa only [zero_mul,sub_zero] using hp⟩

/-- Two explicit real eigenvectors, scaled to a determinant-one basis. -/
theorem exists_eigenbasis (A : SL(2, ℝ)) (l μ : ℝ)
    (hp : l*μ=1) (ht : l+μ=A 0 0+A 1 1)
    (hc : A 1 0 ≠ 0) (hg : l-μ ≠ 0) :
    ∃ C : SL(2, ℝ), A*C=C*diagonalElement l μ hp := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hl : l^2-(A 0 0+A 1 1)*l+1=0 := by
    rw [← ht]
    nlinarith only [hp]
  have hμ : μ^2-(A 0 0+A 1 1)*μ+1=0 := by
    rw [← ht]
    nlinarith only [hp]
  let V : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(l-A 1 1)/A 1 0,(μ-A 1 1)/(l-μ);1,A 1 0/(l-μ)]
  have hV : V.det=1 := by
    rw [Matrix.det_fin_two]
    change ((l-A 1 1)/A 1 0)*(A 1 0/(l-μ))-(μ-A 1 1)/(l-μ)*1=1
    field_simp [hc,hg]
    ring
  refine ⟨⟨V,hV⟩,?_⟩
  apply Subtype.ext
  change (A : Matrix (Fin 2) (Fin 2) ℝ)*V=V*!![l,0;0,μ]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change A 0 0*((l-A 1 1)/A 1 0)+A 0 1*1 =
      ((l-A 1 1)/A 1 0)*l+((μ-A 1 1)/(l-μ))*0
    simp only [mul_one,mul_zero,add_zero]
    field_simp [hc]
    nlinarith only [hl,hdet]
  · simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change A 0 0*((μ-A 1 1)/(l-μ))+A 0 1*(A 1 0/(l-μ)) =
      ((l-A 1 1)/A 1 0)*0+((μ-A 1 1)/(l-μ))*μ
    simp only [mul_zero,zero_add]
    field_simp [hg]
    nlinarith only [hμ,hdet]
  · simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change A 1 0*((l-A 1 1)/A 1 0)+A 1 1*1 =
      1*l+(A 1 0/(l-μ))*0
    simp only [mul_one,one_mul,mul_zero,add_zero]
    field_simp [hc]
    ring
  · simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change A 1 0*((μ-A 1 1)/(l-μ))+A 1 1*(A 1 0/(l-μ)) =
      1*0+(A 1 0/(l-μ))*μ
    simp only [mul_zero,zero_add]
    field_simp [hg]
    ring

#print axioms exists_eigenbasis

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRealEigenbasis
