import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! # A strict affine improvement at every positive unitary error below two -/

open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The skew part of the relative unitary gives an affine displacement
whose residual has norm at most half the squared original error. -/
theorem relative_affine_correction (U Q : unitary (Mat I)) :
    ∃ B : selfAdjoint (Mat I),
      ‖U.val-Q.val-(Complex.I • B.val)*Q.val‖≤‖U.val-Q.val‖^2/2 := by
  let Y := U.val*star Q.val
  let B : Mat I := (-Complex.I/2) • (Y-star Y)
  have hB : IsSelfAdjoint B := by
    change star ((-Complex.I/2) • (Y-star Y))=_
    rw [star_smul,star_sub,star_star,←neg_sub Y (star Y),smul_neg,←neg_smul]
    congr 1
    simp [neg_div]
  refine ⟨⟨B,hB⟩,?_⟩
  have hu := Unitary.mem_iff.mp U.2
  have hq := Unitary.mem_iff.mp Q.2
  let X := U.val-Q.val
  have hG : Complex.I • B=(1/2:ℂ) • (Y-star Y) := by
    dsimp only [B]
    rw [smul_smul]
    congr 1
    linear_combination -Complex.I_sq/2
  have h₁ : Y*Q.val=U.val := by dsimp only [Y]; rw [mul_assoc,hq.1,mul_one]
  have h₂ : X*star X*Q.val=Q.val-U.val-(Q.val*star U.val*Q.val-Q.val) := by
    dsimp only [X]
    rw [star_sub]
    calc
      _ = U.val*star U.val*Q.val-U.val*(star Q.val*Q.val)-
          (Q.val*star U.val*Q.val-Q.val*(star Q.val*Q.val)) := by noncomm_ring
      _ = _ := by rw [hu.2,hq.1,one_mul,mul_one,mul_one]
  have hres : U.val-Q.val-(Complex.I • B)*Q.val=(-1/2:ℂ) • (X*star X*Q.val) := by
    rw [hG,Matrix.smul_mul,sub_mul,h₁,h₂]
    dsimp only [Y]
    rw [star_mul,star_star]
    module
  change ‖U.val-Q.val-(Complex.I • B)*Q.val‖≤_
  rw [hres,norm_smul,CStarRing.norm_mul_mem_unitary _ Q.2]
  have hnorm : ‖(-1/2:ℂ)‖=(1/2:ℝ) := by norm_num [norm_div]
  rw [hnorm]
  calc
    _ ≤ (1/2:ℝ)*(‖X‖*‖star X‖) := mul_le_mul_of_nonneg_left (norm_mul_le ..) (by norm_num)
    _ = _ := by rw [norm_star]; change 1/2*(‖X‖*‖X‖)=‖X‖^2/2; ring

#print axioms relative_affine_correction
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
