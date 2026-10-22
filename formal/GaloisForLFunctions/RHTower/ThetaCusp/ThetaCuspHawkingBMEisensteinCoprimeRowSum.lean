import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularForcing
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-! The literal completed Eisenstein field is the normalized sum over the actual coprime-row matrices. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

def primitiveRowEquiv : D4BMPrimitiveIntegerPair ≃ gammaSet 1 1 0 where
  toFun p := ⟨![p.pair.1,p.pair.2],(gammaSet_one_mem_iff 1 _).mpr p.primitive⟩
  invFun v := ⟨(v.1 0,v.1 1),(gammaSet_one_mem_iff 1 _).mp v.2⟩
  left_inv p := by cases p with | mk p hp => cases p; rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

/-- The original primitive seed is exactly the transformed height power, without a scale change. -/
theorem poincareSeed_eq_row_height (z : UpperHalfPlane) (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed ⟨z.re,z.im,z.im_pos⟩ s p =
      ((gammaSetMatrix (primitiveRowEquiv p) • z).im:ℂ)^s := by
  rw [ModularGroup.im_smul_eq_div_normSq,denom_apply,
    gammaSetMatrix_apply_one_zero,gammaSetMatrix_apply_one_one]
  unfold d4BMPoincareSeed
  congr 2
  dsimp [d4BMPoincareQuadratic,primitiveRowEquiv]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.mul_re,Complex.intCast_re,
    Complex.intCast_im,Complex.add_im,Complex.mul_im,zero_mul,sub_zero,add_zero,
    UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

/-- Exact factor-one-half coprime-row realization of the full scalar cusp field. -/
theorem scalar_eq_coprime_row_sum (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) :
    D4BMGlobalAngularResponse.scalar (P.s-1/2) (coordinates z) =
      reflectedCompletedLambda (2*P.s)*(1/2:ℂ)*
        ∑' v : gammaSet 1 1 0, ((gammaSetMatrix v • z).im:ℂ)^P.s := by
  have he := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg ⟨z.re,z.im,z.im_pos⟩ P z.re
  change d4BMCompletedEisensteinPoincareSeries ⟨z.re,z.im,z.im_pos⟩ P =
    D4BMGlobalAngularResponse.scalar (P.s-1/2) (coordinates z) at he
  rw [← he,d4BMCompletedEisensteinPoincareSeries,d4BMRawEisensteinPoincareSeries]
  rw [← primitiveRowEquiv.tsum_eq (fun v => ((gammaSetMatrix v • z).im:ℂ)^P.s)]
  simp_rw [← poincareSeed_eq_row_height]
  ring

end
end RHTower.D4BMJointSource
